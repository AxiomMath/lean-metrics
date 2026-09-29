/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic
public import LeanMetrics.Authored
import LeanMetrics.Stats
import LeanMetrics.Syntax
import Lean.Elab.DeclarationRange
import Lean.Meta.Instances
import Lean.ProjFns
import Lean.Util.Recognizers

/-! # The declaration dependency graph

Edges from a declaration to those its type or body mentions.
Generated constants are not nodes; see `LeanMetrics.Authored`.
-/

public section

open Lean Meta

namespace LeanMetrics

/-- `irreducible_def foo` hides `foo`'s body behind an opaque wrapper and states it in a theorem
`foo_def : foo = body`. The constants of that body, when `foo` has such a theorem. -/
private def irreducibleDefBody (env : Environment) (n : Name) : Array Name :=
  match n with
  | .str p s =>
    match env.find? (.str p (s ++ "_def")) with
    | some (.thmInfo t) =>
      match t.type.eq? with
      | some (_, lhs, rhs) =>
        if lhs.getAppFn.constName? == some n then rhs.getUsedConstants else #[]
      | none => #[]
    | _ => #[]
  | _ => #[]

/-- Memo tables shared by the dependency computations of all declarations: whether a constant
is a declaration of its own, and which declarations a generated constant stands for. -/
private structure GraphCache where
  authored : Std.HashMap Name Bool := {}
  expansion : Std.HashMap Name NameSet := {}

private abbrev GraphM := StateM GraphCache

/-- Whether a constant is an authored declaration. One outside the project in `tacticNamespaces`
is not. -/
private def isAuthoredCached (ctx : Context) (c : Name) : GraphM Bool := do
  if let some b := (← get).authored[c]? then return b
  let b := isAuthored ctx.env c && (ctx.isOwn c || !isTacticInternal c)
  modify fun s => { s with authored := s.authored.insert c b }
  return b

/-- Whether a constant a body uses is a node of the graph: an authored declaration with a body
of its own (inductive types, opaque constants and quotients have none). -/
private def isBodyNode (ctx : Context) (c : Name) : GraphM Bool :=
  return (← isAuthoredCached ctx c) &&
    !(ctx.env.find? c matches some (.inductInfo _) | some (.opaqueInfo _) | some (.quotInfo _))

/-- Declarations a generated constant stands for: its owner, and what its body uses.
Parent projections, instances and `tacticNamespaces` are not expanded. On a cycle, a constant
still being expanded contributes the set stored so far. -/
private partial def expansion (ctx : Context) (c : Name) : GraphM NameSet := do
  if let some r := (← get).expansion[c]? then return r
  modify fun s => { s with expansion := s.expansion.insert c {} }
  let env := ctx.env
  let mut out : NameSet := {}
  let o := owner env c
  if o != c && (← isBodyNode ctx o) then out := out.insert o
  if !env.isProjectionFn c && !isParentProjection env c && !isInstanceCore env c &&
      !isTacticInternal c then
    let used := match env.find? c with
      | some (.thmInfo v) => v.value.getUsedConstants
      | some (.defnInfo v) => v.value.getUsedConstants
      | _ => #[]
    for u in used do
      if ← isBodyNode ctx u then out := out.insert u
      else out := (← expansion ctx u).foldl (·.insert ·) out
  modify fun s => { s with expansion := s.expansion.insert c out }
  return out

/-- The declarations a declaration's body uses, seen through generated auxiliaries. -/
private def bodyDeps (ctx : Context) (n : Name) (ci : ConstantInfo) : GraphM NameSet := do
  let direct := match ci with
    | .thmInfo v => v.value.getUsedConstants
    | .defnInfo v => v.value.getUsedConstants ++ irreducibleDefBody ctx.env n
    | _ => #[]
  let mut out : NameSet := {}
  for c in direct do
    if ← isBodyNode ctx c then out := out.insert c
    else out := (← expansion ctx c).foldl (·.insert ·) out
  return out

/-- The declarations a declaration's type mentions, each generated constant replaced by its
owner. -/
private def typeDeps (ctx : Context) (ci : ConstantInfo) : GraphM NameSet := do
  let mut out : NameSet := {}
  for c in ci.type.getUsedConstants do
    if ← isAuthoredCached ctx c then out := out.insert c
    else
      let o := owner ctx.env c
      if o != c && ctx.env.contains o && (← isAuthoredCached ctx o) then out := out.insert o
  return out

/-- A declaration's name as written: a private name without the mangling Lean adds. -/
private def displayName (n : Name) : String := toString ((privateToUserName? n).getD n)

private def isCoreModule (m : Name) : Bool :=
  let r := m.getRoot
  r == `Init || r == `Std || r == `Lean

/-- The dependency graph of the project's declarations: internal nodes, edges `(dep, user)`
from internal or foreign non-core declarations to internal ones, and the declarations whose own
body names themselves (direct recursion that survives compilation, as in `unsafe` definitions). -/
private structure DepGraph where
  internal : Array Name
  edges : Array (Name × Name)
  selfLoops : NameSet

private def depGraphOf (ctx : Context) : DepGraph := Id.run do
  let env := ctx.env
  let mut cache : GraphCache := {}
  let mut edges : Array (Name × Name) := #[]
  let mut selfLoops : NameSet := {}
  for user in ctx.authored do
    let some ci := env.find? user | continue
    let (tys, c) := (typeDeps ctx ci).run cache
    let (bodies, c) := (if ci matches .inductInfo _ | .opaqueInfo _ | .quotInfo _ then pure {}
      else bodyDeps ctx user ci).run c
    cache := c
    -- only a direct mention in the body; one found through a generated auxiliary does not count
    if (ci.value? (allowOpaque := true)).any (·.getUsedConstants.contains user) then
      selfLoops := selfLoops.insert user
    for d in bodies.foldl (·.insert ·) tys do
      if d == user then continue
      if ctx.isOwn d || (ctx.moduleOf? d).any (!isCoreModule ·) then edges := edges.push (d, user)
  return { internal := ctx.authored, edges, selfLoops }

/-- Strongly connected components of a graph on `0..n`, each listed after every component it
depends on (Tarjan's algorithm, iteratively). -/
private def sccs (n : Nat) (deps : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let none' := n
  let mut index := Array.replicate n none'
  let mut low := Array.replicate n 0
  let mut onStack := Array.replicate n false
  let mut stack : Array Nat := #[]
  let mut comps : Array (Array Nat) := #[]
  let mut counter := 0
  for root in [0:n] do
    if index[root]! != none' then continue
    index := index.set! root counter; low := low.set! root counter; counter := counter + 1
    stack := stack.push root; onStack := onStack.set! root true
    let mut work : Array (Nat × Nat) := #[(root, 0)]
    while h : work.size > 0 do
      let (v, i) := work[work.size - 1]
      if i < deps[v]!.size then
        work := work.set! (work.size - 1) (v, i + 1)
        let w := deps[v]![i]!
        if index[w]! == none' then
          index := index.set! w counter; low := low.set! w counter; counter := counter + 1
          stack := stack.push w; onStack := onStack.set! w true
          work := work.push (w, 0)
        else if onStack[w]! then
          low := low.set! v (min low[v]! index[w]!)
      else
        work := work.pop
        if h : work.size > 0 then
          let u := work[work.size - 1].1
          low := low.set! u (min low[u]! low[v]!)
        if low[v]! == index[v]! then
          let mut comp := #[]
          repeat
            let w := stack.back!
            stack := stack.pop; onStack := onStack.set! w false
            comp := comp.push w
            if w == v then break
          comps := comps.push comp
  return comps

/-- `log10` of a natural number that may exceed a `Float`'s range. -/
private def log10Nat (x : Nat) : Float :=
  let shift := x.log2 - min x.log2 52
  (x >>> shift).toFloat.log10 + shift.toFloat * Float.log10 2

/-- Local instance registrations disappear on import. Recover their declaration identities
from source selection ranges, including anonymous and private instances. -/
private def sourceInstances (ctx : Context) : NameSet := Id.run do
  let mut positions : Std.HashSet (Name × Nat × Nat) := {}
  for file in ctx.files do
    for cmd in file.commands do
      for decl in declarationsOf cmd do
        if decl.isOfKind ``Parser.Command.instance then
          if let some pos := (Elab.getDeclarationSelectionRef decl).getPos? then
            let p := file.fileMap.toPosition pos
            positions := positions.insert (file.module, p.line, p.column)
  let mut names : NameSet := {}
  for n in ctx.authored do
    if let some mod := ctx.moduleOf? n then
      if let some ranges := declRangeExt.find? ctx.env n then
        let p := ranges.selectionRange.pos
        if positions.contains (mod, p.line, p.column) then names := names.insert n
  return names

/-- Metric `dep_graph`: Shape of the declaration dependency graph: degrees, roots and leaves,
longest chain, and sharing of sub-results. -/
def depGraph : Metric where
  name := "dep_graph"
  description := "shape of the declaration dependency graph: degrees, roots and leaves, longest \
    chain, and sharing of sub-results"
  needsSource := true
  run ctx := do
    let g := depGraphOf ctx
    let idx : Std.HashMap Name Nat := g.internal.foldl (fun m n => m.insert n m.size) {}
    let n := g.internal.size
    let mut deps : Array (Array Nat) := Array.replicate n #[]
    let mut ext : Array NameSet := Array.replicate n {}
    for (d, u) in g.edges do
      let some ui := idx[u]? | continue
      match idx[d]? with
      | some di => deps := deps.modify ui (·.push di)
      | none => ext := ext.modify ui (·.insert d)
    let mut inDeg := Array.replicate n 0
    for ds in deps do for d in ds do inDeg := inDeg.modify d (· + 1)
    -- longest chain and unrolled-tree size per node, over the components in dependency order
    let comps := sccs n deps
    let mut compOf := Array.replicate n 0
    for h : c in [0:comps.size] do for v in comps[c] do compOf := compOf.set! v c
    let mut depth := Array.replicate n 0
    let mut cost := Array.replicate n 0
    for h : c in [0:comps.size] do
      let comp := comps[c]
      let depComps : Std.HashSet Nat := comp.foldl (fun s v =>
        deps[v]!.foldl (fun s d => if compOf[d]! == c then s else s.insert compOf[d]!) s) {}
      let rep (k : Nat) := comps[k]![0]!
      -- a cycle counts as one step of the chain
      let cyclic := comp.size > 1 || g.selfLoops.contains g.internal[comp[0]!]!
      let dd := depComps.fold (fun m k => max m (depth[rep k]! + 1)) 0 + (if cyclic then 1 else 0)
      let cc := depComps.fold (fun s k => s + cost[rep k]!) comp.size
      for v in comp do depth := depth.set! v dd; cost := cost.set! v cc
    -- the main result: the largest of those given, else of the declarations nothing depends on
    let sinks := (List.range n).filter (inDeg[·]! == 0)
    let candidates ← if ctx.mainDecls.isEmpty then pure sinks else
      ctx.mainDecls.toList.mapM fun m => do
        let some i := idx[m]?
          | throwError "`{m}` is not in the dependency graph"
        pure i
    let root? := candidates.foldl (fun best v => match best with
      | some b => if cost[v]! > cost[b]! then some v else best
      | none => some v) none
    let reachable := match root? with
      | none => 0
      | some r => Id.run do
        let mut seen : Std.HashSet Nat := {r}
        let mut stack := #[r]
        while h : stack.size > 0 do
          let v := stack[stack.size - 1]
          stack := stack.pop
          for d in deps[v]! do
            unless seen.contains d do seen := seen.insert d; stack := stack.push d
        return seen.size
    let outDeg := deps.map (·.size)
    let extAll : NameSet := ext.foldl (fun s e => e.foldl (·.insert ·) s) {}
    let rootCost := root?.map (cost[·]!) |>.getD 0
    -- instances first: Prop-valued ones are theorems, and every instance is also a definition
    let declaredInstances := sourceInstances ctx
    let kinds := g.internal.map fun c =>
      if declaredInstances.contains c || isInstanceCore ctx.env c then "instance"
      else match ctx.env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) | some (.opaqueInfo _) | some (.inductInfo _) => "def"
        | _ => "other"
    let kind (i : Nat) := kinds[i]!
    let usedByTheorem : Std.HashSet Nat := (List.range n).foldl (fun s u =>
      if kind u == "theorem" then deps[u]!.foldl (·.insert ·) s else s) {}
    let count (p : Nat → Bool) := toJson ((List.range n).filter p).length
    let columns := #[
      ("n_graph_decls", toJson n), ("n_edges", toJson (outDeg.foldl (· + ·) 0)),
      ("out_deg_mean", mean outDeg 2), ("out_deg_median", median outDeg),
      ("out_deg_max", toJson (maximum outDeg)),
      ("in_deg_mean", mean inDeg 2), ("in_deg_median", median inDeg),
      ("in_deg_max", toJson (maximum inDeg)),
      ("n_roots", toJson sinks.length), ("n_leaves", count (deps[·]!.isEmpty)),
      ("ext_deps_per_decl_mean", mean (ext.map (·.size)) 2), ("n_ext_consts", toJson extAll.size),
      ("longest_pole", toJson (maximum depth)),
      ("root", toJson ((root?.map (displayName g.internal[·]!)).getD "")),
      ("root_id", toJson ((root?.map (toString g.internal[·]!)).getD "")),
      ("cost_root_log10", if rootCost == 0 then .null else decimal (log10Nat rootCost)),
      ("reachable_from_root", toJson reachable),
      ("compression_log10", if rootCost == 0 || reachable == 0 then .null
        else decimal (log10Nat rootCost - reachable.toFloat.log10)),
      ("cost_max_log10", if n == 0 then .null else decimal (log10Nat (maximum cost))),
      ("has_cycle", toJson (comps.any (·.size > 1) || !g.selfLoops.isEmpty)),
      ("n_internal_theorems", count (kind · == "theorem")),
      ("n_internal_defs", count (kind · == "def")),
      ("n_internal_instances", count (kind · == "instance")),
      ("n_instances_unused", count fun i => kind i == "instance" && inDeg[i]! == 0),
      ("n_theorems_unused", count fun i => kind i == "theorem" && inDeg[i]! == 0),
      ("n_theorems_single_use", count fun i => kind i == "theorem" && inDeg[i]! == 1),
      ("n_defs_unused", count fun i => kind i == "def" && inDeg[i]! == 0),
      ("n_defs_no_theorem_user", count fun i => kind i == "def" && !usedByTheorem.contains i)]
    -- Private declarations can have the same user name in different modules. Preserve Lean's
    -- unique names as IDs and keep their readable names separately, including isolated nodes.
    let nodeNames := g.internal.foldl (·.insert ·) extAll
    let nodes := nodeNames.foldl (init := #[]) fun acc name => acc.push <| Json.mkObj [
      ("id", toJson name.toString), ("name", toJson (displayName name)),
      ("module", toJson ((ctx.moduleOf? name).map toString |>.getD "")),
      ("internal", toJson (idx.contains name))]
    let edges := g.edges.map fun (d, u) => Json.arr #[toJson d.toString, toJson u.toString]
    return { columns, details := Json.mkObj [("nodes", Json.arr nodes), ("edges", Json.arr edges)] }

end LeanMetrics
