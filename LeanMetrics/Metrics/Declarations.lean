/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic
import LeanMetrics.Stats
import LeanMetrics.Syntax

/-! # Declarations

Declarations as written: kind, binders, proof mode, reducibility and recursion annotations,
including `mutual` blocks and `… in` wrappers.
Generated auxiliaries of `notation`, `macro` and `syntax` are not included.
-/

public section

open Lean Parser

namespace LeanMetrics

/-- The kind of a declaration node, as its keyword names it. -/
private def declarationKind? (decl : Syntax) : Option String :=
  let k := decl.getKind
  if isTheorem decl then some "theorem"
  else if k == ``Command.definition then some "def"
  else if k == ``Command.abbrev then some "abbrev"
  else if k == ``Command.example then some "example"
  else if k == ``Command.opaque then some "opaque"
  else if k == ``Command.axiom then some "axiom"
  else if k == ``Command.instance then some "instance"
  else if k == ``Command.classInductive then some "class"
  else if k == ``Command.inductive || k == ``Command.coinductive then some "inductive"
  else if k == ``Command.structure then
    if decl[0].isOfKind ``Command.classTk then some "class" else some "structure"
  else none

/-- The binder groups written in a declaration's signature: in its header and in its type
(`∀ (x : α), …`). -/
private def signatureBinders (decl : Syntax) : Array Syntax :=
  match signatureOf? decl with
  | some sig => foldNodes (init := #[]) (s := sig) fun acc b =>
      if binderKinds.contains b.getKind then acc.push b else acc
  | none => #[]
where
  binderKinds : List SyntaxNodeKind :=
    [``Term.explicitBinder, ``Term.implicitBinder, ``Term.strictImplicitBinder, ``Term.instBinder]

private def isImplicitBinder (b : Syntax) : Bool :=
  b.isOfKind ``Term.implicitBinder || b.isOfKind ``Term.strictImplicitBinder

private def kinds : List String :=
  ["theorem", "def", "abbrev", "instance", "structure", "class", "inductive", "axiom", "opaque",
   "example"]

private def defLike : List String :=
  ["def", "abbrev", "class", "structure", "inductive", "instance"]

/-- Metric `declarations`: Declarations by kind, definition-like declarations per theorem, and
signatures with implicit binders. -/
def declarations : Metric where
  name := "declarations"
  description := "declarations by kind, definition-like declarations per theorem, and \
    signatures with implicit binders"
  needsSource := true
  run ctx := do
    let decls := ctx.declarations
    let mut counts : Std.HashMap String Nat := {}
    let mut nImplicit := 0
    for d in decls do
      if let some k := declarationKind? d then
        counts := counts.insert k (counts.getD k 0 + 1)
        if k != "example" && (signatureBinders d).any isImplicitBinder then
          nImplicit := nImplicit + 1
    -- `deriving` clauses and `attribute [instance]` commands also declare instances
    let mut nDerived := 0
    let mut nAttrInstance := 0
    for f in ctx.files do
      for c in f.commands do
        -- `deriving instance C, D for A, B` declares an instance per class and type; a
        -- `deriving` clause on a declaration, one per class
        let commands := nodesOfKind ``Command.deriving c
        let inCommands := commands.foldl (· + countKind ``Command.derivingClass ·) 0
        nDerived := nDerived + (countKind ``Command.derivingClass c - inCommands) +
          commands.foldl (init := 0) fun n d =>
            n + countKind ``Command.derivingClass d * d[5].getSepArgs.size
        for a in nodesOfKind ``Command.attribute c do
          if (attributesUnder a).contains `instance then
            nAttrInstance := nAttrInstance + 1
    counts := counts.insert "instance" (counts.getD "instance" 0 + nDerived + nAttrInstance)
    let n (k : String) := counts.getD k 0
    let nDefLike := defLike.foldl (· + n ·) 0
    return { columns :=
      #[("n_decls", toJson (kinds.foldl (fun a k => if k == "example" then a else a + n k) 0))] ++
      (kinds.map fun k => (s!"n_{k}", toJson (n k))).toArray ++
      #[("n_def_like", toJson nDefLike),
        ("def_like_to_theorem_ratio", ratio nDefLike (n "theorem")),
        ("n_decls_implicit_args", toJson nImplicit), ("n_new_classes", toJson (n "class")),
        ("n_new_instances", toJson (n "instance"))] }

/-- Metric `implicit_args`: Binder groups in declaration signatures, by kind. -/
def implicitArgs : Metric where
  name := "implicit_args"
  description := "binder groups in declaration signatures, by kind"
  needsSource := true
  run ctx := do
    let binders := ctx.declarations.foldl (· ++ signatureBinders ·) #[]
    let count (k : SyntaxNodeKind) := (binders.filter (·.getKind == k)).size
    let explicit := count ``Term.explicitBinder
    let others := count ``Term.implicitBinder + count ``Term.strictImplicitBinder +
      count ``Term.instBinder
    return { columns := #[("n_ia_explicit", toJson explicit),
      ("n_ia_implicit", toJson (count ``Term.implicitBinder)),
      ("n_ia_strict", toJson (count ``Term.strictImplicitBinder)),
      ("n_ia_inst", toJson (count ``Term.instBinder)),
      ("ia_implicit_ratio", ratio others (explicit + others))] }

/-- Metric `proof_mode`: Theorems proved by a term and by a tactic block. -/
def proofMode : Metric where
  name := "proof_mode"
  description := "theorems proved by a term and by a tactic block"
  needsSource := true
  run ctx := do
    let bodies := ctx.declarations.filter isTheorem |>.filterMap bodyOf?
    let nTactic := (bodies.filter isTacticBody).size
    let nTerm := bodies.size - nTactic
    return { columns := #[("n_pm_term", toJson nTerm), ("n_pm_tactic", toJson nTactic),
      ("pm_term_ratio", ratio nTerm bodies.size)] }

/-- Applications of the attribute `name` under `s`, in `@[…]` and `attribute […]`. -/
private def countAttribute (name : Name) (s : Syntax) : Nat :=
  (attributesUnder s).filter (· == name) |>.size

/-- Metric `reducibility`: `@[irreducible]` and `@[reducible]` attributes, `abbrev`s and `def`s. -/
def reducibility : Metric where
  name := "reducibility"
  description := "`@[irreducible]` and `@[reducible]` attributes, `abbrev`s and `def`s"
  needsSource := true
  run ctx := do
    let cmds := ctx.files.foldl (· ++ ·.commands) #[]
    let sum (f : Syntax → Nat) := toJson (cmds.foldl (· + f ·) 0)
    let decls := ctx.declarations
    let nIrreducible := cmds.foldl (· + countAttribute `irreducible ·) 0
    let nAbbrev := (decls.filter (·.isOfKind ``Command.abbrev)).size
    let nDef := (decls.filter (·.isOfKind ``Command.definition)).size
    return { columns := #[
      ("n_red_irreducible", toJson nIrreducible),
      ("n_red_reducible", sum (countAttribute `reducible)),
      ("n_red_abbrev", toJson nAbbrev), ("n_red_def", toJson nDef),
      ("red_irreducible_per_def", ratio nIrreducible nDef 4),
      ("red_abbrev_per_def", ratio nAbbrev nDef 4)] }

/-- Metric `recursion_style`: `termination_by` and `decreasing_by` clauses. -/
def recursionStyle : Metric where
  name := "recursion_style"
  description := "`termination_by` and `decreasing_by` clauses"
  needsSource := true
  run ctx := do
    let cmds := ctx.files.foldl (· ++ ·.commands) #[]
    let sum (k : SyntaxNodeKind) := cmds.foldl (· + countKind k ·) 0
    let t := sum ``Termination.terminationBy
    let d := sum ``Termination.decreasingBy
    return { columns := #[("n_rec_termination_by", toJson t), ("n_rec_decreasing_by", toJson d),
      ("n_rec_well_founded", toJson (t + d)),
      ("rec_uses_well_founded", toJson (decide (t + d > 0)))] }

end LeanMetrics
