/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic
import LeanMetrics.Shake
import LeanMetrics.Stats
import LeanMetrics.Syntax
import Lean.Parser.Module

/-! # Imports

Import counts, and the imports `lake shake` would remove (`LeanMetrics.Shake`).
A second count uses only constants. Tactic imports are reported separately.
-/

public section

open Lean

namespace LeanMetrics

/-- A set of module indices. -/
private abbrev ModuleSet := Nat

/-- The imports a module was compiled with. `Init` is left out, being implicit, unless the file
starts with `prelude` and so writes it (`explicitInit`). -/
private def importsOf (env : Environment) (idx : Nat) (explicitInit := false) : Array Name :=
  let imports := (env.header.moduleData[idx]?.map (·.imports.map (·.module))).getD #[]
  if explicitInit then imports else imports.filter (· != `Init)

private def Context.moduleIdx? (ctx : Context) (m : Name) : Option Nat :=
  ctx.env.getModuleIdx? m |>.map (·.toNat)

/-- For every module, the set of modules it imports directly or indirectly. Module indices are
in import order, so each module's imports are finished before it. -/
private def transitiveImports (env : Environment) : Array ModuleSet := Id.run do
  let mods := env.header.moduleData
  let mut closure : Array ModuleSet := Array.replicate mods.size 0
  for i in [0:mods.size] do
    let mut s : ModuleSet := 0
    for imp in mods[i]!.imports do
      if let some j := env.getModuleIdx? imp.module then
        s := s ||| (1 <<< j.toNat) ||| closure[j.toNat]!
    closure := closure.set! i s
  return closure

/-- For each of `modules`, the set of modules defining a constant that the module's own
constants use, directly or through other constants. -/
private def requiredModules (env : Environment) (modules : Array Nat) : Array ModuleSet := Id.run do
  let moduleOf (c : Name) : Option Nat :=
    (env.getModuleIdxFor? c).map (·.toNat)
  -- `needs c` is the set of modules defining a constant `c` uses, transitively
  let mut needs : Std.HashMap Name ModuleSet := {}
  -- constants already scheduled; one on a cycle (an inductive and its constructors) combines
  -- whatever its cycle partners have so far
  let mut pushed : NameSet := {}
  let mut result := #[]
  for m in modules do
    let mut acc : ModuleSet := 0
    for root in env.header.moduleData[m]!.constNames do
      if root.isInternal then continue
      unless pushed.contains root do
        pushed := pushed.insert root
        -- each constant is visited twice: once to push what it uses, once to combine their sets
        let mut stack : Array (Name × Bool) := #[(root, false)]
        while h : stack.size > 0 do
          let (c, ready) := stack[stack.size - 1]
          stack := stack.pop
          let used := (env.find? c).map usedConstants |>.getD {}
          if ready then
            -- a loop rather than a fold: a closure over `needs` would copy it on the next insert
            let mut s : ModuleSet := 0
            for u in used do
              if let some j := moduleOf u then s := s ||| (1 <<< j)
              s := s ||| needs.getD u 0
            needs := needs.insert c s
          else
            stack := stack.push (c, true)
            for u in used do
              unless pushed.contains u do
                pushed := pushed.insert u
                stack := stack.push (u, false)
      acc := acc ||| needs.getD root 0
    result := result.push acc
  return result
where
  /-- Constants in a constant's type and value, and the constructors of an inductive. -/
  usedConstants (ci : ConstantInfo) : NameSet :=
    let s := ci.type.getUsedConstantsAsSet
    let s := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstantsAsSet.foldl (·.insert ·) s
      | none => s
    match ci with
    | .inductInfo v => v.ctors.foldl (·.insert ·) s
    | .recInfo v => v.all.foldl (·.insert ·) s
    | _ => s

/-- Whether `m` is a module of Mathlib. -/
def isMathlibModule (m : Name) : Bool := m.getRoot == `Mathlib

/-- Tactic modules (`Mathlib.Tactic`, `Lean.Elab.Tactic`). The constants-only count skips them. -/
def isTacticModule (m : Name) : Bool :=
  (`Mathlib.Tactic).isPrefixOf m || (`Lean.Elab.Tactic).isPrefixOf m

/-- Metric `imports`: Imports per file from Mathlib and from elsewhere, and distinct Mathlib modules
imported. -/
def imports : Metric where
  name := "imports"
  description := "imports per file from Mathlib and from elsewhere, and distinct Mathlib \
    modules imported"
  needsSource := false
  run ctx := do
    let perFile := ctx.modules.filterMap fun m =>
      (ctx.moduleIdx? m).map (importsOf ctx.env · (ctx.preludeModules.contains m))
    let mathlib := perFile.map fun is => (is.filter isMathlibModule).size
    let other := perFile.map fun is => (is.filter (!isMathlibModule ·)).size
    let distinct : NameSet := perFile.foldl (fun s is => is.foldl (fun s i =>
      if isMathlibModule i then s.insert i else s) s) {}
    return { columns := #[("mathlib_imports_per_file", mean mathlib 2),
      ("nonmathlib_imports_per_file", mean other 2), ("n_mathlib_modules", toJson distinct.size)] }

/-- Metric `import_discipline`: Imports written, `import Mathlib` of the whole library, and distinct
modules imported. -/
def importDiscipline : Metric where
  name := "import_discipline"
  description := "imports written, `import Mathlib` of the whole library, and distinct modules \
    imported"
  needsSource := false
  run ctx := do
    let all := ctx.modules.foldl (fun acc m =>
      let explicitInit := ctx.preludeModules.contains m
      acc ++ ((ctx.moduleIdx? m).map (importsOf ctx.env · explicitInit)).getD #[]) #[]
    let distinct : NameSet := all.foldl (·.insert ·) {}
    let nWholesale := (all.filter (· == `Mathlib)).size
    return { columns := #[("n_imp_import", toJson all.size),
      ("n_imp_mathlib_wholesale", toJson nWholesale), ("n_imp_distinct", toJson distinct.size),
      ("imp_mathlib_wholesale", toJson (decide (nWholesale > 0)))] }

/-- What a file's header says to `lake shake`: imports marked `-- shake: keep`, and the
`keep-all` and `keep-downstream` markers on its `module` line. -/
private def directives (file : SourceFile) : Shake.Directives :=
  let marked (s : Syntax) (m : String) := s.getTrailing?.any (·.toString.contains s!"shake: {m}")
  let module? := findKind? ``Parser.Module.moduleTk file.header
  -- `public? meta? import all? M`; outside the module system every import is public
  let decode (imp : Syntax) : Import :=
    { module := imp[4].getId, isExported := module?.isNone || imp[0].getNumArgs > 0,
      isMeta := imp[1].getNumArgs > 0, importAll := imp[3].getNumArgs > 0 }
  { keep := (nodesOfKind ``Parser.Module.import file.header).filterMap fun imp =>
      if marked imp "keep" then some (decode imp) else none
    keepAll := module?.any (marked · "keep-all")
    keepDownstream := module?.any (marked · "keep-downstream")
    isPrelude := (findKind? ``Parser.Module.prelude file.header).isSome }

/-- Metric `import_minimizability`: Imports `lake shake` would remove or add, the same count from
constants alone, tactic imports, and the size of the import cone. -/
def importMinimizability : Metric where
  name := "import_minimizability"
  description := "imports `lake shake` would remove or add, the same count from constants \
    alone, tactic imports, and the size of the import cone"
  needsSource := true
  needsModuleView := true
  run ctx := do
    let env := ctx.env
    let names := env.header.moduleNames
    let own := ctx.modules.filterMap ctx.moduleIdx?
    -- the analysis of `lake shake`, on the environment loaded as it loads it
    let some view := ctx.moduleView | throwError "the module view was not loaded"
    let dirs := ctx.files.foldl (fun m f => m.insert f.module (directives f))
      (∅ : NameMap Shake.Directives)
    let verdicts := Shake.run view <| ctx.modules.filterMap fun m =>
      (view.getModuleIdx? m).map fun i => (i.toNat, (dirs.find? m).getD {})
    let vnames := view.header.moduleNames
    -- only a file without `prelude` imports `Init` implicitly
    let implicitInit (i : Nat) (imp : Import) :=
      imp.module == `Init && !ctx.preludeModules.contains vnames[i]!
    let authored (f : Shake.Verdict → Array Import) (i : Nat) (v : Shake.Verdict) :=
      (f v).filter (!implicitInit i ·)
    let total (f : Shake.Verdict → Array Import) :=
      verdicts.foldl (fun n (i, v) => n + (authored f i v).size) 0
    let nWritten := verdicts.foldl (fun n (i, _) =>
      n + (view.header.moduleData[i]!.imports.filter (!implicitInit i ·)).size) 0
    let nRemove := total (·.remove)
    let nUnimplied := total (·.removeUnimplied)
    let nAdd := total (·.add)
    let byModule (f : Shake.Verdict → Array Import) := Json.mkObj <| verdicts.toList.filterMap
      fun (i, v) => let is := authored f i v
        if is.isEmpty then none else some (vnames[i]!.toString, toJson (is.map toString))
    -- the same count, from constants alone
    let closure := transitiveImports env
    let required := requiredModules env own
    let isInit (j : Nat) := (`Init).isPrefixOf names[j]!
    let mut nRemovable := 0; let mut nUnused := 0; let mut nTactic := 0
    let mut usesMathlib := false
    let mut cone : ModuleSet := 0
    for m in own, req in required do
      let imports := (importsOf env m (ctx.preludeModules.contains names[m]!)).filterMap fun i =>
        (env.getModuleIdx? i).map (i, ·.toNat)
      let reach := imports.map fun (_, j) => closure[j]! ||| (1 <<< j)
      -- the needed modules, other than the module itself and `Init`
      let needed := (List.range names.size).filter fun j => req.testBit j && j != m && !isInit j
      nTactic := nTactic + (imports.filter (isTacticModule ·.1)).size
      if imports.any (isMathlibModule ·.1) then usesMathlib := true
      for (_, j) in imports do cone := cone ||| closure[j]! ||| (1 <<< j)
      -- an import stays when it is the only one through which some needed module is reachable
      let sole := needed.foldl (init := (0 : Nat)) fun s r =>
        match (List.range imports.size).filter (reach[·]!.testBit r) with
        | [k] => s ||| (1 <<< k)
        | _ => s
      let judged := (List.range imports.size).filter fun k => !isTacticModule imports[k]!.1
      let neededSet := needed.foldl (fun s r => s ||| (1 <<< r)) (0 : Nat)
      nRemovable := nRemovable + (judged.filter (!sole.testBit ·)).length
      nUnused := nUnused + (judged.filter fun k => reach[k]! &&& neededSet == 0).length
    let coneSize := (List.range names.size).filter cone.testBit |>.length
    return {
      columns := #[("n_impmin_imports", toJson nWritten),
        ("n_impmin_removable_imports", toJson nRemove),
        ("impmin_frac_removable", ratio nRemove nWritten),
        ("n_impmin_unused_imports", toJson nUnimplied),
        ("impmin_frac_unused", ratio nUnimplied nWritten),
        ("n_impmin_imports_to_add", toJson nAdd),
        ("n_impmin_removable_by_constants", toJson nRemovable),
        ("n_impmin_unused_by_constants", toJson nUnused),
        ("n_impmin_tactic_imports", toJson nTactic),
        ("n_impmin_import_cone_size", toJson coneSize),
        ("impmin_uses_import_mathlib", toJson usesMathlib)]
      details := Json.mkObj [("remove_by_module", byModule (·.remove)),
        ("add_by_module", byModule (·.add))] }

end LeanMetrics
