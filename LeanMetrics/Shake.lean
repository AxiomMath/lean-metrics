/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang
-/
module

public import Lean.Environment
import Lean.ExtraModUses
import Lean.ResolveName
import Lean.Compiler.MetaAttr

/-! # Unused imports, as `lake shake` finds them

Imports `lake shake` would remove, and those it would add. No file is edited.
Also runs on projects outside the module system, where `lake shake` does not.
-/

public section

open Lean

namespace LeanMetrics.Shake

/-- Module indices as the bits of a natural number. -/
abbrev Bitset := Nat

/-- The visibility an import has, or a need calls for. -/
structure Kind where
  isExported : Bool
  isMeta : Bool
  deriving BEq, Inhabited

/-- The four kinds: public, private, public `meta` and private `meta`. -/
def Kind.all : Array Kind :=
  #[⟨true, false⟩, ⟨false, false⟩, ⟨true, true⟩, ⟨false, true⟩]

/-- The kind of an import. -/
def Kind.ofImport (imp : Import) : Kind := ⟨imp.isExported, imp.isMeta⟩

/-- A set of modules for each kind. -/
structure Needs where
  pub : Bitset := 0
  priv : Bitset := 0
  metaPub : Bitset := 0
  metaPriv : Bitset := 0
  deriving Inhabited

namespace Needs

/-- The modules needed at kind `k`. -/
def get (n : Needs) : Kind → Bitset
  | ⟨true, false⟩ => n.pub
  | ⟨false, false⟩ => n.priv
  | ⟨true, true⟩ => n.metaPub
  | ⟨false, true⟩ => n.metaPriv

/-- Replace the modules needed at kind `k`. -/
def set (n : Needs) (k : Kind) (s : Bitset) : Needs :=
  match k with
  | ⟨true, false⟩ => { n with pub := s }
  | ⟨false, false⟩ => { n with priv := s }
  | ⟨true, true⟩ => { n with metaPub := s }
  | ⟨false, true⟩ => { n with metaPriv := s }

/-- Whether module `j` is needed at kind `k`. -/
def has (n : Needs) (k : Kind) (j : Nat) : Bool := (n.get k).testBit j

/-- Add modules needed at kind `k`. -/
def union (n : Needs) (k : Kind) (s : Bitset) : Needs := n.set k (n.get k ||| s)

/-- Remove modules from those needed at kind `k`. -/
def sub (n : Needs) (k : Kind) (s : Bitset) : Needs := n.set k (n.get k ^^^ (n.get k &&& s))

end Needs

@[inline] private def bit (j : Nat) : Bitset := 1 <<< j

/-- The modules reachable from a module through importing module `j` by `imp`, given `j`'s
own: which of them the importer may use at which kind. -/
def addTransitiveImps (trans : Needs) (imp : Import) (j : Nat) (impTrans : Needs) : Needs :=
  Id.run do
  let mut t := trans
  if imp.isExported && !imp.isMeta then
    t := t.union ⟨true, false⟩ (bit j ||| impTrans.pub)
  if !imp.isExported && !imp.isMeta then
    t := t.union ⟨false, false⟩ (bit j ||| impTrans.pub)
    if imp.importAll then t := t.union ⟨false, false⟩ (impTrans.pub ||| impTrans.priv)
  if imp.isExported then
    t := t.union ⟨true, true⟩ impTrans.metaPub
    if imp.isMeta then t := t.union ⟨true, true⟩ (bit j ||| impTrans.pub ||| impTrans.metaPub)
  if !imp.isExported then
    if imp.isMeta then t := t.union ⟨false, true⟩ (bit j ||| impTrans.pub ||| impTrans.metaPub)
    if imp.importAll then t := t.union ⟨false, true⟩ (impTrans.metaPub ||| impTrans.metaPriv)
    else t := t.union ⟨false, true⟩ impTrans.metaPub
  return t

/-- Whether a declaration runs at compile time. `match_` auxiliaries are inlined, so their
enclosing declaration decides. -/
private def isDeclMeta' (env : Environment) (n : Name) : Bool :=
  let n := if n.isStr && (n.getString!.startsWith "match_" || n.getString! == "_unsafe_rec") then
    n.getPrefix else n
  isMarkedMeta env n || isDeclMeta env n

/-- Load the one environment extension the analysis reads, the recorded indirect module uses, into
an environment imported without its extensions. -/
def loadIndirectModUses (env : Environment) : IO Environment := do
  let is := indirectModUseExt.toEnvExtension.getState env
  let state ← indirectModUseExt.addImportedFn is.importedEntries { env, opts := {} }
  return indirectModUseExt.toEnvExtension.setState (asyncMode := .sync) env { is with state }

/-- Everything the analysis of one module reads, computed once for the environment. -/
structure State where
  env : Environment
  /-- Per module, the modules it may use at each kind through its imports. -/
  transDeps : Array Needs
  /-- The same before any module's imports were changed. -/
  transDepsOrig : Array Needs
  /-- Modules that must stay imported wherever they are reachable. -/
  preserve : Bitset
  reservedNames : Std.HashSet Name
  indirectModUses : Std.HashMap Name (Array ModuleIdx)

/-- The state before any module is analysed. -/
def State.init (env : Environment) : State := Id.run do
  let mods := env.header.moduleData
  let mut trans : Array Needs := #[]
  let mut preserve : Bitset := 0
  for h : i in [0:mods.size] do
    let mut t : Needs := {}
    for imp in mods[i].imports do
      if let some j := env.getModuleIdx? imp.module then
        t := addTransitiveImps t imp j.toNat trans[j.toNat]!
    trans := trans.push t
    if isExtraRevModUse env i then preserve := preserve ||| bit i
  let reservedNames := env.constants.fold (init := {}) fun s c _ =>
    if isReservedName env c then s.insert c else s
  return { env, transDeps := trans, transDepsOrig := trans, preserve, reservedNames,
           indirectModUses := indirectModUseExt.getState env }

/-- The modules module `i` needs, by kind: where a used constant is defined, where elaboration
recorded a use, or where an attribute ties a used constant. -/
def calcNeeds (s : State) (i : Nat) : Needs := Id.run do
  let env := s.env
  let mut needs : Needs := {}
  for ci in env.header.moduleData[i]!.constants do
    let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
    let k : Kind := ⟨pubCI?.isSome, isDeclMeta' env ci.name⟩
    needs := visit k ci.type needs
    if let some e := ci.value? (allowOpaque := true) then
      let k := if k.isMeta then k
        else if pubCI?.any (·.hasValue (allowOpaque := true)) then ⟨true, false⟩ else ⟨false, false⟩
      needs := visit k e needs
  for use in getExtraModUses env i do
    if let some j := env.getModuleIdx? use.module then
      needs := needs.union ⟨use.isExported, use.isMeta⟩ (bit j.toNat)
  return needs
where
  visit (k : Kind) (e : Expr) (needs : Needs) : Needs :=
    e.foldConsts needs fun c needs => Id.run do
      -- references to reserved names can be regenerated in place; `_simp_` ones stand for
      -- their base
      if s.reservedNames.contains c then return needs
      let c := if c.isStr && c.getString!.startsWith "_simp_" then c.getPrefix else c
      let some j := s.env.getModuleIdxFor? c | return needs
      let j := j.toNat
      let k := { k with isMeta := k.isMeta && !isDeclMeta' s.env c }
      if j == i then return needs
      let mut needs := needs.union k (bit j)
      for ind in s.indirectModUses[c]?.getD #[] do
        if s.transDeps[i]!.has k ind.toNat then needs := needs.union k (bit ind.toNat)
      return needs

/-- The verdict on one module's imports. -/
structure Verdict where
  /-- Imports `lake shake` would remove. -/
  remove : Array Import
  /-- Imports it would add in their place. -/
  add : Array Import
  /-- Imports it would remove under `--keep-implied`: those no kept import implies either. -/
  removeUnimplied : Array Import

/-- What a module's source says about its imports. -/
structure Directives where
  /-- Imports marked `-- shake: keep`. -/
  keep : Array Import := #[]
  /-- The header is marked `-- shake: keep-all`: no import is removed, only missing ones added. -/
  keepAll : Bool := false
  /-- The header is marked `-- shake: keep-downstream`: modules importing this one keep it. -/
  keepDownstream : Bool := false
  /-- The file starts with `prelude`, so it has no implicit `Init` import. -/
  isPrelude : Bool := false

/-- Analyse module `i` and update the state so that modules importing it see its new imports. -/
def visitModule (s : State) (i : Nat) (dir : Directives := {}) : Verdict × State := Id.run do
  let env := s.env
  let mods := env.header.moduleData
  let modName := env.header.modules[i]!.module
  let mut deps := calcNeeds s i
  -- a file outside the module system has no private or `meta` imports: each of its imports
  -- provides everything, so all its needs are of one kind
  unless mods[i]!.isModule do
    deps := { pub := deps.pub ||| deps.priv ||| deps.metaPub ||| deps.metaPriv }
  for imp in mods[i]!.imports do
    if dir.keepAll || dir.keep.contains imp then
      if let some j := env.getModuleIdx? imp.module then
        deps := deps.union (Kind.ofImport imp) (bit j.toNat)
  -- modules to preserve stay needed, downgraded to a private, non-`meta` import
  for j in [0:mods.size] do
    for k in Kind.all do
      if s.transDepsOrig[i]!.has k j && s.preserve.testBit j then
        deps := deps.union ⟨false, false⟩ (bit j)
  -- keep only needs no other need implies
  for j in [0:mods.size] do
    for k in Kind.all do
      if !dir.keepAll && deps.has k j then
        let imp : Import := { module := .anonymous, isExported := k.isExported, isMeta := k.isMeta }
        let t := addTransitiveImps {} imp j s.transDeps[j]!
        for k' in Kind.all do
          deps := deps.sub k' ((t.sub k' (bit j)).get k')
  if !dir.isPrelude then
    if let some j := env.getModuleIdx? `Init then
      deps := (deps.union ⟨true, false⟩ (bit j.toNat)).union ⟨true, true⟩ (bit j.toNat)
  -- what the kept imports make reachable
  let mut transDeps : Needs := {}
  -- a module's own submodules imported as `meta` are kept as plain imports
  let mut alwaysAdd : Array Import := #[]
  for imp in mods[i]!.imports do
    let some j := env.getModuleIdx? imp.module | continue
    let j := j.toNat
    let k := Kind.ofImport imp
    if deps.has k j || imp.importAll then
      transDeps := addTransitiveImps transDeps imp j s.transDeps[j]!
      deps := deps.union k (bit j)
    -- a module's own submodules stay imported
    else if modName.isPrefixOf imp.module then
      let imp := { imp with isMeta := false }
      transDeps := addTransitiveImps transDeps imp j s.transDeps[j]!
      deps := deps.union { k with isMeta := false } (bit j)
      unless mods[i]!.imports.contains imp do alwaysAdd := alwaysAdd.push imp
  -- add what is needed and not reachable, latest modules first so that few imports are added
  let mut newTransDeps := transDeps
  let mut add : Array Import := #[]
  for j in (List.range mods.size).reverse do
    for k in Kind.all do
      if deps.has k j && !newTransDeps.has k j &&
        !newTransDeps.has { k with isExported := true } j then
        let imp : Import :=
          { module := env.header.modules[j]!.module, isExported := k.isExported,
            isMeta := k.isMeta }
        unless mods[i]!.imports.contains imp do add := add.push imp
        deps := deps.union k (bit j)
        newTransDeps := addTransitiveImps newTransDeps imp j s.transDeps[j]!
  add := alwaysAdd ++ add
  let mut remove : Array Import := #[]
  let mut removeUnimplied : Array Import := #[]
  for imp in mods[i]!.imports do
    let some j := env.getModuleIdx? imp.module | continue
    let j := j.toNat
    let k := Kind.ofImport imp
    let unused := !deps.has k j ||
      -- a private import is redundant once the public one is there
      !k.isExported && !imp.importAll && newTransDeps.has { k with isExported := true } j
    if unused then remove := remove.push imp
    if unused && !newTransDeps.has k j then removeUnimplied := removeUnimplied.push imp
  -- modules importing this one now see its new imports
  let mut t : Needs := {}
  for imp in mods[i]!.imports ++ add do
    unless remove.contains imp do
      if let some j := env.getModuleIdx? imp.module then
        t := addTransitiveImps t imp j.toNat s.transDeps[j.toNat]!
  return ({ remove, add, removeUnimplied }, { s with transDeps := s.transDeps.set! i t })

/-- Analyse `modules` (indices, in import order, with what their sources say) one after another,
each seeing the new imports of those before it. -/
def run (env : Environment) (modules : Array (Nat × Directives)) : Array (Nat × Verdict) :=
  Id.run do
  let mut s := State.init env
  let mut out := #[]
  for (i, dir) in modules do
    if dir.keepDownstream then s := { s with preserve := s.preserve ||| bit i }
    let (v, s') := visitModule s i dir
    s := s'
    out := out.push (i, v)
  return out

end LeanMetrics.Shake
