/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang
-/
module

public import Lean.Environment
import Lean.AuxRecursor
import Lean.Class
import Lean.DeclarationRange
import Lean.Meta.Match.MatcherInfo
import Lean.ProjFns
import Lean.Structure

/-! # Declarations an author wrote

Constants with their own source position. Generated constants are excluded.
-/

public section

open Lean Meta

namespace LeanMetrics

/-- Whether `a` and `b` have the same declaration position in the same module. -/
def sameOrigin (env : Environment) (a b : Name) : Bool :=
  match declRangeExt.find? env a, declRangeExt.find? env b with
  | some ra, some rb =>
    ra.selectionRange.pos == rb.selectionRange.pos &&
      env.getModuleIdxFor? a == env.getModuleIdxFor? b
  | _, _ => false

/-- Whether `n` has a source position distinct from its prefix.
For example a constructor, a `where` helper, a `deriving` instance, or a parser from
`syntax`, `notation` or `macro`. -/
def hasOwnDeclaration (env : Environment) (n : Name) : Bool :=
  (declRangeExt.find? env n).isSome && !sameOrigin env n n.getPrefix

/-- Whether structure `s` has `target` among its ancestors. -/
partial def hasAncestor (env : Environment) (s target : Name) (visited : NameSet := {}) : Bool :=
  if visited.contains s then false
  else (getStructureInfo? env s).any fun info =>
    info.parentInfo.any fun p =>
      p.structName == target || hasAncestor env p.structName target (visited.insert s)

/-- Whether `n` converts a structure to one it builds on: the coercion `extends` generates, or a
`toX` in the structure's namespace when the structure is a class or `X` is an ancestor
(`Field.toSemifield`). -/
def isParentProjection (env : Environment) (n : Name) : Bool :=
  match getStructureInfo? env n.getPrefix, n with
  | none, _ => false
  | some info, .str p s =>
    info.parentInfo.any (·.projFn == n) ||
      (s.startsWith "to" && s.length > 2 &&
        let target := (s.drop 2).toString
        (target.startsWith "OfNat" && target.any Char.isDigit) || isClass env p ||
          (getStructureInfo? env (.mkSimple target)).isSome && hasAncestor env p (.mkSimple target))
  | some info, _ => info.parentInfo.any (·.projFn == n)

/-- Namespaces of tactic implementations. -/
def tacticNamespaces : List Name :=
  [`Lean.Grind, `Lean.Omega, `Lean.RArray, `Lean.Meta, `Lean.Elab, `Int.Linear, `Nat.Linear,
   `Nat.ToInt, `Std.Tactic, `Std.Sat, `Std.Internal, `Mathlib.Tactic, `Mathlib.Meta, `Aesop, `Qq]

/-- Whether `n` is in one of the `tacticNamespaces`. -/
def isTacticInternal (n : Name) : Bool := tacticNamespaces.any (·.isPrefixOf n)

/-- Whether `n` is a declaration written in the source.
Excludes generated constants: equation lemmas, `match` auxiliaries, `_proof_n` helpers,
recursors, `noConfusion`, matchers, projections and `extends` coercions. -/
def isAuthored (env : Environment) (n : Name) : Bool :=
  !((privateToUserName? n).getD n).isInternalDetail && hasOwnDeclaration env n &&
    !isAuxRecursor env n && !isNoConfusion env n && !(env.find? n matches some (.recInfo _)) &&
    !(getMatcherInfoCore? env n).isSome && !isParentProjection env n &&
    !env.isProjectionFn n

/-- The declaration a generated constant belongs to: the inductive of a constructor or
recursor, or the prefix of a helper sharing its parent's source position (`foo._proof_1` belongs
to `foo`). Returns `n` itself when there is none. -/
def owner (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) => v.induct
  | some (.recInfo v) => v.name.getPrefix
  | _ => if sameOrigin env n n.getPrefix then n.getPrefix else n

end LeanMetrics
