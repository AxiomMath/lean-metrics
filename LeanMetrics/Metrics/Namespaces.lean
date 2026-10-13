/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic
import LeanMetrics.Syntax

/-! # Namespaces and sections

`namespace` and `section` commands, distinct namespaces, and nesting depth.
-/

public section

open Lean Parser

namespace LeanMetrics

/-- Number of scopes a name opens or closes: one per component (`namespace A.B` opens two),
or one when the optional name of a `section` or `end` is absent. -/
private def scopeCount (optName : Syntax) : Nat :=
  match (identsOf optName)[0]? with
  | some n => n.getNumParts
  | none => 1

/-- Metric `namespaces`: Namespace and section commands, distinct namespaces, and maximum nesting
depth. -/
def namespaces : Metric where
  name := "namespaces"
  description := "namespace and section commands, distinct namespaces, and maximum nesting depth"
  needsSource := true
  run ctx := do
    let mut nNamespace := 0
    let mut nSection := 0
    let mut names : NameSet := {}
    let mut maxDepth := 0
    for file in ctx.files do
      -- the namespace each open scope is in, innermost first; scopes close at the end of a file
      let mut scopes : List Name := []
      for cmd in file.commands do
        let current := scopes.headD .anonymous
        let k := cmd.getKind
        if k == ``Command.namespace then
          nNamespace := nNamespace + 1
          -- the namespace entered, resolved against the enclosing one
          names := names.insert (current ++ cmd[1].getId)
          -- `namespace A.B` opens a scope for `A` and one for `A.B`
          for c in cmd[1].getId.components do
            scopes := (scopes.headD current ++ c) :: scopes
        else if k == ``Command.section then
          nSection := nSection + 1
          scopes := List.replicate (scopeCount cmd[2]) current ++ scopes
        else if k == ``Command.end then
          scopes := scopes.drop (scopeCount cmd[1])
        maxDepth := max maxDepth scopes.length
    return { columns := #[
      ("n_ns_cmds", toJson nNamespace), ("n_ns_distinct", toJson names.size),
      ("n_ns_sections", toJson nSection), ("n_ns_max_depth", toJson maxDepth)] }

end LeanMetrics
