/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic

/-! # Build warnings

Warnings Lake recorded for the project's modules, from its trace files.
A linter warning is grouped by the linter it names; other warnings by their text.
-/

public section

open Lean

namespace LeanMetrics

/-- Warning groups, each with the linters that raise it and phrases that identify its text. -/
def warningKinds : List (String × List String × List String) :=
  [("unused_variable", ["linter.unusedVariables"], ["unused variable"]),
   ("unused_simp_arg", ["linter.unusedSimpArgs"], ["simp argument is unused"]),
   ("unused_section_var", ["linter.unusedSectionVars"],
      ["section variable(s) unused", "automatically included section variable"]),
   ("unreferenced_binder", [], ["is not explicitly referenced"]),
   ("deprecated", ["linter.deprecated"], ["deprecated"]),
   ("simpa_to_simp", ["linter.unnecessarySimpa"], ["instead of 'simpa'", "instead of `simpa`"]),
   ("def_for_prop", [], ["use `theorem` instead of `def`"]),
   ("seq_focus", ["linter.unnecessarySeqFocus"], []),
   ("unused_tactic", ["linter.unusedTactic"], ["Unused tactic linter"]),
   ("unreachable_tactic", ["linter.unreachableTactic"],
      ["unreachable tactic", "is never executed"]),
   ("sorry", [], ["declaration uses 'sorry'", "declaration uses `sorry`"]),
   ("style", ["linter.style"], ["empty lines within commands", "line is too long"]),
   ("overlapping_instances", [], ["Overlapping instance parameters"])]

/-- The linter a warning names in its note on how to disable it (`set_option linter.X false`). -/
private def linterOf? (msg : String) : Option String := do
  let [_, after] := msg.splitOn "set_option linter." |>.take 2 | none
  let name := after.takeWhile fun c => c.isAlphanum || c == '.'
  some ("linter." ++ name.toString)

private def warningKind (msg : String) : String :=
  let hasPhrase (p : String) := (msg.splitOn p).length > 1
  let byLinter := (linterOf? msg).bind fun l =>
    (warningKinds.find? fun (_, linters, _) => linters.any (l.startsWith ·)).map (·.1)
  byLinter.getD <|
    ((warningKinds.find? fun (_, _, phrases) => phrases.any hasPhrase).map (·.1)).getD "other"

/-- Metric `warnings`: Compiler and linter warnings of the project's own modules, by kind. -/
def warnings : Metric where
  name := "warnings"
  description := "compiler and linter warnings of the project's own modules, by kind"
  needsSource := false
  run ctx := do
    let ws := ctx.buildLog.filter (·.level == .warning)
    let modules : NameSet := ws.foldl (·.insert ·.module) {}
    let kinds := ws.map (warningKind ·.message)
    let names := warningKinds.map (·.1) ++ ["other"]
    return { columns := #[
      ("n_warnings", toJson ws.size), ("n_files_with_warnings", toJson modules.size),
      ("warnings_complete", toJson ctx.modulesWithoutLog.isEmpty)] ++
      (names.map fun k => (s!"n_warn_{k}", toJson (kinds.filter (· == k)).size)).toArray }

end LeanMetrics
