/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic
import LeanMetrics.Stats
import LeanMetrics.Syntax
import Lean.Parser.Syntax

/-! # Options, attributes and metaprogramming

`set_option`, attribute applications, and `macro`, `elab` and `syntax` commands.
-/

public section

open Lean Parser

namespace LeanMetrics

/-- Every `set_option` in the project, at command, term and tactic level, by option name. -/
private def Context.setOptions (ctx : Context) : Array (Name × Syntax) :=
  ctx.commands.foldl (init := #[]) fun acc c =>
    (nodesOfKind ``Command.set_option c ++ nodesOfKind ``Term.set_option c ++
      nodesOfKind ``Tactic.set_option c).foldl (fun acc s => acc.push (s[1].getId, s)) acc

/-- Options that switch off or weaken a check: backward-compatibility switches (`backward.*`),
skipping the kernel type checker, and the trust level. -/
private def isWeakeningOption (n : Name) : Bool :=
  (`backward).isPrefixOf n || n == `debug.skipKernelTC || n == `trust

/-- Metric `set_options`: `set_option` uses: heartbeat and recursion limits, disabled linters,
options that weaken checks, and distinct options. -/
def setOptions : Metric where
  name := "set_options"
  description := "`set_option` uses: heartbeat and recursion limits, disabled linters, options \
    that weaken checks, and distinct options"
  needsSource := true
  run ctx := do
    let opts := ctx.setOptions
    let count (p : Name × Syntax → Bool) := toJson (opts.filter p).size
    let isFalse (s : Syntax) := s[3].isAtom && s[3].getAtomVal == "false" || s[3].getId == `false
    let names : NameSet := opts.foldl (·.insert ·.1) {}
    return { columns := #[
      ("n_setopt_total", toJson opts.size), ("n_maxHeartbeats", count (·.1 == `maxHeartbeats)),
      ("n_maxRecDepth", count (·.1 == `maxRecDepth)),
      ("n_linter_disable", count fun (n, s) => (`linter).isPrefixOf n && isFalse s),
      ("n_exotic_options", count (isWeakeningOption ·.1)),
      ("n_setopt_distinct_names", toJson names.size)] }

private def trackedAttributes : List Name :=
  [`simp, `instance, `reducible, `irreducible, `inline, `ext, `deprecated]

/-- Metric `attributes`: Attribute applications, with columns for common attributes. -/
def attributes : Metric where
  name := "attributes"
  description := "attribute applications, with columns for common attributes"
  needsSource := true
  run ctx := do
    let applied := ctx.commands.foldl (· ++ attributesUnder ·) #[]
    let count (n : Name) := (applied.filter (· == n)).size
    let tracked := trackedAttributes.foldl (· + count ·) 0
    return { columns := #[
      ("n_attributes", toJson applied.size),
      ("n_attributes_other", toJson (applied.size - tracked)),
      ("n_attribute_commands",
        toJson (ctx.commands.foldl (· + countKind ``Command.attribute ·) 0))] ++
      (trackedAttributes.map fun n => (s!"attr_{n}", toJson (count n))).toArray }

/-- Whether an `open` command names a namespace under `Lean` or `Qq`. -/
private def opensMetaNamespace (s : Syntax) : Bool :=
  (identsOf s).any fun n => (`Lean).isPrefixOf n || (`Qq).isPrefixOf n

/-- Metric `metaprogramming`: Macros, elaborators, syntax declarations, `#eval`/`run_cmd`, and
`open`s of Lean's namespaces. -/
def metaprogramming : Metric where
  name := "metaprogramming"
  description := "macros, elaborators, syntax declarations, `#eval`/`run_cmd`, and `open`s of \
    Lean's namespaces"
  needsSource := true
  run ctx := do
    let sum (k : SyntaxNodeKind) := ctx.commands.foldl (· + countKind k ·) 0
    let opens := ctx.commands.foldl (· ++ nodesOfKind ``Command.open ·) #[]
    let counts := #[
      ("n_macro", sum ``Command.macro), ("n_macro_rules", sum ``Command.macro_rules),
      ("n_elab", sum ``Command.elab), ("n_elab_rules", sum ``Command.elab_rules),
      ("n_syntax", sum ``Command.syntax), ("n_declare_syntax_cat", sum ``Command.syntaxCat),
      ("n_run_cmd", sum ``runCmd), ("n_eval", sum ``Command.eval),
      ("n_open_meta", (opens.filter opensMetaNamespace).size)]
    return { columns := counts.map (fun (k, n) => (k, toJson n)) ++
      #[("uses_metaprogramming", toJson (if counts.any (·.2 > 0) then 1 else 0))] }

end LeanMetrics
