/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang
-/
module

public import LeanMetrics.Basic
import LeanMetrics.Stats
import Lean.DocString

/-! # Documentation and naming

Docstrings on authored declarations, and placeholder names.
-/

public section

open Lean

namespace LeanMetrics

/-- Metric `docstrings`: Declarations with a docstring, and their share. -/
def docstrings : Metric where
  name := "docstrings"
  description := "declarations with a docstring, and their share"
  needsSource := false
  run ctx := do
    let decls := ctx.authored
    let mut documented := 0
    for d in decls do
      if (← findDocString? ctx.env d).isSome then documented := documented + 1
    return { columns := #[("n_doc_decls", toJson decls.size),
      ("n_doc_documented", toJson documented),
      ("doc_coverage", ratio documented decls.size)] }

/-- Name stems counted as placeholders. -/
def placeholderStems : List String :=
  ["aux", "tmp", "temp", "lemma", "lem", "thm", "claim", "step", "goal", "foo", "bar", "baz",
    "hyp", "h"]

/-- Whether the last component of a name is a placeholder: a letter followed only by digits or
primes (`h`, `x2`), up to two letters and a number (`hx1`), or a placeholder stem with an optional
number (`aux`, `lem_3`). Subscript digits count as digits. -/
private def isOpaqueName (n : Name) : Bool :=
  let last := match (privateToUserName? n).getD n with
    | .str _ s => s
    | _ => ""
  let s := last.map fun c =>
    if '₀' ≤ c && c ≤ '₉' then Char.ofNat (c.toNat - '₀'.toNat + '0'.toNat) else c
  let cs := s.toList
  let letters := cs.takeWhile Char.isAlpha
  let rest := cs.drop letters.length
  let digits := rest.takeWhile Char.isDigit
  let tail := rest.drop digits.length
  let singleLetter := letters.length == 1 && rest.all fun c => c.isDigit || c == '\''
  let shortNumbered := letters.length ∈ [1, 2] && !digits.isEmpty && (tail == [] || tail == ['\''])
  let stem := placeholderStems.any fun p =>
    s == p || (s.startsWith p && (let r := (s.drop p.length).toString
      let r := if r.startsWith "_" || r.startsWith "'" then (r.drop 1).toString else r
      !r.isEmpty && r.all Char.isDigit))
  !s.isEmpty && (singleLetter || shortNumbered || stem)

/-- Metric `name_opacity`: Declarations with placeholder names, and their share. -/
def nameOpacity : Metric where
  name := "name_opacity"
  description := "declarations with placeholder names, and their share"
  needsSource := false
  run ctx := do
    let decls := ctx.authored
    let nOpaque := (decls.filter isOpaqueName).size
    return { columns := #[("n_no_named", toJson decls.size), ("n_no_opaque", toJson nOpaque),
      ("no_opaque_ratio", ratio nOpaque decls.size)] }

end LeanMetrics
