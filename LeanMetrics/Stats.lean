/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang
-/
module

public import Lean.Data.Json

/-! # Summary statistics

Means, medians and percentiles, as JSON decimals.
-/

public section

open Lean

namespace LeanMetrics

/-- `x` rounded to `digits` decimal places, as an exact JSON decimal. -/
def decimal (x : Float) (digits : Nat := 3) : Json :=
  let scaled := (x.abs * (10 ^ digits).toFloat).round.toUInt64.toNat
  .num ⟨if x < 0 then -(scaled : Int) else scaled, digits⟩

/-- `num / den` rounded, or `0` when `den` is zero. -/
def ratio (num den : Nat) (digits : Nat := 3) : Json :=
  if den == 0 then toJson (0 : Nat) else decimal (num.toFloat / den.toFloat) digits

/-- The mean, rounded to `digits` places. -/
def mean (xs : Array Nat) (digits : Nat := 1) : Json :=
  ratio (xs.foldl (· + ·) 0) xs.size digits

/-- The median; the mean of the two middle values when the sample size is even. -/
def median (xs : Array Nat) : Json :=
  let s := xs.qsort (· < ·)
  if s.isEmpty then toJson (0 : Nat)
  else if s.size % 2 == 1 then toJson s[s.size / 2]!
  else decimal ((s[s.size / 2 - 1]! + s[s.size / 2]!).toFloat / 2) 1

/-- The largest value, or `0` for an empty sample. -/
def maximum (xs : Array Nat) : Nat := xs.foldl max 0

/-- The `p`-th percentile, by linear interpolation between order statistics at rank
`1 + p(n-1)/100`. -/
def percentile (xs : Array Nat) (p : Nat) : Json :=
  let s := xs.qsort (· < ·)
  if s.isEmpty then toJson (0 : Nat)
  else
    let h := p * (s.size - 1)
    let lo := h / 100
    let frac := (h % 100).toFloat / 100
    let v := s[lo]!.toFloat + frac * ((s[min (lo + 1) (s.size - 1)]!).toFloat - s[lo]!.toFloat)
    if h % 100 == 0 then toJson s[lo]! else decimal v 2

/-- The value at the nearest rank `⌈p·n/100⌉` of a sorted sample. -/
def nearestRankSorted (s : Array Nat) (p : Nat) : Nat :=
  if s.isEmpty then 0 else s[min (s.size - 1) ((p * s.size + 99) / 100 - 1)]!

/-- The value at the nearest rank `⌈p·n/100⌉`. -/
def nearestRank (xs : Array Nat) (p : Nat) : Nat := nearestRankSorted (xs.qsort (· < ·)) p

/-- Size, nearest-rank p50/p90/p99, maximum and sum of a sample. -/
def distribution (xs : Array Nat) : Json :=
  let s := xs.qsort (· < ·)
  Json.mkObj [("n", toJson xs.size), ("p50", toJson (nearestRankSorted s 50)),
    ("p90", toJson (nearestRankSorted s 90)), ("p99", toJson (nearestRankSorted s 99)),
    ("max", toJson (maximum xs)), ("sum", toJson (xs.foldl (· + ·) 0))]

end LeanMetrics
