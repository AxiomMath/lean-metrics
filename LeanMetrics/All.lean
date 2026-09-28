/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang
-/
module

public import LeanMetrics.Metrics.Commands
public import LeanMetrics.Metrics.Declarations
public import LeanMetrics.Metrics.Docs
public import LeanMetrics.Metrics.Graph
public import LeanMetrics.Metrics.Imports
public import LeanMetrics.Metrics.Namespaces
public import LeanMetrics.Metrics.Tactics
public import LeanMetrics.Metrics.Text
public import LeanMetrics.Metrics.Warnings

/-! # The metrics `lean-metrics` runs, in output order -/

public section

namespace LeanMetrics

/-- Every metric, in the order they appear in the output. -/
def allMetrics : Array Metric := #[
  loc, files, comments, sourceShape,
  declarations, implicitArgs, proofMode, reducibility, recursionStyle,
  tactics, decideUsage, sorryAxiom, proofSize, proofStructure, proofLength,
  setOptions, attributes, metaprogramming, namespaces,
  imports, importDiscipline, importMinimizability,
  depGraph, docstrings, nameOpacity, warnings]

end LeanMetrics
