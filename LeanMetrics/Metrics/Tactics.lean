/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic
import LeanMetrics.Stats
import LeanMetrics.Syntax
import LeanMetrics.Metrics.Declarations
import Lean.Parser.Tactic

/-! # Tactics and proofs

Tactic calls, `sorry` and axioms, and proof size.
A call is a syntax node whose kind is in the `tactic` category.
-/

public section

open Lean Parser

namespace LeanMetrics

/-- Tactic kinds that only group or sequence other tactics. -/
private def groupingKinds : List SyntaxNodeKind :=
  [``Tactic.paren, ``Tactic.nestedTactic, ``cdot]

/-- The kinds of Lean's `tactic` syntax category in `env`. -/
def tacticKinds (env : Environment) : SyntaxNodeKindSet :=
  match (parserExtension.getState env).categories.find? `tactic with
  | some cat => cat.kinds
  | none => {}

/-- The keyword a tactic node is written with (`rw`, `norm_num`, `<;>`): its first atom that is
a direct child, or the last component of its kind when it has none. -/
def tacticKeyword (s : Syntax) : String :=
  match s.getArgs.findSome? fun a => if a.isAtom then some a.getAtomVal else none with
  | some v => v
  | none => match s.getKind with
    | .str _ k => k
    | k => k.toString

/-- The keywords of the tactic calls under `s`, in source order. -/
def tacticCalls (isTactic : SyntaxNodeKind → Bool) (s : Syntax) : Array String :=
  foldNodes (init := #[]) (s := s) fun acc t =>
    if isTactic t.getKind && !groupingKinds.contains t.getKind then acc.push (tacticKeyword t)
    else acc

/-- Tactic kinds in `file`: those of the project's environment and those its `local` syntax
declares. -/
def isTacticIn (kinds : SyntaxNodeKindSet) (file : SourceFile) (k : SyntaxNodeKind) : Bool :=
  kinds.contains k || file.localTacticKinds.contains k

/-- The options a tactic node's configuration leaves on, reading its items in order: `+opt` and
`(opt := true)` turn an option on, `-opt` and any other value turn it off. -/
private def configOptions (tac : Syntax) : Array Name :=
  match findKind? ``Tactic.optConfig tac with
  | some cfg =>
    let settings : NameMap Bool := foldNodes (init := {}) (s := cfg) fun m item =>
      if item.isOfKind ``Tactic.posConfigItem then m.insert item[1].getId true
      else if item.isOfKind ``Tactic.negConfigItem then m.insert item[1].getId false
      else if item.isOfKind ``Tactic.valConfigItem then
        m.insert item[1].getId (item[3].isIdent && item[3].getId == `true)
      else m
    settings.foldl (fun acc n on => if on then acc.push n else acc) #[]
  | none => #[]

/-- Tactics counted in `frac_by_automation`. -/
def automationTactics : List String :=
  ["aesop", "decide", "gcongr", "grind", "linarith", "native_decide", "nlinarith", "norm_num",
   "omega", "positivity", "ring", "simp"]

/-- Tactics with their own `tactic_<name>` column: the list below, then any automation tactic
not already in it. -/
def columnTactics : List String :=
  let common := ["apply", "calc", "change", "dsimp", "exact", "have", "intro", "let", "letI",
    "linarith", "norm_num", "obtain", "omega", "rcases", "refine", "rfl", "ring", "rw", "simp",
    "simpa"]
  common ++ automationTactics.filter (!common.contains ·)

/-- Metric `tactics`: Tactic calls by keyword, distinct tactics, the share made by automation,
`unfold`, `omit` and `set_option`. -/
def tactics : Metric where
  name := "tactics"
  description := "tactic calls by keyword, distinct tactics, the share made by automation, \
    `unfold`, `omit` and `set_option`"
  needsSource := true
  run ctx := do
    let kinds := tacticKinds ctx.env
    let calls := ctx.files.foldl (init := #[]) fun acc f =>
      f.commands.foldl (· ++ tacticCalls (isTacticIn kinds f) ·) acc
    let hist : Std.HashMap String Nat := calls.foldl (fun m k => m.insert k (m.getD k 0 + 1)) {}
    let count (k : String) := hist.getD k 0
    let nAutomation := automationTactics.foldl (· + count ·) 0
    let cmds := ctx.commands
    let sum (k : SyntaxNodeKind) := cmds.foldl (· + countKind k ·) 0
    let sorted := hist.toArray.qsort fun a b => a.2 > b.2 || a.2 == b.2 && a.1 < b.1
    return {
      columns := #[
        ("n_tactic_calls", toJson calls.size), ("n_distinct_tactics", toJson hist.size),
        ("frac_by_automation", ratio nAutomation calls.size 6),
        ("n_unfold", toJson (count "unfold")),
        ("n_omit", toJson (sum ``Command.omit)),
        ("n_set_option", toJson (sum ``Command.set_option + sum ``Term.set_option +
          sum ``Tactic.set_option))] ++
        (columnTactics.map fun k => (s!"tactic_{k}", toJson (count k))).toArray
      details := Json.mkObj [("histogram", Json.arr (sorted.map fun (k, n) =>
        Json.mkObj [("tactic", k), ("calls", toJson n)]))] }

/-- Metric `decide_usage`: `decide` by configuration, `native_decide`, `simp +arith` and `rfl`. -/
def decideUsage : Metric where
  name := "decide_usage"
  description := "`decide` by configuration, `native_decide`, `simp +arith` and `rfl`"
  needsSource := true
  run ctx := do
    let cmds := ctx.commands
    let decides := cmds.foldl (· ++ nodesOfKind ``Tactic.decide ·) #[]
    let nKernel := (decides.filter fun d => (configOptions d).contains `kernel).size
    let nNative := (decides.filter fun d => (configOptions d).contains `native).size
    let simps := cmds.foldl (fun acc c => acc ++ nodesOfKind ``Tactic.simp c ++
      nodesOfKind ``Tactic.simpAll c ++ nodesOfKind ``Tactic.simpa c ++
      nodesOfKind ``Tactic.dsimp c) #[]
    let termRfl := ctx.declarations.filter fun d =>
      (bodyOf? d).any fun b => let b := unwrapProof b; b.isIdent && b.getId == `rfl
    let nNativeDecide := cmds.foldl (· + countKind ``Tactic.nativeDecide ·) 0
    return { columns := #[
      ("n_dec_decide", toJson (decides.size - nKernel - nNative)), ("n_dec_kernel", toJson nKernel),
      ("n_dec_native", toJson nNative), ("n_dec_native_decide", toJson nNativeDecide),
      ("n_dec_simp_arith", toJson (simps.filter fun s => (configOptions s).contains `arith).size),
      ("n_dec_rfl", toJson (cmds.foldl (· + countKind ``Tactic.tacticRfl ·) 0 + termRfl.size)),
      ("dec_uses_native_decide", toJson (decide (nNativeDecide > 0)))] }

/-- Metric `sorry_axiom`: `sorry`, `admit`, `axiom` declarations and `native_decide`. -/
def sorryAxiom : Metric where
  name := "sorry_axiom"
  description := "`sorry`, `admit`, `axiom` declarations and `native_decide`"
  needsSource := true
  run ctx := do
    let sum (k : SyntaxNodeKind) := ctx.commands.foldl (· + countKind k ·) 0
    return { columns := #[
      ("n_sorry", toJson (sum ``Tactic.tacticSorry + sum ``Term.sorry)),
      ("n_admit", toJson (sum ``Tactic.tacticAdmit)),
      ("n_sorryax_axiom", toJson (ctx.declarations.filter (·.isOfKind ``Command.axiom)).size),
      ("n_sorryax_native_decide", toJson (sum ``Tactic.nativeDecide))] }

/-- Number of syntax nodes under `s`. -/
private def nodeCount (s : Syntax) : Nat := foldNodes (fun n _ => n + 1) 0 s

/-- Deepest nesting of `by` blocks under `s`. -/
private partial def byDepth (s : Syntax) : Nat :=
  if isQuotationKind s.getKind then 0
  else
    let here := if isTacticBody s then 1 else 0
    here + s.getArgs.foldl (fun d a => max d (byDepth a)) 0

/-- Metric `proof_size`: Size of each theorem's proof in tactic calls, syntax nodes, `have`s and
`by` nesting. -/
def proofSize : Metric where
  name := "proof_size"
  description := "size of each theorem's proof in tactic calls, syntax nodes, `have`s and \
    `by` nesting"
  needsSource := true
  run ctx := do
    let kinds := tacticKinds ctx.env
    -- theorem bodies with the tactics of the file each is in
    let bodies := ctx.files.foldl (init := #[]) fun acc f =>
      (f.commands.foldl (· ++ declarationsOf ·) #[]).foldl (init := acc) fun acc d =>
        match isTheorem d, bodyOf? d with
        | true, some b => acc.push (b, f)
        | _, _ => acc
    let proofs := bodies.map (·.1)
    let keywords := bodies.map fun (b, f) => tacticCalls (isTacticIn kinds f) b
    let calls := keywords.map (·.size)
    let haves := keywords.map fun ks => (ks.filter (· == "have")).size
    let nodes := proofs.map nodeCount
    let depths := proofs.map byDepth
    let over (k : Nat) := ratio (calls.filter (· > k)).size proofs.size 4
    let longest := calls.qsort (· > ·)
    let inLongest := (longest.extract 0 ((longest.size + 9) / 10)).foldl (· + ·) 0
    let rank (xs : Array Nat) (p : Nat) := toJson (nearestRank xs p)
    return {
      columns := #[
        ("ps_n_theorems", toJson proofs.size),
        ("ps_calls_p50", rank calls 50), ("ps_calls_p90", rank calls 90),
        ("ps_calls_p99", rank calls 99), ("ps_calls_max", toJson (maximum calls)),
        ("ps_nodes_p50", rank nodes 50), ("ps_nodes_p90", rank nodes 90),
        ("ps_nodes_max", toJson (maximum nodes)),
        ("ps_haves_p90", rank haves 90), ("ps_haves_max", toJson (maximum haves)),
        ("ps_by_depth_p90", rank depths 90), ("ps_by_depth_max", toJson (maximum depths)),
        ("ps_frac_over_30_calls", over 30), ("ps_frac_over_100_calls", over 100),
        ("ps_frac_over_200_calls", over 200),
        ("ps_calls_share_longest_decile", ratio inLongest (calls.foldl (· + ·) 0) 4)]
      details := Json.mkObj [("tactic_calls", distribution calls),
        ("syntax_nodes", distribution nodes),
        ("haves", distribution haves), ("by_depth", distribution depths)] }

/-- Keywords counted by `proof_structure`, in tactic and term position. -/
private def structuringKeywords : List (String × List String) :=
  [("have", ["have"]), ("let", ["let"]), ("suffices", ["suffices"]), ("show", ["show"]),
   ("calc", ["calc"]), ("destructuring", ["obtain", "rcases"])]

/-- Occurrences of each keyword token under `s`, outside syntax quotations. -/
private def keywordCounts (s : Syntax) : Std.HashMap String Nat :=
  foldNodes (init := {}) (s := s) fun m t =>
    t.getArgs.foldl (init := m) fun m a =>
      if a.isAtom then m.insert a.getAtomVal (m.getD a.getAtomVal 0 + 1) else m

/-- Metric `proof_structure`: `have`, `let`, `suffices`, `show`, `calc` and destructuring steps in
theorem proofs, in total and per proof. -/
def proofStructure : Metric where
  name := "proof_structure"
  description := "`have`, `let`, `suffices`, `show`, `calc` and destructuring steps in theorem \
    proofs, in total and per proof"
  needsSource := true
  run ctx := do
    let proofs := ctx.proofs
    let counts := proofs.map keywordCounts
    let total (kws : List String) :=
      counts.foldl (fun n m => kws.foldl (fun n k => n + m.getD k 0) n) 0
    let totals := structuringKeywords.map fun (col, kws) => (col, total kws)
    let nSteps := totals.foldl (· + ·.2) 0
    return { columns :=
      (totals.map fun (col, n) => (s!"n_ps_{col}", toJson n)).toArray ++
      #[("n_ps_steps", toJson nSteps), ("ps_steps_per_proof", ratio nSteps proofs.size)] ++
      (totals.map fun (col, n) => (s!"ps_{col}_per_proof", ratio n proofs.size)).toArray }

/-- Non-blank lines of a proof body, not counting a first line holding only `by`. -/
private def proofLines (text : String) (body : Syntax) : Nat :=
  match body.getPos?, body.getTailPos? with
  | some a, some b =>
    let lines := (String.Pos.Raw.extract text a b).splitOn "\n"
    let lines := if lines.head?.any (·.trimAscii.toString == "by") then lines.drop 1 else lines
    lines.foldl (fun n l => if l.trimAscii.isEmpty then n else n + 1) 0
  | _, _ => 0

/-- Metric `proof_length`: Number of theorem proofs and their mean, median and maximum non-blank
lines. -/
def proofLength : Metric where
  name := "proof_length"
  description := "number of theorem proofs and their mean, median and maximum non-blank lines"
  needsSource := true
  run ctx := do
    let proofs := ctx.files.foldl (init := #[]) fun acc f =>
      f.commands.foldl (init := acc) fun acc c =>
        (declarationsOf c).foldl (init := acc) fun acc d =>
          match isTheorem d, bodyOf? d with
          | true, some body => acc.push (declaredName d, proofLines f.text body)
          | _, _ => acc
    let lengths := proofs.map (·.2)
    return {
      columns := #[("n_proofs", toJson lengths.size), ("proof_loc_mean", mean lengths),
        ("proof_loc_median", median lengths), ("proof_loc_max", toJson (maximum lengths))]
      details := Json.arr (proofs.map fun (n, l) =>
        Json.mkObj [("theorem", toString n), ("lines", toJson l)]) }

end LeanMetrics
