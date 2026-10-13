import Lean

/-! The `lemma` command, declared exactly as Mathlib declares it. -/

open Lean

syntax (name := lemma) declModifiers group("lemma " declId ppIndent(declSig) declVal) : command

@[macro «lemma»] def expandLemma : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration
