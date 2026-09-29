/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic
public import Lean.Parser.Command
public import Lean.Parser.Term

/-! # Walking source syntax

Helpers over the commands of a source file. Syntax quotations are skipped.
-/

public section

open Lean Parser

namespace LeanMetrics

/-- Whether `cmd` is a `lemma` command. Core Lean has no `lemma` kind; recognised by shape
(modifiers, then a group whose first atom is `lemma`). -/
def isLemmaCommand (cmd : Syntax) : Bool :=
  cmd.getNumArgs == 2 && cmd[0].isOfKind ``Command.declModifiers && cmd[1].isOfKind groupKind &&
    cmd[1][0].isAtom && cmd[1][0].getAtomVal == "lemma"

/-- Syntax quotation kinds. Their contents build syntax. -/
def quotationKinds : List SyntaxNodeKind :=
  [``Term.quot, ``Term.dynamicQuot, ``Term.precheckedQuot, ``Tactic.quot, ``Tactic.quotSeq,
   ``Command.quot]

/-- Whether `k` is a syntax quotation kind. -/
def isQuotationKind (k : SyntaxNodeKind) : Bool := quotationKinds.contains k

/-- Fold over every node under `s` (itself included), not entering syntax quotations. -/
partial def foldNodes (f : α → Syntax → α) (init : α) (s : Syntax) : α :=
  match s with
  | .node _ k args =>
    if isQuotationKind k then init
    else args.foldl (foldNodes f) (f init s)
  | _ => init

/-- Number of nodes of kind `k` under `s`, outside syntax quotations. -/
def countKind (k : SyntaxNodeKind) (s : Syntax) : Nat :=
  foldNodes (fun n t => if t.isOfKind k then n + 1 else n) 0 s

/-- Nodes of kind `k` under `s`, outside syntax quotations, in source order. -/
def nodesOfKind (k : SyntaxNodeKind) (s : Syntax) : Array Syntax :=
  foldNodes (fun acc t => if t.isOfKind k then acc.push t else acc) #[] s

/-- The first node of kind `k` under `s`, outside syntax quotations. -/
partial def findKind? (k : SyntaxNodeKind) (s : Syntax) : Option Syntax :=
  match s with
  | .node _ kind args =>
    if kind == k then some s
    else if isQuotationKind kind then none
    else args.findSome? (findKind? k)
  | _ => none

/-- Identifiers under `s`, in source order. -/
partial def identsOf (s : Syntax) : Array Name :=
  match s with
  | .ident _ _ v _ => #[v]
  | _ => s.getArgs.foldl (fun acc a => acc ++ identsOf a) #[]

/-- The first atom of `s`: the keyword a command or tactic is written with. -/
partial def leadingAtom? (s : Syntax) : Option String :=
  match s with
  | .atom _ v => some v
  | _ => s.getArgs.findSome? leadingAtom?

/-- The declarations a top-level command introduces, each as the node holding its keyword,
name, signature and body: the command itself, the members of a `mutual` block, and the
declaration a `… in` wrapper wraps. -/
partial def declarationsOf (cmd : Syntax) : Array Syntax :=
  let k := cmd.getKind
  if k == ``Command.in then declarationsOf cmd[2]
  else if k == ``Command.declaration || isLemmaCommand cmd then #[cmd[1]]
  else if k == ``Command.mutual then cmd[1].getArgs.foldl (fun acc c => acc ++ declarationsOf c) #[]
  else #[]

/-- The modifiers (`@[…]`, `private`, `noncomputable`, docstring) of a declaration command. -/
def modifiersOf? (cmd : Syntax) : Option Syntax :=
  if cmd.isOfKind ``Command.declaration || isLemmaCommand cmd then some cmd[0] else none

/-- Whether a declaration node is a theorem: `theorem` or a `lemma` group. -/
def isTheorem (decl : Syntax) : Bool :=
  decl.isOfKind ``Command.theorem ||
    decl.isOfKind groupKind && decl[0].isAtom && decl[0].getAtomVal == "lemma"

/-- The signature of a declaration node (`declSig` or `optDeclSig`). -/
def signatureOf? (decl : Syntax) : Option Syntax :=
  decl.getArgs.find? fun a => a.isOfKind ``Command.declSig || a.isOfKind ``Command.optDeclSig

/-- The `declId` of a declaration node: a direct child, or under the optional node an `instance`
wraps it in. -/
def declIdOf? (decl : Syntax) : Option Syntax :=
  decl.getArgs.findSome? fun a =>
    if a.isOfKind ``Command.declId then some a
    else if a.isOfKind nullKind then a.getArgs.find? (·.isOfKind ``Command.declId)
    else none

/-- The declared name, as written, of a declaration node (anonymous for `example` and
unnamed `instance`s). -/
def declaredName (decl : Syntax) : Name :=
  match declIdOf? decl with
  | some declId => declId[0].getId
  | none => .anonymous

/-- The body a declaration is defined by: the term after `:=`, or the alternatives of a
pattern-matching definition. `termination_by`, `decreasing_by` and `where` clauses are left
out. -/
def bodyOf? (decl : Syntax) : Option Syntax :=
  match decl.getArgs.find? (·.isOfKind ``Command.declValSimple) with
  | some v => some v[1]
  | none =>
    match decl.getArgs.find? (·.isOfKind ``Command.declValEqns) with
    | some e => some e[0][0]
    | none => none

/-- Remove wrappers that do not change a proof's tactic/term mode. Keep the original syntax
for source size and `by` depth: treating a wrapper as a `by` node would count it twice. -/
partial def unwrapProof (body : Syntax) : Syntax :=
  if body.isOfKind ``Term.paren || body.isOfKind ``Term.typeAscription then unwrapProof body[1]
  else if body.isOfKind ``Term.set_option then unwrapProof body[5]
  else if body.isOfKind ``Term.open then unwrapProof body[3]
  else body

/-- Whether this syntax node itself is a tactic block. -/
def isTacticBody (body : Syntax) : Bool :=
  body.isOfKind ``Term.byTactic || body.isOfKind ``Term.byTactic'

/-- Theorem bodies of the project, in source order. -/
def Context.proofs (ctx : Context) : Array Syntax :=
  ctx.declarations.filter isTheorem |>.filterMap bodyOf?

/-- The name of the attribute an `attrInstance` applies, as written (`simp`, `instance`,
`to_additive`). -/
def attributeName (inst : Syntax) : Name :=
  let attr := inst[1]
  if attr.isOfKind ``Attr.simple then attr[0].getId
  else ((leadingAtom? attr).map Name.mkSimple).getD attr.getKind

/-- Every attribute applied under `s`, by `@[…]` or `attribute […]`. -/
def attributesUnder (s : Syntax) : Array Name :=
  (nodesOfKind ``Term.attrInstance s).map attributeName

end LeanMetrics
