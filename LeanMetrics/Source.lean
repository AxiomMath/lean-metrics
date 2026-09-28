/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic
public import Lean.Elab.Frontend
import LeanMetrics.Syntax
import Lean.Parser.Syntax

/-! # Parsing a project's source files

Each file is parsed with Lean's parser. Commands that change parsing or scoping are elaborated
as the file is read.
-/

public section

open Lean Elab Command Parser System

namespace LeanMetrics

/-- Commands that open or close a scope, or change which names and syntax are in scope. -/
def scopingCommandKinds : List SyntaxNodeKind :=
  [``Command.namespace, ``Command.section, ``Command.end, ``Command.open, ``Command.set_option]

/-- Whether elaborating `cmd` can change parsing of the rest of the file.
A scoping or `local` command can. Elaborating a declaration again would declare it twice. -/
partial def affectsParsing (cmd : Syntax) : Bool :=
  let k := cmd.getKind
  if k == ``Command.in then affectsParsing cmd[0] && affectsParsing cmd[2]
  else if k == ``Command.declaration || k == ``Command.mutual || isLemmaCommand cmd then false
  -- `local` syntax can come from a library's own commands, such as Mathlib's `notation3`
  else scopingCommandKinds.contains k || (findKind? ``Term.local cmd).isSome

/-- The first alternative of each `choice` node. Several parsers can accept the same text. -/
partial def collapseChoices (s : Syntax) : Syntax :=
  match s with
  | .node info k args =>
    if k == choiceKind then
      match args[0]? with
      | some a => collapseChoices a
      | none => s
    else .node info k (args.map collapseChoices)
  | _ => s

/-- The kinds of syntax category `cat` in `env`. -/
def categoryKinds (env : Environment) (cat : Name) : SyntaxNodeKindSet :=
  ((parserExtension.getState env).categories.find? cat).map (·.kinds) |>.getD {}

/-- For every module of `env`, the set (as bits of a natural number) of modules it imports
directly or indirectly, itself included. Module indices are in import order. -/
def importClosures (env : Environment) : Array Nat := Id.run do
  let mods := env.header.moduleData
  let mut closure : Array Nat := Array.replicate mods.size 0
  for h : i in [0:mods.size] do
    let mut s : Nat := 1 <<< i
    for imp in mods[i].imports do
      if let some j := env.getModuleIdx? imp.module then s := s ||| closure[j.toNat]!
    closure := closure.set! i s
  return closure

/-- `env` with `ext`'s state as if `env` imported only the modules in `closure` (module indices,
as bits). -/
def narrowExtension [Inhabited σ] (env : Environment) (closure : Nat)
    (ext : PersistentEnvExtension α β σ) : IO Environment := do
  let entries := (Array.range env.header.moduleData.size).map fun i =>
    if closure.testBit i then ext.getModuleEntries env i else #[]
  return ext.setState env (← (ext.addImportedFn entries).run { env, opts := {} })

/-- An environment extension as Lean registers it, with its types erased. -/
abbrev RegisteredExtension := PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry
  EnvExtensionState

/-- The registered extension `Lean.namespacesExt`. Lean keeps the name private. -/
def namespacesExtension : IO RegisteredExtension := do
  let some ext := (← persistentEnvExtensionsRef.get).find? fun e =>
      privateToUserName? e.name == some `Lean.namespacesExt
    | throw <| .userError "Lean's namespace extension `Lean.namespacesExt` is not registered; \
        lean-metrics does not support this Lean version"
  return ext

/-- `env` with the tokens, parsers, syntax categories and namespaces of the modules in `closure`
(module indices, as bits). Other extensions are kept. `namespaces` is `namespacesExtension`. -/
def withSyntaxOf (env : Environment) (namespaces : RegisteredExtension) (closure : Nat) :
    IO Environment := do
  let env ← narrowExtension env closure parserExtension.ext
  narrowExtension env closure namespaces

/-- `env` with the namespaces Lean registers when it adds declaration `name`: each proper prefix of
the name as written, unless its last component marks it internal. -/
def registerNamePrefixes (env : Environment) (name : Name) : Environment :=
  match privateToUserName name with
  | n@(.str _ s) => if s.front == '_' then env else go env n
  | _ => env
where
  go (env : Environment) : Name → Environment
    | .str p _ => if isNamespaceName p then go (env.registerNamespace p) p else env
    | _ => env
  isNamespaceName : Name → Bool
    | .str .anonymous _ => true
    | .str p _ => isNamespaceName p
    | _ => false

/-- `env` with the namespaces the declarations of `cmd` register when added in namespace `ns`.
A structure or inductive type also opens its own, which its constructors are declared in. -/
def registerDeclaredNamespaces (env : Environment) (ns : Name) (cmd : Syntax) : Environment :=
  (declarationsOf cmd).foldl (init := env) fun env decl =>
    let n := declaredName decl
    if n.isAnonymous then env else
    let full := if n.getRoot == `_root_ then n.replacePrefix `_root_ .anonymous else ns ++ n
    let isType := decl.isOfKind ``Command.structure || decl.isOfKind ``Command.inductive ||
      decl.isOfKind ``Command.classInductive
    registerNamePrefixes env (if isType then full ++ `mk else full)

/-- The syntax module `idx` of `env` declares, as the parser extension's entries, each with the
position in the module's source from which it is in effect: that of the parser or category
declaration adding it, or, for a token or node kind, that of the next such declaration, which
uses it. An entry whose declaration has no position in this module, such as an imported parser
given a parser attribute here, keeps the position of the entry before it. -/
def declaredSyntax (env : Environment) (idx : Nat) :
    Array (Position × ScopedEnvExtension.Entry ParserExtension.OLeanEntry) := Id.run do
  let entries := parserExtension.ext.getModuleEntries env idx
  let mut pos : Position := ⟨0, 0⟩
  let mut out := #[]
  for e in entries.reverse do
    let val := match e with | .global a | .scoped _ a => a
    match val with
    | .parser _ d _ | .category _ d _ =>
      pos := if env.getModuleIdxFor? d != some idx then ⟨0, 0⟩ else
        ((declRangeExt.find? env d).map (·.range.pos)).getD ⟨0, 0⟩
    | _ => pure ()
    out := out.push (pos, e)
  return out.reverse

/-- `env` with one parser-extension entry added. A scoped entry also registers its namespace,
which the `namespace` command around its declaration registered. -/
def addSyntax (env : Environment) (entry : ScopedEnvExtension.Entry ParserExtension.OLeanEntry) :
    IO Environment := do
  let ext := parserExtension
  let (env, entry) ← match entry with
    | .global a =>
      pure (env, .global (← (ext.descr.ofOLeanEntry (ext.getState env) a).run { env, opts := {} }))
    | .scoped ns a =>
      let b ← (ext.descr.ofOLeanEntry (ext.getState env) a).run { env, opts := {} }
      pure (env.registerNamespace ns, .scoped ns b)
  return ext.ext.modifyState env (ScopedEnvExtension.addEntryFn ext.descr · entry)

/-- The first node kind under `s`, in any `choice` alternative, that `isForeign` rejects. -/
private partial def firstForeign (isForeign : SyntaxNodeKind → Bool) (s : Syntax) :
    Option SyntaxNodeKind :=
  match s with
  | .node _ k args => if isForeign k then some k else args.findSome? (firstForeign isForeign)
  | _ => none

/-- The result of parsing a file's commands. -/
structure Parsed where
  commands : Array Syntax
  messages : MessageLog
  /-- The end-of-input token, which carries the whitespace and comments after the last command. -/
  eoi : Syntax
  /-- Tactic kinds declared by `local` syntax in the file, absent from the environment it was
  parsed against. -/
  localTacticKinds : NameSet
  /-- A syntax kind the parse used that the file could not have seen: from a module it does not
  import, or its own above where it is declared. -/
  foreignKind? : Option SyntaxNodeKind

/-- Parse the commands after the header against `env`, elaborating those that `affectsParsing`.
`isForeign k pos` says whether the file cannot have used syntax kind `k` in a command at `pos`.
Each of `pending` (see `declaredSyntax`) is added to the environment before the first command
that starts after its position, and when `registerNamespaces` holds, each declaration registers
the namespaces its name opens as it is read. -/
def parseCommands (env : Environment) (inputCtx : InputContext)
    (parserState : ModuleParserState)
    (isForeign : SyntaxNodeKind → String.Pos.Raw → Bool := fun _ _ => false)
    (pending : Array (Position × ScopedEnvExtension.Entry ParserExtension.OLeanEntry) := #[])
    (registerNamespaces := false) :
    IO Parsed := do
  let baseTactics := categoryKinds env `tactic
  let mut cmdState := Command.mkState env {} {}
  let mut pstate := parserState
  let mut cmds : Array Syntax := #[]
  let mut localTactics : NameSet := {}
  let mut foreign? : Option SyntaxNodeKind := none
  let mut eoi := Syntax.missing
  let mut next := 0
  repeat
    let here := inputCtx.fileMap.toPosition pstate.pos
    while h : next < pending.size do
      let (p, entry) := pending[next]
      unless p.line < here.line || p.line == here.line && p.column < here.column do break
      cmdState := { cmdState with env := ← addSyntax cmdState.env entry }
      next := next + 1
    let scope := cmdState.scopes.head!
    let pmctx : ParserModuleContext :=
      { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let (cmd, ps, msgs) := parseCommand inputCtx pmctx pstate cmdState.messages
    pstate := ps
    cmdState := { cmdState with messages := msgs }
    if isTerminalCommand cmd then eoi := cmd; break
    if foreign?.isNone then foreign? := firstForeign (isForeign · (cmd.getPos?.getD 0)) cmd
    cmds := cmds.push (collapseChoices cmd)
    if registerNamespaces then
      cmdState := { cmdState with
        env := registerDeclaredNamespaces cmdState.env scope.currNamespace cmd }
    if affectsParsing cmd then
      let cmdCtx : Command.Context :=
        { fileName := inputCtx.fileName, fileMap := inputCtx.fileMap,
          snap? := none, cancelTk? := none }
      match ← EIO.toIO' ((elabCommandTopLevel cmd) cmdCtx |>.run cmdState) with
      | .ok (_, s) =>
        cmdState := s
        -- a `local` command, possibly inside a wrapper such as `… in`, may declare tactic syntax
        if (findKind? ``Term.local cmd).isSome then
          for (k, _) in categoryKinds cmdState.env `tactic do
            unless baseTactics.contains k do localTactics := localTactics.insert k
      | .error e =>
        cmdState := { cmdState with
          messages := cmdState.messages.add
            { fileName := inputCtx.fileName,
              pos := inputCtx.fileMap.toPosition (cmd.getPos?.getD 0),
              data := e.toMessageData } }
  return { commands := cmds, messages := cmdState.messages, eoi, localTacticKinds := localTactics,
           foreignKind? := foreign? }

/-- Parse the file at `path`. `closure` is the modules it imports, as bits (see `importClosures`).

Parsed against `env`. On errors, or on syntax from outside the file's imports or from above its
own declaration, parsed again against only those imports. -/
def parseFile (env : Environment) (namespaces : RegisteredExtension) (idx closure : Nat)
    (module : Name) (root path : FilePath) : IO (SourceFile × MessageLog) := do
  -- the parser normalizes line endings, and syntax positions refer to the normalized text
  let inputCtx := mkInputContext (← IO.FS.readFile (root / path)) path.toString
  let text := inputCtx.fileMap.source
  let (header, parserState, _) ← parseHeader inputCtx
  -- Lean's own syntax is always available; anything else must come from the file's imports
  -- and the file's own syntax only below the point where the file declares it
  let isForeign (k : SyntaxNodeKind) (pos : String.Pos.Raw) : Bool :=
    match env.getModuleIdxFor? k with
    | some j =>
      if j.toNat == idx then
        (declRangeExt.find? env k).any fun r =>
          let p := inputCtx.fileMap.toPosition pos
          r.range.pos.line > p.line || r.range.pos.line == p.line && r.range.pos.column > p.column
      else
        let r := env.header.modules[j.toNat]!.module.getRoot
        !closure.testBit j.toNat && r != `Init && r != `Lean && r != `Std && r != `Lake
    | none => false
  let p ← parseCommands env inputCtx parserState isForeign
  let suspect := p.commands.any (·.hasMissing) || p.foreignKind?.isSome
  let mk (p : Parsed) (reparsed : Bool) : SourceFile :=
    { module, path, text, fileMap := inputCtx.fileMap, header, commands := p.commands, eoi := p.eoi,
      localTacticKinds := p.localTacticKinds, reparsed }
  if !suspect then return (mk p false, p.messages)
  -- the file's own syntax and namespaces come into effect where the file declares them
  let fileEnv ← withSyntaxOf env namespaces (closure ^^^ (1 <<< idx))
  let q ← parseCommands fileEnv inputCtx parserState
    (pending := declaredSyntax env idx) (registerNamespaces := true)
  return (mk q true, q.messages)

end LeanMetrics
