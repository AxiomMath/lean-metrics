/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Evan Wang
-/
module

public import LeanMetrics.Basic
import LeanMetrics.Stats
import LeanMetrics.Syntax

/-! # Size, comments and source text

Line counts, comments, and line and name lengths.
Comments are taken from token whitespace, so a `--` in a string is not a comment.
-/

public section

open Lean Parser System

namespace LeanMetrics

/-- The lines of a file; a final newline ends the last line rather than starting another. -/
def lines (s : String) : List String :=
  if s.isEmpty then [] else
  let ls := s.splitOn "\n"
  if s.endsWith "\n" then ls.dropLast else ls

/-- Number of lines of `s` that hold something other than whitespace. -/
def nonblankLines (s : String) : Nat :=
  (s.splitOn "\n").foldl (fun n l => if l.trimAscii.isEmpty then n else n + 1) 0

/-- Metric `loc`: Non-blank lines over all of the project's Lean files. -/
def loc : Metric where
  name := "loc"
  description := "non-blank lines over all of the project's Lean files"
  needsSource := true
  run ctx := return { columns := #[("loc", toJson (ctx.files.foldl (· + nonblankLines ·.text) 0))] }

/-- Metric `files`: Number of Lean files and their mean and median non-blank lines. -/
def files : Metric where
  name := "files"
  description := "number of Lean files and their mean and median non-blank lines"
  needsSource := true
  run ctx := do
    let sizes := ctx.files.map (nonblankLines ·.text)
    return { columns := #[("n_files", toJson sizes.size), ("file_loc_mean", mean sizes),
      ("file_loc_median", median sizes)] }

/-- A comment in the source: its byte range and whether it is a doc comment. -/
private structure Comment where
  start : String.Pos.Raw
  stop : String.Pos.Raw
  isDoc : Bool

/-- The line and block comments in a stretch of whitespace between tokens. -/
private partial def commentsIn (text : String) (start stop : String.Pos.Raw) : Array Comment :=
  go start #[]
where
  go (p : String.Pos.Raw) (acc : Array Comment) : Array Comment :=
    if p ≥ stop then acc
    else if p.get text == '-' && (p.next text).get text == '-' then
      let e := lineEnd p
      go e (acc.push ⟨p, e, false⟩)
    else if p.get text == '/' && (p.next text).get text == '-' then
      let e := blockEnd ((p.next text).next text) 1
      go e (acc.push ⟨p, e, false⟩)
    else go (p.next text) acc
  lineEnd (p : String.Pos.Raw) : String.Pos.Raw :=
    if p ≥ stop || p.get text == '\n' then p else lineEnd (p.next text)
  /-- End of a block comment at nesting depth `d`, from just after its opening delimiter. -/
  blockEnd (p : String.Pos.Raw) (d : Nat) : String.Pos.Raw :=
    if p ≥ stop then stop
    else if p.get text == '-' && (p.next text).get text == '/' then
      let q := (p.next text).next text
      if d == 1 then q else blockEnd q (d - 1)
    else if p.get text == '/' && (p.next text).get text == '-' then
      blockEnd ((p.next text).next text) (d + 1)
    else blockEnd (p.next text) d

/-- Every comment in a file: plain comments from the whitespace around its tokens, and doc
comments (`/-- -/`, `/-! -/`) from the syntax nodes that hold them. -/
private def fileComments (file : SourceFile) : Array Comment := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array Comment := #[]
  -- the end-of-input token holds the whitespace after the last command, all of a file's text
  -- when it has no command
  let trees := #[file.header] ++ file.commands ++ #[file.eoi]
  for t in trees do
    for tok in tokens t do
      if let .original leading _ trailing _ := tok.getHeadInfo then
        for ws in [leading, trailing] do
          unless seen.contains ws.startPos.byteIdx do
            seen := seen.insert ws.startPos.byteIdx
            out := out ++ commentsIn file.text ws.startPos ws.stopPos
    for doc in nodesOfKind ``Command.docComment t ++ nodesOfKind ``Command.moduleDoc t do
      if let (some a, some b) := (doc.getPos?, doc.getTailPos?) then
        out := out.push ⟨a, b, true⟩
  return out
where
  tokens (s : Syntax) : Array Syntax :=
    match s with
    | .node _ _ args => args.foldl (fun acc a => acc ++ tokens a) #[]
    | .missing => #[]
    | tok => #[tok]

/-- Metric `comments`: Comments (doc comments included), doc comments, and the lines and share of
lines carrying comment text. -/
def comments : Metric where
  name := "comments"
  description := "comments (doc comments included), doc comments, and the lines and share of \
    lines carrying comment text"
  needsSource := true
  run ctx := do
    let mut n := 0; let mut nDoc := 0; let mut lines := 0; let mut total := 0
    for file in ctx.files do
      let map := file.fileMap
      let cs := fileComments file
      n := n + cs.size
      nDoc := nDoc + (cs.filter (·.isDoc)).size
      -- a line carries comment text when the comment's part of it is not blank
      let mut commentLines : Std.HashSet Nat := {}
      for c in cs do
        let first := (map.toPosition c.start).line
        let parts := (String.Pos.Raw.extract file.text c.start c.stop).splitOn "\n"
        for part in parts, i in [0:parts.length] do
          unless part.trimAscii.isEmpty do commentLines := commentLines.insert (first + i)
      lines := lines + commentLines.size
      total := total + nonblankLines file.text
    return { columns := #[("n_comments", toJson n), ("n_doc_comments", toJson nDoc),
      ("comment_loc", toJson lines), ("comment_loc_share", ratio lines total)] }

/-- A universe written as a literal `Type n` with `n ≥ 1`. -/
private def isLiteralUniverseAboveZero (s : Syntax) : Bool :=
  s.isOfKind ``Term.type &&
    (s[1].getArgs.any fun l => l.isNatLit?.any (· ≥ 1))

/-- Occurrences of an atom under `s`, outside syntax quotations. -/
private def countAtom (v : String) (s : Syntax) : Nat :=
  foldNodes (fun n t => n + (t.getArgs.filter (fun a => a.isAtom && a.getAtomVal == v)).size) 0 s

/-- Metric `source_shape`: Line lengths, declaration-name and file-path lengths, theorems per file,
module docs, and explicit universes. -/
def sourceShape : Metric where
  name := "source_shape"
  description := "line lengths, declaration-name and file-path lengths, theorems per file, \
    module docs, and explicit universes"
  needsSource := true
  run ctx := do
    let mut lineLens : Array Nat := #[]
    let mut nameLens : Array Nat := #[]
    let mut pathLens : Array Nat := #[]
    let mut nTheorem := 0; let mut nModuleDoc := 0
    let mut nType := 0; let mut nTypeStar := 0; let mut nSortStar := 0
    for file in ctx.files do
      lineLens := lineLens ++ ((lines file.text).map (·.length)).toArray
      pathLens := pathLens.push file.path.toString.length
      if file.commands.any (·.isOfKind ``Command.moduleDoc) then nModuleDoc := nModuleDoc + 1
      for cmd in file.commands do
        for decl in declarationsOf cmd do
          if isTheorem decl then nTheorem := nTheorem + 1
          if let some declId := declIdOf? decl then
            if let .ident _ raw _ _ := declId[0] then nameLens := nameLens.push raw.toString.length
        nType := nType +
          foldNodes (fun n t => if isLiteralUniverseAboveZero t then n + 1 else n) 0 cmd
        nTypeStar := nTypeStar + countAtom "Type*" cmd
        nSortStar := nSortStar + countAtom "Sort*" cmd
    let nFiles := ctx.files.size
    return { columns := #[
      ("shp_line_len_p99", percentile lineLens 99), ("shp_line_len_max", toJson (maximum lineLens)),
      ("shp_frac_lines_over_100", ratio (lineLens.filter (· > 100)).size lineLens.size 4),
      ("shp_decl_name_len_mean", mean nameLens), ("shp_decl_name_len_p95", percentile nameLens 95),
      ("shp_decl_name_len_max", toJson (maximum nameLens)),
      ("shp_file_path_len_max", toJson (maximum pathLens)),
      ("shp_theorems_per_file", ratio nTheorem nFiles 2),
      ("shp_frac_files_module_doc", ratio nModuleDoc nFiles),
      ("shp_n_type_ge1", toJson nType), ("shp_n_type_star", toJson nTypeStar),
      ("shp_n_sort_star", toJson nSortStar)] }

end LeanMetrics
