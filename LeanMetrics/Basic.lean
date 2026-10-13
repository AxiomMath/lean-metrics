/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang
-/
module

public import Lean.Environment
public import Lean.CoreM
public import Lean.Data.Json
public import Lake.Util.Log

/-! # Metrics over a Lean project

A `Metric` reads a `Context` — the compiled environment, the parsed source and the build log —
and reports named columns.
-/

public section

open Lean System

namespace LeanMetrics

/-- One of the project's own source files, parsed as written. -/
structure SourceFile where
  /-- The module the file defines. -/
  module : Name
  /-- Path relative to the project root. -/
  path : FilePath
  text : String
  fileMap : FileMap
  /-- The module header (`module`, `prelude`, `import`s). -/
  header : Syntax
  /-- Top-level commands in source order. Macros are unexpanded; a `choice` node keeps its
  first alternative. -/
  commands : Array Syntax
  /-- The end-of-input token, whose leading whitespace holds the comments after the last command. -/
  eoi : Syntax := .missing
  /-- Tactic kinds the file declares with `local` syntax, which the project's environment lacks. -/
  localTacticKinds : NameSet := {}
  /-- Whether the file had to be parsed again with only its own imports' syntax (see
  `LeanMetrics.parseFile`). -/
  reparsed : Bool := false
  deriving Inhabited

/-- A diagnostic Lake recorded while building one of the project's modules. -/
structure BuildMessage where
  module : Name
  level : Lake.LogLevel
  message : String
  deriving Inhabited

/-- Everything a metric may read. -/
structure Context where
  env : Environment
  /-- The same modules loaded as `lake shake` loads them, when a metric asks for it
  (`Metric.needsModuleView`): each declaration keeps both the view its own module has and the
  view importers have, which say whether an import is needed publicly. -/
  moduleView : Option Environment
  /-- The project's own modules: those whose source lives in the root package. -/
  modules : Array Name
  /-- Own modules whose file starts with `prelude`, so that an `Init` import is written, not
  implicit. -/
  preludeModules : NameSet := {}
  moduleSet : NameSet
  files : Array SourceFile
  /-- The top-level commands of all files, file by file. -/
  commands : Array Syntax
  /-- The declaration nodes those commands introduce (see `LeanMetrics.declarationsOf`). -/
  declarations : Array Syntax
  /-- The declarations of the project's modules an author wrote (see `LeanMetrics.isAuthored`),
  in module order. -/
  authored : Array Name
  /-- Build messages of the project's own modules, from Lake's trace files. -/
  buildLog : Array BuildMessage
  /-- Modules whose trace file was missing, so their messages are unknown. -/
  modulesWithoutLog : Array Name
  /-- The project's main results, when given, under their internal names; `dep_graph` measures
  from the largest of them. -/
  mainDecls : Array Name := #[]

/-- Module a constant is defined in (the main module for constants added after import). -/
def Context.moduleOf? (ctx : Context) (n : Name) : Option Name :=
  match ctx.env.getModuleIdxFor? n with
  | some idx => ctx.env.header.modules[idx.toNat]?.map (·.module)
  | none => if ctx.env.constants.map₂.contains n then some ctx.env.header.mainModule else none

/-- Whether a constant is defined in one of the project's own modules. -/
def Context.isOwn (ctx : Context) (n : Name) : Bool :=
  (ctx.moduleOf? n).any ctx.moduleSet.contains

/-- A metric's output: flat columns, and optional structured detail (per-module lists,
histograms) that is emitted only when asked for. -/
structure Report where
  columns : Array (String × Json)
  details : Json := .null

/-- A named group of columns computed from a `Context`. -/
structure Metric where
  name : String
  /-- One sentence on what the metric measures, shown by `lean-metrics --list`. -/
  description : String
  /-- Whether the metric reads the parsed source; metrics that do not can run without parsing. -/
  needsSource : Bool
  /-- Whether the metric reads `Context.moduleView`. -/
  needsModuleView : Bool := false
  run : Context → CoreM Report

end LeanMetrics
