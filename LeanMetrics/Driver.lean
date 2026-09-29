/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang, Vasily Ilin
-/
module

public import LeanMetrics.Basic
public import LeanMetrics.Project
import LeanMetrics.Authored
import LeanMetrics.Shake
import LeanMetrics.Source
import LeanMetrics.Syntax

/-! # Measuring a project

Load a built Lake project, parse its files, read its build logs and run the metrics.
The output is one JSON document; see `SCHEMA.md`.
-/

public section

open Lean System Lake

namespace LeanMetrics

/-- A JSON value whose objects keep their fields in the given order. -/
inductive Output where
  | value (j : Json)
  | object (fields : Array (String × Output))
  deriving Inhabited

/-- Render with one field per line; values that are not `Output.object`s stay on one line. -/
partial def Output.render (o : Output) (indent : String := "") : String :=
  match o with
  | .value j => j.compress
  | .object fields =>
    if fields.isEmpty then "{}" else
    let inner := indent ++ "  "
    let lines := fields.map fun (k, v) => inner ++ Json.renderString k ++ ": " ++ v.render inner
    "{\n" ++ ",\n".intercalate lines.toList ++ "\n" ++ indent ++ "}"

/-- Version of the output format, raised whenever a column is renamed, removed or changes
meaning. -/
def schemaVersion : Nat := 2

/-- The version of `lean-metrics`, reported in its output. -/
def toolVersion : String := "0.2.0"

/-- What to measure and how to report it. -/
structure Options where
  /-- Root directory of the Lake project to measure. -/
  root : FilePath := "."
  /-- Libraries to measure; empty means every `lean_lib` of the root package. -/
  libraries : Array Name := #[]
  /-- Measure only modules under these name prefixes; empty means all of the libraries' modules. -/
  modulePrefixes : Array Name := #[]
  /-- Metrics to run; empty means all of them. -/
  metrics : Array String := #[]
  /-- Also report each metric's structured detail. -/
  details : Bool := false
  /-- Report a metric's failure in the output instead of failing the run. -/
  keepGoing : Bool := false
  /-- The project's main results; empty means the declaration nothing depends on whose
  dependency tree is largest. -/
  mainDecls : Array Name := #[]

/-- `path` relative to `root`, when it lies under it. -/
def relativeTo (root path : FilePath) : FilePath :=
  let r := root.toString ++ "/"
  if r.isPrefixOf path.toString then (path.toString.drop r.length).toString else path

/-- Load the project, parse its files and read its build logs. Returns the context, a description
of the project, and diagnostics for anything that could not be read. -/
def loadContext (opts : Options) (parseSource moduleView : Bool) :
    IO (Context × Array (String × Output) × Array (String × Output)) := do
  checkToolchain opts.root
  -- loading the workspace of a project that was never built would fetch its dependencies
  unless ← (opts.root / ".lake").isDir do
    throw <| .userError s!"{opts.root} has not been built; run `lake build` first"
  let ws ← loadWorkspace opts.root
  let libs ← selectLibraries ws opts.libraries
  let underPrefix (m : Name) :=
    opts.modulePrefixes.isEmpty || opts.modulePrefixes.any (·.isPrefixOf m)
  let selected ← selectedModules libs opts.modulePrefixes
  if selected.isEmpty then
    throw <| .userError "no modules selected: the libraries have none under the given prefixes"
  checkBuilt ws <| if opts.modulePrefixes.isEmpty then libs.map (·.name.toString)
    else selected.map (s!"+{·.name}")
  searchPathRef.set ws.augmentedLeanPath
  -- Parsing needs the syntax extensions of the imported modules, which their initializers
  -- register.
  unsafe enableInitializersExecution
  -- `importAll` also loads the private part of module-system files, where their proofs live.
  let imports := selected.map ({ module := ·.name, importAll := true })
  let (env, view) ← withImporting do
    let (_, st) ← (importModulesCore imports).run
    let env ← finalizeImport st imports {} (trustLevel := 1024) (leakEnv := true) (loadExts := true)
    -- the module view: the same files, keeping each declaration's view from importing modules
    let view ← if moduleView then
        let view ← finalizeImport st.markAllExported imports {} (trustLevel := 1024)
          (leakEnv := true) (loadExts := false) (isModule := true)
        some <$> Shake.loadIndirectModUses view
      else pure none
    return (env, view)
  let own := (ownModules ws env).filter (underPrefix ·.name)
  let root := ws.root.dir
  let mut files : Array SourceFile := #[]
  let mut sourceErrors : Array Json := #[]
  let mut elabErrors : Array Json := #[]
  if parseSource then
    let closures := importClosures env
    let namespaces ← namespacesExtension
    for mod in own do
      let path := relativeTo root mod.leanFile
      try
        let some idx := env.getModuleIdx? mod.name | continue
        let (file, msgs) ←
          parseFile env namespaces idx.toNat closures[idx.toNat]! mod.name root path
        files := files.push file
        -- a failed scoping or syntax command matters only where it left the parse incomplete
        if file.commands.any (·.hasMissing) then
          for msg in msgs.toList do
            if msg.severity == .error then
              elabErrors := elabErrors.push <| Json.mkObj [("file", toString path),
                ("line", toJson msg.pos.line),
                ("message", (← msg.data.toString).trimAscii.toString)]
      catch e =>
        sourceErrors := sourceErrors.push
          (Json.mkObj [("file", toString path), ("error", toString e)])
  let mut buildLog : Array BuildMessage := #[]
  let mut withoutLog : Array Name := #[]
  for mod in own do
    match ← buildMessages mod with
    | some msgs => buildLog := buildLog ++ msgs
    | none => withoutLog := withoutLog.push mod.name
  let commands := files.foldl (· ++ ·.commands) #[]
  -- which files start with `prelude`, from their headers alone
  let mut preludeModules : NameSet := {}
  for mod in own do
    let inputCtx := Parser.mkInputContext (← IO.FS.readFile mod.leanFile) mod.leanFile.toString
    let (header, _, _) ← Parser.parseHeader inputCtx
    if (header.raw.find? (·.isOfKind ``Parser.Module.prelude)).isSome then
      preludeModules := preludeModules.insert mod.name
  let authored := own.foldl (init := #[]) fun acc mod =>
    match env.getModuleIdx? mod.name with
    | some idx => env.header.moduleData[idx.toNat]!.constNames.foldl (init := acc) fun acc n =>
        if isAuthored env n then acc.push n else acc
    | none => acc
  let ctx : Context := {
    env, moduleView := view, preludeModules, modules := own.map (·.name),
    moduleSet := own.foldl (·.insert ·.name) {}, files,
    commands, declarations := commands.foldl (· ++ declarationsOf ·) #[], authored, buildLog,
    modulesWithoutLog := withoutLog }
  let diagnostics : Array (String × Output) := #[
    ("reparsed_files", .value (toJson (files.filter (·.reparsed) |>.map (·.path.toString)))),
    ("commands_with_parse_errors", .value <| Json.arr <| files.flatMap fun f =>
      f.commands.filter (·.hasMissing) |>.map fun c => Json.mkObj [("file", toString f.path),
        ("line", toJson (f.fileMap.toPosition (c.getPos?.getD 0)).line)]),
    ("scoping_command_errors", .value (Json.arr elabErrors)),
    ("unreadable_files", .value (Json.arr sourceErrors)),
    ("modules_without_build_log", .value (toJson (withoutLog.map toString)))]
  let project : Array (String × Output) := #[
    ("name", .value (toString ws.root.baseName)),
    ("libraries", .value (toJson (libs.map (·.name.toString)))),
    ("n_modules", .value (toJson own.size))]
  return (ctx, project, diagnostics)

/-- The project's declarations that `names` name as written in the source, where a private name
has none of the mangling Lean adds. -/
def resolveDecls (authored : Array Name) (names : Array Name) : IO (Array Name) :=
  names.mapM fun m => do
    if authored.contains m then return m
    match authored.filter (privateToUserName? · == some m) with
    | #[n] => return n
    | #[] => throw <| .userError s!"`{m}` is not one of the project's declarations"
    | _ => throw <| .userError s!"`{m}` names private declarations of several modules"

/-- Run `metrics` over the project described by `opts`. Returns the output document and whether
every metric succeeded. -/
def measure (opts : Options) (all : Array Metric) : IO (Output × Bool) := do
  let requested := opts.metrics.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]
  let metrics ← if requested.isEmpty then pure all else requested.mapM fun n => do
    let some m := all.find? (·.name == n)
      | throw <| .userError s!"unknown metric `{n}` (see `lean-metrics --list`)"
    pure m
  let (ctx, project, diagnostics) ←
    loadContext opts (metrics.any (·.needsSource)) (metrics.any (·.needsModuleView))
  let ctx := { ctx with mainDecls := ← resolveDecls ctx.authored opts.mainDecls }
  let coreCtx : Core.Context := { fileName := "<lean-metrics>", fileMap := default, options := {} }
  let mut columns : Array (String × Output) := #[]
  let mut details : Array (String × Json) := #[]
  let mut failures : Array (String × Json) := #[]
  for m in metrics do
    try
      let (r, _) ← (m.run ctx).toIO coreCtx { env := ctx.env }
      columns := columns.push (m.name, .object (r.columns.map fun (k, v) => (k, .value v)))
      if opts.details && !r.details.isNull then details := details.push (m.name, r.details)
    catch e =>
      unless opts.keepGoing do throw <| .userError s!"metric `{m.name}` failed: {e}"
      failures := failures.push (m.name, toString e)
  let diagnostics := diagnostics.push ("metric_errors", .value (Json.mkObj failures.toList))
  let doc : Output := .object <| #[
    ("schema_version", .value (toJson schemaVersion)),
    ("tool", .object #[("name", .value "lean-metrics"), ("version", .value toolVersion)]),
    ("lean", .object #[("version", .value Lean.versionString), ("githash", .value Lean.githash)]),
    ("project", .object project),
    ("metrics", .object columns)] ++
    (if opts.details then
      #[("details", .object (details.map fun (k, v) => (k, .value v)))]
    else #[]) ++
    #[("diagnostics", .object diagnostics)]
  return (doc, failures.isEmpty)

end LeanMetrics
