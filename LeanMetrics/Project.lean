/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang
-/
module

public import LeanMetrics.Basic
public import Lake.Config.Workspace
public import Lake.Load.Workspace
public import Lake.Build.Common
public import Lake.Util.Version
import Lake.Config.InstallPath
import Lake.Config.Env

/-!
# Finding a project's own code

A project is the root package of a Lake workspace. Its own modules are the modules of its
`lean_lib`s, as their `roots` and `globs` select them, together with every module they import
that lives in the root package. Dependencies (Mathlib, Batteries, …) are loaded but not measured.
-/

public section

open Lean System Lake

namespace LeanMetrics

/-- The project must use the toolchain this tool was built with: `.olean` files are specific to
one Lean version. -/
def checkToolchain (dir : FilePath) : IO Unit := do
  unless ← dir.isDir do throw <| .userError s!"{dir} is not a directory"
  let some project ← ToolchainVer.ofDir? dir | return
  -- `Lean.toolchain` omits the `v` of a release tag, which `lean-toolchain` files write
  let tool := ToolchainVer.ofString s!"{Lean.origin}:v{Lean.versionString}"
  unless project == tool do
    throw <| .userError s!"the project uses {project}, but lean-metrics was built with {tool}; \
      build lean-metrics with the project's toolchain"

/-- The Lean installation `lean` resolves to in `dir`, which is the project's toolchain when
elan manages it. -/
def leanInstallIn (dir : FilePath) : IO LeanInstall := do
  let out ← IO.Process.output { cmd := "lean", args := #["--print-prefix"], cwd := dir }
  unless out.exitCode == 0 do
    throw <| .userError s!"could not find a Lean installation: `lean --print-prefix` failed \
      in {dir}"
  LeanInstall.get out.stdout.trimAscii.copy (collocated := true)

/-- The root package of the workspace at `dir`, loaded as `lake` would load it. -/
def loadWorkspace (dir : FilePath) : IO Workspace := do
  let wsDir ← IO.FS.realPath dir
  let lean ← leanInstallIn wsDir
  -- a standard toolchain ships Lake next to Lean
  let lakeEnv ←
    match ← (Lake.Env.compute (LakeInstall.ofLean lean) lean (← findElanInstall?)).toBaseIO with
    | .ok env => pure env
    | .error msg => throw <| .userError s!"could not set up the Lake environment: {msg}"
  let (ws?, log) ← (Lake.loadWorkspace { lakeEnv, wsDir }).captureLog
  match ws? with
  | some ws => return ws
  | none => throw <| .userError s!"could not load the Lake workspace at {wsDir}:\n{log}"

/-- The libraries to measure: those named in `libs`, or else those `lake build` builds (the root
package's default targets that are libraries), or else every `lean_lib` of the root package. -/
def selectLibraries (ws : Workspace) (libs : Array Name) : IO (Array LeanLib) := do
  let all := ws.root.leanLibs
  if libs.isEmpty then
    let defaults := all.filter fun lib => ws.root.defaultTargets.contains lib.name
    return if defaults.isEmpty then all else defaults
  libs.mapM fun n => match all.find? (·.name == n) with
    | some lib => pure lib
    | none => throw <| .userError
        s!"the root package has no library `{n}` (it has {all.map (·.name) |>.toList})"

/-- The modules the libraries' `roots` and `globs` select, or, given name prefixes, the modules of
the libraries' source directories under them. Their imports are added once the environment is
loaded (`ownModules`). -/
def selectedModules (libs : Array LeanLib) (prefixes : Array Name) : IO (Array Lake.Module) :=
  libs.foldlM (init := #[]) fun acc lib => do
    if prefixes.isEmpty then return acc ++ (← lib.getModuleArray)
    let found ← IO.mkRef acc
    let add (mod : Name) := do
      if lib.isBuildableModule mod then found.modify (·.push { lib, name := mod })
    for p in prefixes do
      -- `p` may name a module (`P.lean`), a directory of modules (`P/`), or both
      if ← (modToFilePath lib.srcDir p "lean").pathExists then add p
      if ← (modToFilePath lib.srcDir p "").isDir then
        Glob.submodules p |>.forEachModuleIn lib.srcDir add
    found.get

/-- Every module in `env` whose source belongs to the root package, in import order. -/
def ownModules (ws : Workspace) (env : Environment) : Array Lake.Module :=
  env.header.moduleNames.filterMap ws.root.findModule?

/-- Fail unless the build of `targets` is up to date, as Lake judges it: every module's sources,
imports and options are those its artifacts were built from, dependencies included. This asks
Lake itself (`lake build --no-build`), which builds nothing. -/
def checkBuilt (ws : Workspace) (targets : Array String) : IO Unit := do
  let out ← IO.Process.output
    { cmd := ws.lakeEnv.lake.lake.toString, args := #["build", "--no-build"] ++ targets,
      cwd := ws.root.dir }
  unless out.exitCode == 0 do
    let detail := (out.stdout ++ out.stderr).trimAscii.toString
    throw <| .userError
      s!"the project is not built; run `lake build` first\n{detail}"

/-- Build messages Lake saved in a module's trace file, or `none` when they are unknown: there is
no trace, or the module was fetched from a cache rather than compiled. -/
def buildMessages (mod : Lake.Module) : IO (Option (Array BuildMessage)) := do
  let (trace?, _) ← (readTraceFile mod.traceFile).run? {}
  match trace? with
  | some (.ok data) =>
    if data.synthetic then return none
    return some <| data.log.entries.filterMap fun e =>
      if e.level == .trace then none
      else some { module := mod.name, level := e.level, message := e.message }
  | _ => return none

end LeanMetrics
