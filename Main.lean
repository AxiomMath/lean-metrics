/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang
-/
module

import Cli
import LeanMetrics

/-!
# `lean-metrics`

Measure the Lake project in the current directory and write the metrics as JSON.
-/

open Cli LeanMetrics

/-- Run the command line `p`. -/
def runCmd (p : Parsed) : IO UInt32 := do
  if p.hasFlag "list" then
    for m in allMetrics do IO.println s!"{m.name}: {m.description}"
    return 0
  let list (flag : String) : Array String :=
    (p.flag? flag |>.map (·.as! (Array String))).getD #[]
  let opts : Options := {
    root := (p.flag? "root" |>.map (·.as! String)).getD "."
    libraries := (list "lib").map String.toName
    modulePrefixes := (list "module").map String.toName
    metrics := list "metric"
    details := p.hasFlag "details"
    keepGoing := p.hasFlag "keep-going"
    mainDecls := (list "main").map String.toName }
  try
    -- the project's initializers and metrics may print; only the JSON document goes to stdout
    let (doc, ok) ← IO.withStdout (← IO.getStderr) (measure opts allMetrics)
    let out := doc.render ++ "\n"
    match p.flag? "output" |>.map (·.as! String) with
    | some path => IO.FS.writeFile path out
    | none => IO.print out
    return if ok then 0 else 3
  catch e =>
    IO.eprintln s!"lean-metrics: {e}"
    return 2

/-- The command line of `lean-metrics`. -/
def cmd : Cmd := `[Cli|
  "lean-metrics" VIA runCmd; ["0.2.0"]
  "Measure a built Lake project: size, declarations, proofs, tactics, imports, dependency \
  structure, documentation and build warnings. Run `lake build` in the project first."

  FLAGS:
    root : String;          "Project directory (default: the current directory)."
    o, output : String;     "Write the JSON here instead of to standard output."
    lib : Array String;     "Measure only these libraries of the root package (comma-separated)."
    module : Array String;  "Measure only modules under these name prefixes (comma-separated)."
    metric : Array String;  "Run only these metrics (comma-separated); see --list."
    details;                "Include per-metric detail such as histograms and per-module lists."
    "keep-going";           "Record a failing metric in the output instead of stopping."
    main : Array String;    "The project's main results, named as in the source (comma-separated)."
    list;                   "List the metrics and exit."
]

/-- Copy everything `h` yields to standard error. -/
partial def forwardToStderr (h : IO.FS.Handle) : IO Unit := do
  let chunk ← h.read 65536
  unless chunk.isEmpty do
    (← IO.getStderr).write chunk
    forwardToStderr h

/-- Whether a command line writes its JSON document to standard output. -/
def writesDocumentToStdout (args : List String) : Bool :=
  !args.any fun a => a == "-o" || a == "--output" || a.startsWith "--output=" ||
    a == "-h" || a == "--help" || a == "--version" || a == "--list"

/-- The document on standard output must be all it carries, but the project's initializers run in
this process and can print, or start programs that print, to the same file descriptor. So a run
that writes to standard output measures in a child process that writes the document to a file and
whose standard output is passed on to standard error. -/
public def main (args : List String) : IO UInt32 := do
  unless writesDocumentToStdout args do return ← cmd.validate args
  let (_, path) ← IO.FS.createTempFile
  try
    let self ← IO.appPath
    let child ← IO.Process.spawn {
      cmd := self.toString, args := (args ++ ["--output", path.toString]).toArray,
      stdin := .null, stdout := .piped }
    forwardToStderr child.stdout
    let code ← child.wait
    if code == 0 || code == 3 then IO.print (← IO.FS.readFile path)
    -- the child explains the failures it anticipates; a crash or a kill explains nothing
    else if code > 3 then
      IO.eprintln s!"lean-metrics: the measurement stopped abnormally (exit {code})"
    return code
  finally
    IO.FS.removeFile path
