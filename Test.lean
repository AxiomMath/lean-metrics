/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Wang
-/
import Lean.Data.Json

/-!
# Tests

Each directory under `test/fixtures` is a small Lake project. Its `expected.json` holds values
`lean-metrics` must report for it, worked out by hand from the source (or, for unused imports,
taken from `lake shake`); values the file does not list are not checked. An optional
`cases.json` lists further runs, each with the arguments to pass, the exit code to expect, and
the values to expect. Standard output must always be exactly one JSON document.

Run with `lake test`.
-/

open Lean System

def fixtures : FilePath := "test" / "fixtures"

def run (cmd : String) (args : Array String) (cwd : Option FilePath := none) :
    IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd }

def runOk (cmd : String) (args : Array String) (cwd : Option FilePath := none) : IO Unit := do
  let out ← run cmd args cwd
  unless out.exitCode == 0 do
    throw <| .userError s!"`{cmd} {" ".intercalate args.toList}` failed:\n{out.stdout}{out.stderr}"

/-- Paths at which `actual` differs from `expected`. Objects are compared on the keys `expected`
lists; numbers by exact value, so `5` and `5.0` agree. -/
partial def mismatches (path : String) (expected actual : Json) : Array String :=
  match expected, actual with
  | .obj fields, .obj _ =>
    fields.foldl (init := #[]) fun acc k v =>
      match actual.getObjVal? k with
      | .ok a => acc ++ mismatches s!"{path}.{k}" v a
      | .error _ => acc.push s!"{path}.{k}: missing"
  | .num a, .num b => if compare a b == .eq then #[] else #[s!"{path}: expected {a}, got {b}"]
  | e, a => if e == a then #[] else #[s!"{path}: expected {e.compress}, got {a.compress}"]

/-- One run of `lean-metrics` on a fixture, and what it must produce. -/
structure Case where
  args : Array String := #[]
  exit : Nat := 0
  /-- Values the output must contain; only checked when the run succeeds. -/
  expect : Json := .null
  deriving FromJson

/-- Problems with one run: a wrong exit code, output that is not one JSON document, or values
that differ from the expected ones. -/
def check (exe : FilePath) (dir : FilePath) (c : Case) : IO (Array String) := do
  let out ← run exe.toString (#["--root", dir.toString] ++ c.args)
  let label := if c.args.isEmpty then "" else s!" {" ".intercalate c.args.toList}"
  if out.exitCode.toNat != c.exit then
    return #[s!"{label}: exit {out.exitCode}, expected {c.exit}; stderr: {out.stderr.trimAscii}"]
  -- exit 3 (a metric failed under `--keep-going`) still writes the document; other failures none
  if c.exit != 0 && c.exit != 3 then
    return if out.stdout.isEmpty then #[] else #[s!"{label}: wrote to stdout on failure"]
  match Json.parse out.stdout with
  | .error e => return #[s!"{label}: stdout is not one JSON document ({e})"]
  | .ok actual =>
    return if c.expect.isNull then #[] else (mismatches "" c.expect actual).map (label ++ ·)

def main : IO UInt32 := do
  runOk "lake" #["build", "lean-metrics"]
  let exe := (← IO.currentDir) / ".lake" / "build" / "bin" / "lean-metrics"
  let dirs := (← fixtures.readDir).qsort (·.fileName < ·.fileName)
  let mut failed := 0
  for dir in dirs do
    let expectedFile := dir.path / "expected.json"
    unless ← expectedFile.pathExists do continue
    runOk "lake" #["build"] dir.path
    let mut cases : Array Case :=
      #[{ expect := ← IO.ofExcept (Json.parse (← IO.FS.readFile expectedFile)) }]
    let casesFile := dir.path / "cases.json"
    if ← casesFile.pathExists then
      cases := cases ++ (← IO.ofExcept (Json.parse (← IO.FS.readFile casesFile) >>= fromJson?))
    let mut problems : Array String := #[]
    for c in cases do problems := problems ++ (← check exe dir.path c)
    if problems.isEmpty then
      IO.println s!"ok    {dir.fileName}"
    else
      failed := failed + 1
      IO.println s!"FAIL  {dir.fileName}"
      for p in problems do IO.println s!"       {p}"
  -- a source touched but unchanged is still what Lake built from
  let dir := fixtures / "scopes"
  runOk "touch" #[(dir / "Scopes" / "A.lean").toString]
  runOk "lake" #["build"] dir
  let touched ← check exe dir {}
  if touched.isEmpty then IO.println "ok    scopes after touch and rebuild"
  else
    failed := failed + 1
    IO.println s!"FAIL  scopes after touch and rebuild"
    for p in touched do IO.println s!"       {p}"
  -- a module rebuilt without the modules that import it leaves them stale
  let file := dir / "Scopes" / "A.lean"
  let original ← IO.FS.readFile file
  IO.FS.writeFile file (original ++ "\ndef extra : Nat := 0\n")
  runOk "lake" #["build", "Scopes.A"] dir
  let stale ← check exe dir { exit := 2 }
  IO.FS.writeFile file original
  runOk "lake" #["build"] dir
  if stale.isEmpty then IO.println "ok    scopes with a stale importer"
  else
    failed := failed + 1
    IO.println s!"FAIL  scopes with a stale importer"
    for p in stale do IO.println s!"       {p}"
  return if failed == 0 then 0 else 1
