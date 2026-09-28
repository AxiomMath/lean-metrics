# `lean-metrics`

Source and dependency-structure metrics for Lean 4 projects, as one JSON document.
The format is described in [`SCHEMA.md`](./SCHEMA.md).

`lean-metrics` reads a built Lake project: source files with Lean's parser, declarations from the
compiled environment, and build warnings from Lake's trace files.

## Requirements

- `lean-metrics` must be built with the same Lean version as the project it measures, because
  `.olean` files are specific to one Lean version. The `main` branch targets Lean `v4.34.0`.
- The project must build: `lake build` in the project exits without an error. `lean-metrics` reads
  the compiled modules and does not build them itself.

## How to Run

1. Build `lean-metrics` with `lake build`.

2. Call the `lean-metrics` binary from the root of the project, or pass the project with `--root`.

For example, with a project `MyProject` next to this repository:
```
|__ MyProject (*we are here)
|__ lean-metrics
```

build the project and measure it:
```sh
lake build
../lean-metrics/.lake/build/bin/lean-metrics > metrics.json
```

This measures the libraries `lake build` builds (the default targets that are `lean_lib`s) and
every module they import from the project itself. Dependencies such as Mathlib are loaded but not
measured.

Alternatively, `lean-metrics.sh` does both steps: run from the root of a project, it builds the
project, builds `lean-metrics` with the same toolchain, and runs it.
```sh
../lean-metrics/lean-metrics.sh > metrics.json
```

### Options

`--root DIR` measures the project in `DIR` instead of the current directory.

`-o FILE` (or `--output FILE`) writes the document to `FILE` instead of standard output.

`--lib A,B` measures only these libraries of the project.

`--module P,Q` measures only the modules under these name prefixes. This selects one project of a
monorepo, for example `--module MyMonorepo.ProjectA`, and loads only what those modules import.

`--metric M,N` runs only these metrics; `--list` lists all of them with a one-line description.

`--details` adds structured detail to the document, such as the tactic histogram, the dependency
graph's edges, and the imports `lake shake` would remove and add in each module.

`--main A,B` names the project's main results, as they are written in the source. The dependency
graph (`dep_graph`) is measured from the largest of them; by default, from the largest declaration
nothing in the project depends on. Other metrics ignore it.

`--keep-going` records a metric that fails in the document instead of stopping.

The exit code is 0 on success, 1 when the command line cannot be parsed, 2 when the project cannot
be measured (including an unknown library, metric or main result), and 3 when a metric failed under
`--keep-going`. Every failure is explained on standard error.

## Metrics

Each metric is a group of columns in the document's `metrics` object. [`SCHEMA.md`](./SCHEMA.md)
defines every column. `lean-metrics --list` prints one line per metric.

* `loc`, `files`, `comments`, `source_shape`: file size, comments and source text.
* `declarations`, `implicit_args`, `proof_mode`, `reducibility`, `recursion_style`: declarations.
* `tactics`, `decide_usage`, `sorry_axiom`: tactic calls, decision procedures, `sorry` and axioms.
* `proof_size`, `proof_structure`, `proof_length`: proof size and structure.
* `set_options`, `attributes`, `metaprogramming`, `namespaces`: options, attributes, syntax and
  scope.
* `imports`, `import_discipline`, `import_minimizability`: imports, including ones `lake shake`
  would remove.
* `dep_graph`: the declaration dependency graph.
* `docstrings`, `name_opacity`: documentation and declaration names.
* `warnings`: build warnings.

## Notes

### Parsing

Each source file is first parsed against the environment of the whole project. When that parse has
errors, or uses syntax the file could not have seen when it was compiled, the file is parsed again
against exactly its own imports. Such files are listed under `diagnostics.reparsed_files`.

### Unused imports

`import_minimizability` reports the imports `lake shake` (Lean `v4.34.0`) would remove and add,
and respects `-- shake: keep`. It also runs on projects outside the module system, where
`lake shake` itself does not.

> [!NOTE]
> Loading a project runs its `initialize` declarations, as Lean does when it imports them, so only
> measure projects you would build. Anything they print goes to standard error, never into the
> document.

> [!NOTE]
> Loading the environment dominates memory use. A project that imports all of Mathlib needs several
> gigabytes.

### Troubleshoot

* `the project is not built`: a module changed since it was built. Run `lake build` in the project
  first.
* `the project uses …, but lean-metrics was built with …`: build `lean-metrics` with the project's
  toolchain.

## Testing

```sh
lake test
```

This builds each project under `test/fixtures`, measures it, and compares the document with the
values in the project's `expected.json`, which are worked out by hand from its source or taken from
`lake shake`.

## License

Apache 2.0; see [`LICENSE`](./LICENSE) and [`NOTICE`](./NOTICE).
