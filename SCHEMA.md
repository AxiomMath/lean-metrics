# `lean-metrics` output format: version 1

`lean-metrics` writes one JSON object. It begins with version information for the format, the tool
and Lean, and a description of the project, followed by the metrics:

```
{
    "schema_version": integer,
    "tool": {
        "name": string,
        "version": string
    },
    "lean": {
        "version": string,
        "githash": string
    },
    "project": {
        "name": string,
        "libraries": [string],
        "n_modules": integer
    },
    "metrics": {
        "<metric>": { "<column>": number | boolean | string | null, ... },
        ...
    },
    "details": { "<metric>": ..., ... },
    "diagnostics": { ... }
}
```

`details` is present only with `--details`. The objects keep their fields in the order shown here
and, within a metric, in the order its columns are listed below.

`schema_version` is raised whenever a column is renamed, removed, or changes meaning. Adding a
column or a metric does not raise it.

## What is measured

The project is the root package of the Lake workspace. Its libraries are those `lake build` builds:
the default targets that are `lean_lib`s, or every `lean_lib` when none is a default target. Its
modules are those these libraries select through `roots` and `globs`, together with every module
they import from the root package. `--lib` restricts this to some of the libraries, and `--module`
to modules under given name prefixes. Dependencies are loaded but not measured.

Source metrics read each file with Lean's parser, macros unexpanded. Declarations inside `mutual`
blocks and `… in` wrappers are included. Syntax quotations, such as `` `(tactic| simp) ``, are
skipped.

Environment metrics count authored declarations. See `LeanMetrics.Authored`.

Means, medians and ratios are rounded half away from zero. Percentiles interpolate linearly between
the order statistics at rank `1 + p(n-1)/100`. A ratio with a zero denominator is `0`.

## Columns

### `loc`
- `loc`: non-blank lines over all files.

### `files`
- `n_files`: number of files.
- `file_loc_mean`, `file_loc_median`: non-blank lines per file.

### `comments`
- `n_comments`: comments of every kind, doc comments included.
- `n_doc_comments`: doc comments (`/-- -/`) and module docs (`/-! -/`).
- `comment_loc`: lines carrying comment text.
- `comment_loc_share`: `comment_loc` over `loc`.

### `source_shape`
- `shp_line_len_p99`, `shp_line_len_max`: line lengths in characters.
- `shp_frac_lines_over_100`: share of lines longer than 100 characters, Mathlib's limit.
- `shp_decl_name_len_mean`, `shp_decl_name_len_p95`, `shp_decl_name_len_max`: lengths of declaration
  names as written.
- `shp_file_path_len_max`: longest file path relative to the project root.
- `shp_theorems_per_file`: theorems over files.
- `shp_frac_files_module_doc`: share of files with a module doc.
- `shp_n_type_ge1`: universes written as a literal `Type n` with `n ≥ 1`.
- `shp_n_type_star`, `shp_n_sort_star`: uses of Mathlib's `Type*` and `Sort*`.

### `declarations`
- `n_theorem` (theorems and `lemma`s), `n_def`, `n_abbrev`, `n_instance`, `n_structure`, `n_class`
  (`class` and `class inductive`), `n_inductive`, `n_axiom`, `n_opaque`, `n_example`: counts by
  kind. `n_instance` also counts instances declared by `deriving` clauses (one per class and type)
  and `attribute [instance]` commands.
- `n_decls`: all of the above except `example`.
- `n_def_like`: `def`, `abbrev`, `class`, `structure`, `inductive` and `instance` together.
- `def_like_to_theorem_ratio`: `n_def_like` over `n_theorem`.
- `n_decls_implicit_args`: declarations whose signature has an implicit (`{…}`) or strict-implicit
  (`⦃…⦄`) binder group. `variable` binders do not count.
- `n_new_classes`, `n_new_instances`: same as `n_class` and `n_instance`.

### `implicit_args`
- `n_ia_explicit`, `n_ia_implicit`, `n_ia_strict`, `n_ia_inst`: binder groups in declaration
  signatures, by kind.
- `ia_implicit_ratio`: share of those groups that are not explicit.

### `proof_mode`
- `n_pm_tactic`, `n_pm_term`: theorems proved by a tactic block (`:= by …`), and all others, which
  includes pattern-matching alternatives.
- `pm_term_ratio`: share of theorems proved by a term.

### `reducibility`
- `n_red_irreducible`, `n_red_reducible`: applications of these attributes.
- `n_red_abbrev`, `n_red_def`: `abbrev` and `def` declarations.
- `red_irreducible_per_def`, `red_abbrev_per_def`: per `def`.

### `recursion_style`
- `n_rec_termination_by`, `n_rec_decreasing_by`: clauses giving a termination measure or proof.
- `n_rec_well_founded`: their sum; `rec_uses_well_founded`: whether it is positive.

### `tactics`
A tactic call is a syntax node whose kind is in the environment's `tactic` category. That includes
tactics from Mathlib and from the project itself, and combinators (`<;>`, `first`, `try`,
`all_goals`). Grouping forms (`(…)`, `·`, nested blocks) are not calls. A call is keyed by the
keyword it is written with. All commands are counted, including `decreasing_by` blocks outside
theorem bodies.
- `n_tactic_calls`, `n_distinct_tactics`: calls, and distinct keywords.
- `frac_by_automation`: share of calls made by `aesop`, `decide`, `gcongr`, `grind`, `linarith`,
  `native_decide`, `nlinarith`, `norm_num`, `omega`, `positivity`, `ring` or `simp`.
- `tactic_<name>`: calls of each automation tactic above, and of `apply`, `calc`, `change`, `dsimp`,
  `exact`, `have`, `intro`, `let`, `letI`, `linarith`, `norm_num`, `obtain`, `omega`, `rcases`,
  `refine`, `rfl`, `ring`, `rw`, `simp` and `simpa`.
- `n_unfold`: calls of `unfold`.
- `n_omit`: `omit` commands.
- `n_set_option`: `set_option` at command, term and tactic level.
- Details: `histogram`, every keyword with its number of calls.

### `decide_usage`
- `n_dec_decide`, `n_dec_kernel`, `n_dec_native`: `decide` calls, split by whether their
  configuration turns on `kernel` or `native` (`+kernel`, `(kernel := true)`); the first counts the
  rest.
- `n_dec_native_decide`: `native_decide` calls; `dec_uses_native_decide`: whether there are any.
- `n_dec_simp_arith`: `simp`, `simp_all`, `simpa` and `dsimp` calls whose configuration turns on
  `arith`.
- `n_dec_rfl`: the `rfl` tactic, and declarations whose body is the term `rfl`.

### `sorry_axiom`
- `n_sorry`, `n_admit`: `sorry` (tactic or term) and `admit`.
- `n_sorryax_axiom`: `axiom` declarations.
- `n_sorryax_native_decide`: `native_decide` calls.

### `proof_size`
Over theorem bodies, with nearest-rank percentiles.
- `ps_n_theorems`: theorem bodies.
- `ps_calls_p50`, `ps_calls_p90`, `ps_calls_p99`, `ps_calls_max`: tactic calls per proof.
- `ps_nodes_p50`, `ps_nodes_p90`, `ps_nodes_max`: syntax nodes per proof.
- `ps_haves_p90`, `ps_haves_max`: tactic `have`s per proof.
- `ps_by_depth_p90`, `ps_by_depth_max`: deepest nesting of `by` blocks.
- `ps_frac_over_30_calls`, `ps_frac_over_100_calls`, `ps_frac_over_200_calls`: share of proofs with
  more tactic calls than that.
- `ps_calls_share_longest_decile`: share of all tactic calls made in the tenth of proofs with the
  most.
- Details: `tactic_calls`, `syntax_nodes`, `haves` and `by_depth` as `{n, p50, p90, p99, max, sum}`.

### `proof_structure`
Keyword tokens in theorem bodies, in tactic and term position alike.
- `n_ps_have`, `n_ps_let`, `n_ps_suffices`, `n_ps_show`, `n_ps_calc`: each keyword's count.
- `n_ps_destructuring`: `obtain` and `rcases`.
- `n_ps_steps`: the sum of the above.
- `ps_steps_per_proof`, `ps_<construct>_per_proof`: the same, per theorem.

### `proof_length`
- `n_proofs`: theorem bodies.
- `proof_loc_mean`, `proof_loc_median`, `proof_loc_max`: non-blank lines of the body. A first line
  holding only `by` is not counted.

### `set_options`
- `n_setopt_total`: `set_option` at every level.
- `n_maxHeartbeats`, `n_maxRecDepth`: of these two options.
- `n_linter_disable`: `linter.*` options set to `false`.
- `n_exotic_options`: options that weaken a check (`backward.*`, `debug.skipKernelTC`, `trust`).
- `n_setopt_distinct_names`: distinct options set.

### `attributes`
- `n_attributes`: attribute instances in `@[…]` and `attribute […]`; `attribute [simp] a b` is one.
- `attr_simp`, `attr_instance`, `attr_reducible`, `attr_irreducible`, `attr_inline`, `attr_ext`,
  `attr_deprecated`: applications of each.
- `n_attributes_other`: the rest.
- `n_attribute_commands`: `attribute […]` commands.

### `metaprogramming`
- `n_macro`, `n_macro_rules`, `n_elab`, `n_elab_rules`, `n_syntax`, `n_declare_syntax_cat`: commands
  of each kind.
- `n_run_cmd`, `n_eval`: `run_cmd` and `#eval` commands.
- `n_open_meta`: `open` commands naming a namespace under `Lean` or `Qq`.
- `uses_metaprogramming`: 1 when any of the above is positive.

### `namespaces`
- `n_ns_cmds`, `n_ns_sections`: `namespace` and `section` commands.
- `n_ns_distinct`: distinct namespaces entered by `namespace` commands, each resolved against the
  enclosing namespace (`namespace B` inside `namespace A` enters `A.B`).
- `n_ns_max_depth`: deepest scope nesting in any file. `namespace A.B` opens two scopes.

### `imports`
Imports as the compiled modules record them, without the implicit `Init`.
- `mathlib_imports_per_file`, `nonmathlib_imports_per_file`: per module, mean imports from `Mathlib`
  and from elsewhere.
- `n_mathlib_modules`: distinct `Mathlib` modules imported.

### `import_discipline`
- `n_imp_import`: imports over all modules.
- `n_imp_mathlib_wholesale`: imports of the module `Mathlib` itself; `imp_mathlib_wholesale`:
  whether there are any.
- `n_imp_distinct`: distinct modules imported.

### `import_minimizability`
Unused imports as `lake shake` finds them. See `LeanMetrics.Shake`.
- `n_impmin_imports`: imports, without the implicit `Init`.
- `n_impmin_removable_imports`: imports `lake shake` would remove; `impmin_frac_removable`: their
  share. An import it would replace with a narrower one, or downgrade from `public`, counts as
  removed.
- `n_impmin_imports_to_add`: imports it would add in their place.
- `n_impmin_unused_imports`: imports it would remove under `--keep-implied`, which keeps an import
  the remaining imports imply; `impmin_frac_unused`: their share.
- `n_impmin_removable_by_constants`, `n_impmin_unused_by_constants`: the same two counts from
  constants alone, followed transitively from each module's public declarations (private ones are
  not followed). An import is removable when every module defining a constant the file transitively
  uses stays reachable through its other imports, and unused when no such module is reachable
  through it. Imports of tactic modules are not included. See `LeanMetrics.Metrics.Imports`.
- `n_impmin_tactic_imports`: imports of tactic modules (`Mathlib.Tactic.*`, `Lean.Elab.Tactic.*`).
- `impmin_uses_import_mathlib`: whether any module imports from `Mathlib`.
- `n_impmin_import_cone_size`: modules reachable from the project's imports.
- Details: `remove_by_module`, `add_by_module`.

### `dep_graph`
Nodes are the authored declarations (see `LeanMetrics.Authored`). An edge runs from `d` to `u` when
`u`'s type or body mentions `d` (see `LeanMetrics.Metrics.Graph`).
- A body's use of an inductive type, an `opaque` constant or a quotient is not an edge; a type's use
  is. The value of an `opaque` constant is not read.
- An edge through a generated constant is redirected to the declaration that constant belongs to.
- A body that goes through a generated auxiliary depends on what the auxiliary's body uses.
- Constants of other packages are *external* leaves; those of `Init`, `Std` and `Lean` are dropped.
- The *main result* is the declaration nothing depends on that has the largest unrolled cost.

Columns:
- `n_graph_decls`, `n_edges`: nodes, and edges between them.
- `out_deg_*`, `in_deg_*` (`mean`, `median`, `max`): dependencies and dependents per declaration.
- `n_roots`: declarations nothing depends on.
- `n_leaves`: declarations that depend on no other declaration of the project.
- `ext_deps_per_decl_mean`, `n_ext_consts`: external constants used per declaration, and distinct
  ones.
- `longest_pole`: edges on the longest dependency chain. A cycle counts as one step.
- `root`: the main result, the declaration with the largest cost (next column) among those given
  with `--main`, or among the declarations nothing depends on when none are given.
- `cost_root_log10`: `log10` of the main result's cost, the size of its dependency tree fully
  unrolled (`cost(v) = 1 + Σ cost(dependencies)`).
- `reachable_from_root`: declarations the main result depends on, itself included.
- `compression_log10`: `log10(cost / reachable)`, how much the proofs share sub-results.
- `cost_max_log10`: the largest cost.
- `has_cycle`: whether the graph has a cycle, a declaration whose body names itself included. Edges
  come from compiled bodies, where structural and well-founded recursion no longer name the
  functions they call, so only `unsafe` definitions produce one. A self-reference is not an edge.
- `n_internal_theorems`, `n_internal_defs`, `n_internal_instances`: nodes by kind. Instances are
  classified first, then theorems, then definitions (`def`, `opaque`, inductive types). Other nodes,
  such as constructors and axioms, are in none of the three.
- `n_theorems_unused`, `n_defs_unused`, `n_instances_unused`: nodes nothing depends on.
- `n_theorems_single_use`: theorems exactly one declaration depends on.
- `n_defs_no_theorem_user`: definitions no theorem mentions.

### `docstrings`
- `n_doc_decls`, `n_doc_documented`: authored declarations, and those with a docstring.
- `doc_coverage`: their ratio.

### `name_opacity`
A name's last component is a *placeholder* when it is:
- a letter followed only by digits or primes (`h`, `x2`);
- one or two letters and a number (`hx1`); or
- one of `aux`, `tmp`, `temp`, `lemma`, `lem`, `thm`, `claim`, `step`, `goal`, `foo`, `bar`, `baz`,
  `hyp`, `h`, optionally followed by a number.

Columns:
- `n_no_named`, `n_no_opaque`: authored declarations, and those with placeholder names.
- `no_opaque_ratio`: their ratio.

### `warnings`
Warnings of the project's own modules, from the logs Lake saves in its trace files. A module fetched
from a cache has no log. A linter warning is grouped by the linter that raised it; other warnings by
their text.
- `n_warnings`, `n_files_with_warnings`.
- `warnings_complete`: whether every module had a build log.
- `n_warn_<kind>`, for each kind: `unused_variable`, `unused_simp_arg`, `unused_section_var`,
  `unreferenced_binder`, `deprecated`, `simpa_to_simp`, `def_for_prop`, `seq_focus`,
  `unused_tactic`, `unreachable_tactic`, `sorry`, `style`, `overlapping_instances` and `other`.

## `diagnostics`

- `reparsed_files`: files parsed a second time against only their own imports. This happens when the
  first parse, against the whole project's environment, had errors or used syntax the file could
  not have seen when it was compiled: syntax from a module it does not import, or its own syntax
  above the point where it declares it.
- `commands_with_parse_errors`: commands that still failed to parse, with file and line. Their
  metrics may be incomplete.
- `scoping_command_errors`: in files that still have parse errors, the scoping or syntax commands
  that failed to elaborate while the file was parsed, with file, line and message.
- `unreadable_files`: files that could not be read or parsed at all.
- `modules_without_build_log`: modules whose warnings are unknown.
- `metric_errors`: metrics that failed under `--keep-going`.
