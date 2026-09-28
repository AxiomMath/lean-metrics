#!/usr/bin/env bash
# Measure the Lake project in the current directory and print its metrics as JSON.
#
#   cd my-project && /path/to/lean-metrics/lean-metrics.sh [lean-metrics options]
#
# Builds the project, builds lean-metrics with the same toolchain, then runs it. Options are passed
# to lean-metrics; see `lean-metrics.sh --help`.
set -euo pipefail

tool="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project="$(pwd)"

# options that only describe the tool need no project
for arg in "$@"; do
  case "$arg" in
    -h|--help|--version|--list)
      (cd "$tool" && lake build lean-metrics >&2)
      exec "$tool/.lake/build/bin/lean-metrics" "$@" ;;
  esac
done

if [[ ! -f "$project/lakefile.toml" && ! -f "$project/lakefile.lean" ]]; then
  echo "lean-metrics: no lakefile in $project; run this at the root of a Lake project" >&2
  exit 2
fi
# compare toolchains as elan names them, with or without the `leanprover/lean4:` origin
toolchain() { tr -d '[:space:]' < "$1" 2>/dev/null | sed 's#^leanprover/lean4:##'; }
want="$(toolchain "$tool/lean-toolchain")"
have="$(toolchain "$project/lean-toolchain")"; have="${have:-none}"
if [[ "$want" != "$have" ]]; then
  echo "lean-metrics: the project uses $have, but this lean-metrics is for $want" >&2
  exit 2
fi

(cd "$project" && lake build >&2)
(cd "$tool" && lake build lean-metrics >&2)
exec "$tool/.lake/build/bin/lean-metrics" --root "$project" "$@"
