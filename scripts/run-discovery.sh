#!/usr/bin/env bash
# Run local Duper discovery and keep its report; this never updates the corpus.
# Usage:
#   bash scripts/run-discovery.sh
#   bash scripts/run-discovery.sh --targets open-root --module TruthCore.Causality --limit 40 --premise-pool all
#   bash scripts/run-discovery.sh --target STATEMENT --premise-pool all
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

if (( $# == 0 )); then
    set -- --targets next-tests --limit 30 --premise-pool all
fi

truth="${TRUTH_DISCOVER_BIN:-$root/target/release/truth}"
if [[ ! -x "$truth" ]]; then
    printf 'Missing truth CLI: %s\nBuild it with: cargo build --locked --release -p truth\n' "$truth" >&2
    exit 2
fi

report_dir="${TRUTH_DISCOVER_REPORT_DIR:-$root/.cache/discover}"
lock="${TRUTH_DISCOVER_LOCK:-/tmp/moenarch/truth-core-heavy.lock}"
mkdir -p -- "$report_dir" "$(dirname -- "$lock")"
run_dir="$(mktemp -d "$report_dir/$(date -u +%Y%m%dT%H%M%SZ)-XXXXXXXX")"
git rev-parse HEAD > "$run_dir/revision.txt"
git status --porcelain > "$run_dir/status.txt"
printf '%q ' "$truth" --json discover "$@" > "$run_dir/command.txt"
printf '\n' >> "$run_dir/command.txt"

printf 'Discovery output: %s\n' "$run_dir"
if [[ -s "$run_dir/status.txt" ]]; then
    printf 'Note: the working tree is not clean; see status.txt for uncommitted changes.\n' >&2
fi

if flock "$lock" python3 scripts/worker_env.py -- "$truth" --json discover "$@" \
    > "$run_dir/report.json" 2> >(tee "$run_dir/stderr.log" >&2); then
    :
else
    result=$?
    printf 'Discovery failed (exit %s). Inspect %s/stderr.log\n' "$result" "$run_dir" >&2
    exit "$result"
fi

python3 - "$run_dir/report.json" <<'PY'
import json
from pathlib import Path
import sys

path = Path(sys.argv[1])
try:
    report = json.loads(path.read_text())
    summary = report['summary']
    print(f"Report: {path}")
    print(f"Targets: {summary['targets']}; proved: {summary['proved']}; "
          f"discoveries: {summary['discoveries']}; "
          f"incompatibilities: {summary['incompatibilities']}; "
          f"missing bridges: {summary['missing_bridges']}; "
          f"unresolved: {summary['unresolved']}; errors: {summary['errors']}")
except (OSError, ValueError, KeyError, TypeError) as exc:
    sys.exit(f"Invalid discovery report at {path}: {exc}")
if summary['errors']:
    sys.exit('Discovery completed with internal errors; inspect the saved report.')
PY
