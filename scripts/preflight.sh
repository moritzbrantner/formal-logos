#!/usr/bin/env bash
# Pre-push preflight for research workers: the cheap offline checks CI runs, plus a
# lint for mistakes that have repeatedly cost a repair round-trip (#2028-#2030).
#
#   scripts/preflight.sh                 base = merge-base of HEAD and origin/main
#   scripts/preflight.sh --base <ref>    compare against another base
#   scripts/preflight.sh --allow-dirty   report uncommitted/untracked files as a warning
#
# Run from the repository root with target/release/truth built. It fails fast on the
# first failing check. It does not run `lake build`, bind-check, Comparator or NanoDa:
# run the focused build and `truth bind-check --affected --base <BASE>` separately.
set -euo pipefail

base_ref=""
allow_dirty=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --base) base_ref="${2:?--base needs a ref}"; shift 2 ;;
    --allow-dirty) allow_dirty=1; shift ;;
    -h|--help) sed -n '2,11p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "preflight: unknown argument: $1" >&2; exit 2 ;;
  esac
done

cd "$(git rev-parse --show-toplevel)"

if [[ ! -x target/release/truth ]]; then
  echo "preflight: target/release/truth is missing; run: cargo build --locked --release -p truth" >&2
  exit 2
fi

if [[ -n "$base_ref" ]]; then
  base=$(git rev-parse --verify "$base_ref^{commit}")
else
  base=$(git merge-base HEAD origin/main)
fi
echo "preflight: base $base"

step() {
  local name=$1; shift
  local shown="$*"
  (( ${#shown} > 160 )) && shown="${shown:0:160} ..."
  echo
  echo "==> $name: $shown"
  if ! "$@"; then
    echo
    echo "preflight FAILED at: $name" >&2
    echo "  command: $*" >&2
    exit 1
  fi
}

# Same invocations as .github/workflows/ci.yml (corpus-and-lean job).
step "corpus check" target/release/truth check
step "attribution self-check" target/release/truth attribution-check --base "$base"
step "connectivity gate (new statements join the root component or record a connection_plan)" \
  target/release/truth connectivity --base "$base"
step "batch specs regenerate their records" python3 scripts/argument_batch.py records --check specs/*.toml
step "bundle audit" python3 scripts/bundle_audit.py
step "generated docs tables" python3 scripts/docs_index.py
step "generated import aggregators" scripts/root-imports.sh

# Files changed since the base: committed, staged, unstaged and untracked (not ignored).
changed=$(
  {
    git diff --name-only --diff-filter=d "$base"...HEAD
    git diff --name-only --diff-filter=d --cached
    git diff --name-only --diff-filter=d
    git ls-files --others --exclude-standard
  } | sort -u
)

lint() {
  CHANGED="$changed" python3 - <<'PY'
import datetime, json, os, re, sys

today = datetime.date.today().isoformat()
errors = []
artifact = re.compile(r"(^|/)(target|\.lake|node_modules|__pycache__)/|\.pyc$")
heading_date = re.compile(r"\((\d{4}-\d{2}-\d{2})\)")

def walk(node, key, found):
    if isinstance(node, dict):
        for k, v in node.items():
            if k == key and isinstance(v, str):
                found.append(v)
            walk(v, key, found)
    elif isinstance(node, list):
        for v in node:
            walk(v, key, found)
    return found

for path in filter(None, os.environ["CHANGED"].splitlines()):
    if artifact.search(path):
        errors.append(f"{path}: build artifact or cache must not be committed")
        continue
    if not os.path.isfile(path):
        continue
    if path.startswith("docs/") and path.endswith(".md"):
        with open(path, encoding="utf-8") as fh:
            for n, line in enumerate(fh, 1):
                if line.startswith("#"):
                    for d in heading_date.findall(line):
                        if d > today:
                            errors.append(f"{path}:{n}: heading dated {d}, after today ({today})")
    if path.startswith("corpus/") and path.endswith(".json"):
        try:
            with open(path, encoding="utf-8") as fh:
                record = json.load(fh)
        except ValueError as exc:
            errors.append(f"{path}: invalid JSON: {exc}")
            continue
        for label in walk(record, "label", []):
            if len(label) > 100:
                errors.append(f"{path}: label has {len(label)} characters (max 100): {label[:60]}...")
        if path.startswith("corpus/attempts/"):
            for d in walk(record, "date", []):
                if d[:10] > today:
                    errors.append(f"{path}: date {d} is after today ({today})")

for e in errors:
    print(e)
sys.exit(1 if errors else 0)
PY
}
step "lint changed files (artifacts, future dates, label length)" lint

dirty=$(git status --porcelain --untracked-files=normal)
if [[ -n "$dirty" ]]; then
  echo
  echo "Uncommitted or untracked files (the checks above ran on the working tree, not on what you push):"
  echo "$dirty"
  if [[ $allow_dirty -eq 0 ]]; then
    echo "preflight FAILED: commit (or remove) these files, e.g. regenerated records, then rerun." >&2
    exit 1
  fi
fi

echo
echo "preflight passed against $base."
echo "Not run here: the focused 'lake build' of touched modules and"
echo "'target/release/truth bind-check --affected --base $base' for touched results."
