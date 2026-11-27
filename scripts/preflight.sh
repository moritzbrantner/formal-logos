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
# When HEAD is behind origin/main it also checks that every batch spec regenerates
# unchanged on the merge result (main requires branches to be up to date).
set -euo pipefail

base_ref=""
allow_dirty=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --base) base_ref="${2:?--base needs a ref}"; shift 2 ;;
    --allow-dirty) allow_dirty=1; shift ;;
    -h|--help) sed -n '2,13p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
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
step "placement gate (new results reach the root, are placed, or record a connection_plan)" \
  target/release/truth orphans --base "$base" --gate
step "batch specs regenerate their records" python3 scripts/argument_batch.py records --check specs/*.toml

# Files changed since the base: committed, staged, unstaged and untracked (not ignored).
changed=$(
  {
    git diff --name-only --diff-filter=d "$base"...HEAD
    git diff --name-only --diff-filter=d --cached
    git diff --name-only --diff-filter=d
    git ls-files --others --exclude-standard
  } | sort -u
)

# Every batch spec must also regenerate unchanged once this branch is merged with
# origin/main (#2139: two PRs that each passed broke main together through a stale
# regeneration). When HEAD is behind origin/main, check the committed merge result in
# a scratch copy; the working tree is not touched.
merged_specs() {
  local upstream=origin/main out tree tmp status=0
  if ! git rev-parse --verify -q "$upstream^{commit}" >/dev/null; then
    echo "no $upstream: skipped"
    return 0
  fi
  if git merge-base --is-ancestor "$upstream" HEAD; then
    echo "HEAD contains $upstream: the check above already covers the merge"
    return 0
  fi
  if ! out=$(git merge-tree --write-tree --no-messages HEAD "$upstream"); then
    echo "HEAD does not merge cleanly with $upstream: merge it, resolve the conflicts and rerun" >&2
    return 1
  fi
  tree=${out%%$'\n'*}
  tmp=$(mktemp -d "${TMPDIR:-/tmp}/preflight-merge.XXXXXX")
  git archive "$tree" corpus results specs scripts | tar -x -C "$tmp"
  (cd "$tmp" && python3 scripts/argument_batch.py records --check specs/*.toml) || status=$?
  rm -rf "$tmp"
  if (( status != 0 )); then
    echo "the merge with $upstream leaves records stale: merge $upstream, regenerate with" \
      "'python3 scripts/argument_batch.py records SPEC --write --fix' and rerun" >&2
  fi
  return "$status"
}
step "batch specs regenerate their records on the merge with origin/main" merged_specs

step "bundle audit" python3 scripts/bundle_audit.py

# The bundle-audit tests (Python and explorer) pin record counts of the audited
# bundles, so a corpus change can break them without touching the audit itself.
# Scoped: they run only when a corpus record or an audited bundle input changed.
audit_tests() {
  if ! grep -qE '^(corpus/|docs/notes/[^/]*-migration\.json$|scripts/(test_)?bundle_audit\.py$|apps/corpus-explorer/src/lib/bundle-audit)' <<<"$changed"; then
    echo "no corpus record or audited bundle input changed: skipped"
    return 0
  fi
  python3 -m unittest discover -s scripts -p test_bundle_audit.py || return 1
  if command -v bun >/dev/null; then
    (cd apps/corpus-explorer && bun test src/lib/bundle-audit.test.ts) || return 1
  else
    echo "bun not found: the explorer bundle-audit test is left to CI"
  fi
}
step "bundle-audit tests (when corpus records or audited bundles changed)" audit_tests

step "generated docs tables" python3 scripts/docs_index.py
step "generated import aggregators" scripts/root-imports.sh

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
