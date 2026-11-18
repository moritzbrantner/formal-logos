#!/usr/bin/env bash
# Refresh for truth-mcp (docs/truth-mcp.md), run by the server itself.
#   prepare: clone or fetch the repository and, when GH_TOKEN is set, download
#            a fresh issue/PR snapshot into *.next files. Runs while research
#            calls continue.
#   apply:   move the checkout to the fetched commit, install the snapshot and
#            rebuild the note index. Runs while no research call runs.
# The snapshot is a derived cache of public GitHub data, never research authority.
set -euo pipefail
: "${TRUTH_ROOT:?}" "${TRUTH_BIN:?}" "${TRUTH_SNAPSHOT:?}" "${TRUTH_OPEN_ISSUES:?}"
repo_url=${TRUTH_MCP_GIT_URL:-https://github.com/moritzbrantner/formal-logos.git}
gh_repo=${TRUTH_MCP_GH_REPO:-moritzbrantner/formal-logos}
branch=${TRUTH_MCP_BRANCH:-main}

case ${1:-} in
prepare)
  if [[ ! -d $TRUTH_ROOT/.git ]]; then
    git clone --quiet --branch "$branch" "$repo_url" "$TRUTH_ROOT"
  else
    git -C "$TRUTH_ROOT" fetch --quiet origin "$branch"
  fi
  if [[ -n ${GH_TOKEN:-} ]]; then
    mkdir -p "$(dirname "$TRUTH_SNAPSHOT")"
    work=$(mktemp -d)
    trap 'rm -rf "$work"' EXIT
    captured=$(date -u +%Y-%m-%dT%H:%M:%SZ)
    fields=number,title,body,url,state,comments,updatedAt
    gh issue list -R "$gh_repo" --state all --limit 20000 --json "$fields" > "$work/issues.json"
    gh pr list -R "$gh_repo" --state all --limit 20000 --json "$fields" > "$work/prs.json"
    jq -n --arg at "$captured" --slurpfile i "$work/issues.json" --slurpfile p "$work/prs.json" \
      '{captured_at: $at, items: ($i[0] + $p[0])}' > "$TRUTH_SNAPSHOT.next"
    jq '[.[] | select(.state == "OPEN")]' "$work/issues.json" > "$TRUTH_OPEN_ISSUES.next"
  fi
  ;;
apply)
  git -C "$TRUTH_ROOT" reset --quiet --hard "origin/$branch"
  git -C "$TRUTH_ROOT" clean --quiet -fd
  for file in "$TRUTH_SNAPSHOT" "$TRUTH_OPEN_ISSUES"; do
    if [[ -f $file.next ]]; then mv -f "$file.next" "$file"; fi
  done
  "$TRUTH_BIN" --root "$TRUTH_ROOT" index build > /dev/null
  ;;
*)
  echo "usage: $0 prepare|apply" >&2
  exit 2
  ;;
esac
