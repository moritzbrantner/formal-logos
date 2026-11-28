#!/usr/bin/env bash
# Build truth-mcp locally and install it on the Hetzner host (docs/truth-mcp.md).
#   deploy/truth-mcp/deploy.sh [SSH_HOST]        build, ship, install, restart
#   deploy/truth-mcp/deploy.sh cert [SSH_HOST]   issue the mcp.moenarch.com certificate
# Auth: /opt/truth-mcp/env on the host sets TRUTH_MCP_NO_AUTH=1 (default) or TRUTH_MCP_TOKEN.
set -euo pipefail
domain=mcp.moenarch.com
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)

if [[ ${1:-} == cert ]]; then
  host=${2:-hetzner}
  ssh "$host" "certbot certonly --non-interactive --webroot -w /var/www/letsencrypt -d $domain \
    --key-type ecdsa --deploy-hook /etc/letsencrypt/renewal-hooks/deploy/truth-mcp-tls"
  exit
fi

host=${1:-hetzner}
tag=$(git -C "$repo" rev-parse --short=12 HEAD)$(git -C "$repo" diff --quiet HEAD -- truth truth-mcp deploy Cargo.toml Cargo.lock || echo -dirty)
docker build -f "$here/Dockerfile" -t "truth-mcp:$tag" "$repo"
docker save "truth-mcp:$tag" | gzip -1 | ssh "$host" 'gunzip | docker load'

ssh "$host" mkdir -p /opt/truth-mcp
scp -q "$here/compose.yml" "$host:/opt/truth-mcp/compose.yml"
scp -q "$here/traefik.yml" "$host:/etc/dokploy/traefik/dynamic/truth-mcp.yml"
scp -q "$here/certbot-hook.sh" "$host:/etc/letsencrypt/renewal-hooks/deploy/truth-mcp-tls"
ssh "$host" bash -s -- "$tag" <<'REMOTE'
set -euo pipefail
tag=$1
chmod 755 /etc/letsencrypt/renewal-hooks/deploy/truth-mcp-tls
umask 077
# Auth mode lives in the host's env file: TRUTH_MCP_NO_AUTH=1 (the default
# written here) or TRUTH_MCP_TOKEN=<secret> to require a bearer token.
if ! grep -qE '^(TRUTH_MCP_TOKEN|TRUTH_MCP_NO_AUTH)=' /opt/truth-mcp/env 2>/dev/null; then
  echo "TRUTH_MCP_NO_AUTH=1" >> /opt/truth-mcp/env
fi
# Browser-based MCP clients send an Origin header; allow the hosted chat apps.
if ! grep -q '^TRUTH_MCP_ALLOWED_ORIGINS=' /opt/truth-mcp/env; then
  echo "TRUTH_MCP_ALLOWED_ORIGINS=https://claude.ai,https://chatgpt.com,https://chat.openai.com" >> /opt/truth-mcp/env
fi
chmod 600 /opt/truth-mcp/env
cd /opt/truth-mcp
TRUTH_MCP_TAG=$tag docker compose up -d --remove-orphans
echo "TRUTH_MCP_TAG=$tag" > /opt/truth-mcp/.env
REMOTE
echo "deployed truth-mcp:$tag to $host"
