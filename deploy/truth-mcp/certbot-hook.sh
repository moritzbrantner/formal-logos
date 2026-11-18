#!/usr/bin/env bash
# Certbot deploy hook, installed by deploy.sh to
# /etc/letsencrypt/renewal-hooks/deploy/truth-mcp-tls: Traefik reads the
# mcp.moenarch.com certificate from its dynamic directory.
set -euo pipefail
if [[ ${RENEWED_LINEAGE:-} == /etc/letsencrypt/live/mcp.moenarch.com ]]; then
  for file in fullchain.pem privkey.pem; do
    target=/etc/dokploy/traefik/dynamic/website-certs/mcp.moenarch.com-$file
    install -m 600 "$RENEWED_LINEAGE/$file" "$target.next"
    mv -f "$target.next" "$target"
  done
  touch /etc/dokploy/traefik/dynamic/truth-mcp.yml
fi
