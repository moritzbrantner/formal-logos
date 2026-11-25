# Read-only MCP endpoint (`truth-mcp`)

`truth-mcp` (#1645) exposes the existing research retrieval commands to remote
agent sessions over MCP (Streamable HTTP, stateless JSON responses). It adds no
corpus, index or proof engine: each tool runs the `truth` binary on one checkout
with a fixed argument vector and returns its text output. It is separate from
the [local agent service](agent-service.md), which must never be exposed.

Deployed at `https://mcp.moenarch.com/mcp` (health: `/healthz`).

## Tools

| Tool | Command |
| --- | --- |
| `research_synthesis` | `truth synthesis [STATEMENT \| --question TEXT] [--limit N]` |
| `research_search` | `truth index search WORDS [--limit N]` |
| `research_brief` | `truth brief (TARGET \| --question TEXT) [--issues-from SNAPSHOT]` |
| `research_novelty_check` | `truth novelty (TEXT \| --statement ID) [--issues-from SNAPSHOT]` |
| `research_dossier` | `truth dossier STATEMENT [--issues-from OPEN-ISSUES]` |
| `research_context` | `truth context TARGET` |
| `research_related` | `truth related STATEMENT` |
| `research_semantics` | `truth semantics TARGET` or `truth semantics [--premise P]... --conclusion C [--definition D]... [--bridge B]...` (at most 12 each of premises, definitions and bridges) |
| `research_inspect` | `truth inspect ID` |
| `research_history` | `truth issues --from OPEN-ISSUES --for ID` |

Call `research_synthesis` with no arguments for the current God-existence case. For a particular question, pass `{"question":"Does one source give being to every actual recipient?","limit":2}`. Each matching judgment names its assessed statements. Passing one of their IDs as `target` brings up its support routes and their shared premises.

Every result starts with its binding: repository commit and commit time, the
exact command, and the issue snapshot's capture time and size, or "unknown"
when none is loaded. A failed refresh is shown as a stale-data warning.
Results are advisory retrieval with the CLI's own boundaries; a missing hit is
not evidence that no prior work exists. Text output only, capped at
`TRUTH_MCP_MAX_OUTPUT` bytes (default 60,000; the `--json` form of `brief` is
tens of megabytes).

## Security model

- Read-only: no paths, shells, writes, builds or source materialization. Tool
  arguments are passed as separate argv entries, may not start with `-`, are
  length-limited and closed by `additionalProperties: false`.
- One `truth` run at a time (each loads the corpus, up to about 700 MB), at most
  four queued callers, 120 s per call, 20 calls per minute globally; Traefik adds
  30 requests per minute per client IP.
- Requests with an `Origin` header are rejected unless listed in
  `TRUTH_MCP_ALLOWED_ORIGINS` (DNS-rebinding guard).
- Auth: the repository and its issues are public, so the deployment currently
  runs with `TRUTH_MCP_NO_AUTH=1`. Setting `TRUTH_MCP_TOKEN` (32+ characters)
  in place of it requires `Authorization: Bearer <token>`. The server refuses to
  start with neither.

## Data and refresh

The image contains only the binaries. `deploy/truth-mcp/refresh.sh` clones the
public repository into the `/data` volume and, every `TRUTH_MCP_REFRESH_SECS`
(default 3600), fetches `main` (`prepare`, while calls continue), then resets the
checkout and rebuilds the note index (`apply`, while no call runs). With
`GH_TOKEN` set (a fine-grained token with public-repository read access only), it
also downloads an issue/PR snapshot: a derived cache, never research authority.

## Deployment

```bash
deploy/truth-mcp/deploy.sh hetzner        # build locally, ship image, install, restart
deploy/truth-mcp/deploy.sh cert hetzner   # once DNS for mcp.moenarch.com points at the host
```

The script installs `/opt/truth-mcp/compose.yml` (container on
`dokploy-network`, read-only root, 1.5 GB memory limit), the Traefik route
`/etc/dokploy/traefik/dynamic/truth-mcp.yml` and a certbot deploy hook that
copies the certificate into Traefik's directory. Configuration lives in
`/opt/truth-mcp/env` on the host.

Smoke test:

```bash
curl -s https://mcp.moenarch.com/healthz
curl -s https://mcp.moenarch.com/mcp -H 'Content-Type: application/json' \
  -d '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"research_search","arguments":{"query":"fourth way","limit":3}}}'
ssh hetzner docker logs --tail 20 truth-mcp
```

Add it to a client, e.g. `claude mcp add --transport http truth-core https://mcp.moenarch.com/mcp`,
or exercise it with the MCP Inspector:

```bash
bunx @modelcontextprotocol/inspector@0.17.2 --cli https://mcp.moenarch.com/mcp --transport http \
  --method tools/call --tool-name research_novelty_check --tool-arg 'text=contingent beings depend on a necessary being'
```

Tool results are text only. Clients that receive `structuredContent` may show
the model only that, so the binding stays in the text header.

CI runs the adapter's unit tests offline; it never deploys or calls the server.
