# Build from the repository root:
#   docker build -f deploy/truth-mcp/Dockerfile -t truth-mcp .
# The image holds only the two binaries; the server clones the public
# repository into /data at runtime (deploy/truth-mcp/refresh.sh).
FROM rust:1-bookworm@sha256:75d26c23c24cc6ea1cdabf0714a6bff8fd7bf3248716043fd7ae86dac7f41b94 AS build
WORKDIR /src
COPY Cargo.toml Cargo.lock ./
COPY truth truth
COPY truth-mcp truth-mcp
RUN cargo build --locked --release -p truth -p truth-mcp

FROM debian:bookworm-slim@sha256:e67eeead736ff7bbe258ef088bff683635c561b1fcfefad0806c1df4ab49ce0e
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates git gh jq curl \
 && rm -rf /var/lib/apt/lists/* \
 && useradd --system --uid 10001 --home-dir /data truth \
 && mkdir -p /data && chown truth /data
COPY --from=build /src/target/release/truth /src/target/release/truth-mcp /usr/local/bin/
COPY deploy/truth-mcp/refresh.sh /usr/local/bin/truth-mcp-refresh
USER truth
ENV TRUTH_BIN=/usr/local/bin/truth \
    TRUTH_ROOT=/data/checkout \
    TRUTH_MCP_STATE=/data/state \
    TRUTH_MCP_REFRESH_CMD=/usr/local/bin/truth-mcp-refresh \
    TRUTH_MCP_ADDR=0.0.0.0:8765
VOLUME /data
EXPOSE 8765
HEALTHCHECK --interval=60s --timeout=5s --start-period=600s \
  CMD curl -fsS http://127.0.0.1:8765/healthz > /dev/null || exit 1
ENTRYPOINT ["truth-mcp"]
