//! Read-only MCP endpoint over the `truth` research retrieval commands (#1645).
//!
//! The adapter adds no corpus, index or proof engine of its own: every tool
//! runs the `truth` binary on one checkout with a fixed argument vector and
//! returns its text output with the checkout and issue-snapshot binding. See
//! `docs/truth-mcp.md` for the tool list, security model and deployment.

mod http;
mod mcp;
mod runner;

use std::sync::Arc;

fn main() {
    let config = match runner::Config::from_env() {
        Ok(config) => config,
        Err(message) => {
            eprintln!("truth-mcp: {message}");
            std::process::exit(2);
        }
    };
    let state = Arc::new(runner::State::new(config));
    runner::start_refresh(Arc::clone(&state));
    http::serve(state);
}
