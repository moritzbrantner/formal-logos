//! JSON-RPC methods and the read-only research tools.
//!
//! Each tool maps validated arguments to one fixed `truth` command. Arguments
//! are passed as separate argv entries (no shell) and may not start with `-`,
//! so a caller cannot add options, paths or other subcommands.

use crate::runner::State;
use serde_json::{Map, Value, json};
use std::time::Instant;

const PROTOCOL_VERSIONS: [&str; 3] = ["2025-11-25", "2025-06-18", "2025-03-26"];

const INSTRUCTIONS: &str = "Read-only retrieval over the Truth Core research corpus \
(statements, arguments, Lean-verified results, attempts, notes and an offline GitHub \
issue/PR snapshot). Every result names the repository commit and the issue snapshot it \
was computed from. The output is advisory retrieval, not a verdict: keep formal Lean \
consequence, recorded provisional judgments, source attribution and issue/work status \
distinct; a missing hit or 'no-match-found' is not evidence that no prior work exists, \
and an unknown or stale issue snapshot is stated explicitly. IDs may be uuids, legacy \
ids (STMT-...) or labels. Start with research_search or research_brief.";

type Builder = fn(&Map<String, Value>, &State) -> Result<Vec<String>, String>;

struct Tool {
    name: &'static str,
    description: &'static str,
    schema: fn() -> Value,
    build: Builder,
}

fn limit_schema() -> Value {
    json!({ "type": "integer", "minimum": 1, "maximum": 20, "description": "Entries per section (default 6)." })
}

fn id_schema(what: &str) -> Value {
    json!({ "type": "string", "maxLength": 300, "description": what })
}

const TOOLS: &[Tool] = &[
    Tool {
        name: "research_search",
        description: "Full-text search over corpus records and research notes (`truth index search`). \
Returns ranked records and note sections with their IDs and paths.",
        schema: || {
            json!({ "type": "object", "required": ["query"], "additionalProperties": false, "properties": {
                "query": { "type": "string", "maxLength": 300, "description": "Search words." },
                "limit": limit_schema() } })
        },
        build: |args, _| {
            let query = text(args, "query", 300)?.ok_or("query is required")?;
            let mut argv = vec!["index".into(), "search".into()];
            // Each word becomes its own argv entry, so no word may look like an option.
            let words: Vec<&str> = query
                .split_whitespace()
                .filter(|word| !word.starts_with('-'))
                .collect();
            if words.is_empty() {
                return Err("query has no search words".into());
            }
            argv.extend(words.into_iter().map(str::to_string));
            argv.extend(limit(args)?);
            Ok(argv)
        },
    },
    Tool {
        name: "research_brief",
        description: "Research brief (`truth brief`): for a corpus ID, or for a free-text question, the \
relevant notes, recorded assessments, rivals, conditional results, git history and issue/PR history, \
with the evidence boundary of each. Give exactly one of `target` or `question`.",
        schema: || {
            json!({ "type": "object", "additionalProperties": false, "properties": {
                "target": id_schema("Statement, argument, result or other record ID or label."),
                "question": { "type": "string", "maxLength": 1000, "description": "Free-text research question." },
                "limit": limit_schema() } })
        },
        build: |args, state| {
            let mut argv = vec!["brief".to_string()];
            match (text(args, "target", 300)?, text(args, "question", 1000)?) {
                (Some(target), None) => argv.push(target),
                (None, Some(question)) => argv.extend(["--question".into(), question]),
                _ => return Err("give exactly one of target or question".into()),
            }
            argv.extend(limit(args)?);
            argv.extend(snapshot(state));
            Ok(argv)
        },
    },
    Tool {
        name: "research_novelty_check",
        description: "Advisory prior-work check (`truth novelty`) for a proposed claim, theorem or \
connection: classifies it as already-recorded, partially-recorded or no-match-found (never 'novel') \
and lists the hits with their evidence kind. Give exactly one of `text` or `statement` (an existing \
statement checked against everything else).",
        schema: || {
            json!({ "type": "object", "additionalProperties": false, "properties": {
                "text": { "type": "string", "maxLength": 1000, "description": "Proposed claim or connection." },
                "statement": id_schema("Existing statement ID or label."),
                "limit": limit_schema() } })
        },
        build: |args, state| {
            let mut argv = vec!["novelty".to_string()];
            match (text(args, "text", 1000)?, text(args, "statement", 300)?) {
                (Some(claim), None) => argv.push(claim),
                (None, Some(statement)) => argv.extend(["--statement".into(), statement]),
                _ => return Err("give exactly one of text or statement".into()),
            }
            argv.extend(limit(args)?);
            argv.extend(snapshot(state));
            Ok(argv)
        },
    },
    Tool {
        name: "research_dossier",
        description: "Premise dossier (`truth dossier`): a statement's frontier status, supporting and \
opposing arguments, rivals, claims, attempts and targeting issues.",
        schema: || {
            json!({ "type": "object", "required": ["statement"], "additionalProperties": false, "properties": {
                "statement": id_schema("Statement ID or label."), "limit": limit_schema() } })
        },
        build: |args, state| {
            let statement = text(args, "statement", 300)?.ok_or("statement is required")?;
            let mut argv = vec!["dossier".into(), statement];
            argv.extend(limit(args)?);
            if state.config.open_issues.is_file() {
                argv.extend([
                    "--issues-from".into(),
                    state.config.open_issues.display().to_string(),
                ]);
            }
            Ok(argv)
        },
    },
    Tool {
        name: "research_context",
        description: "Context pack for an argument or result (`truth context`): the frozen Lean \
statement, premise status, other routes, countermodels, attempts and open work. A statement \
concluded by several arguments is reported as ambiguous with the candidate argument IDs.",
        schema: || {
            json!({ "type": "object", "required": ["target"], "additionalProperties": false, "properties": {
                "target": id_schema("Argument or result ID or label."), "limit": limit_schema() } })
        },
        build: |args, _| {
            let target = text(args, "target", 300)?.ok_or("target is required")?;
            let mut argv = vec!["context".into(), target];
            argv.extend(limit(args)?);
            Ok(argv)
        },
    },
    Tool {
        name: "research_related",
        description: "Propositions, argument bundles and attempts related to a statement (`truth related`). \
Rankings are discovery aids, not equivalence or implication.",
        schema: || {
            json!({ "type": "object", "required": ["statement"], "additionalProperties": false, "properties": {
                "statement": id_schema("Statement ID or label."), "limit": limit_schema() } })
        },
        build: |args, _| {
            let statement = text(args, "statement", 300)?.ok_or("statement is required")?;
            let mut argv = vec!["related".into(), statement];
            argv.extend(limit(args)?);
            Ok(argv)
        },
    },
    Tool {
        name: "research_semantics",
        description: "Semantic dependencies and equivocation check (`truth semantics`). With `target` \
(statement, argument or result): its definitions with formal status, disambiguations, the senses it \
uses, and for each connected argument the senses per term with the statements carrying them and a \
verdict (single sense, bridged, allowlisted legacy mixing, mixing control, unbridged). With `premises` \
and `conclusion` (and optional `bridges`, each STATEMENT or STATEMENT@SENSE,SENSE): a preflight of the \
candidate argument judged as `truth check` judges a new argument, naming unbridged sense mixing and the \
bridges it would need. Give `target` or `premises` + `conclusion`, not both.",
        schema: || {
            let ids = |what: &str| json!({ "type": "array", "maxItems": MAX_LIST, "items": id_schema(what), "description": what });
            json!({ "type": "object", "additionalProperties": false, "properties": {
                "target": id_schema("Statement, argument or result ID or label."),
                "premises": ids("Premise statement IDs or labels of a candidate argument."),
                "conclusion": id_schema("Conclusion statement ID or label of a candidate argument."),
                "bridges": ids("Candidate sense-bridge statements: STATEMENT or STATEMENT@SENSE,SENSE."),
                "limit": limit_schema() } })
        },
        build: |args, _| {
            let target = text(args, "target", 300)?;
            let premises = texts(args, "premises", 300)?;
            let conclusion = text(args, "conclusion", 300)?;
            let bridges = texts(args, "bridges", 300)?;
            let mut argv = vec!["semantics".to_string()];
            match (target, conclusion) {
                (Some(target), None) if premises.is_empty() && bridges.is_empty() => {
                    argv.push(target);
                    argv.extend(limit(args)?);
                }
                (None, Some(conclusion)) => {
                    if !limit(args)?.is_empty() {
                        return Err("limit applies only to target".into());
                    }
                    for premise in premises {
                        argv.extend(["--premise".into(), premise]);
                    }
                    argv.extend(["--conclusion".into(), conclusion]);
                    for bridge in bridges {
                        argv.extend(["--bridge".into(), bridge]);
                    }
                }
                _ => return Err("give either target, or premises and conclusion".into()),
            }
            Ok(argv)
        },
    },
    Tool {
        name: "research_inspect",
        description: "One corpus record by ID or label (`truth inspect`), with its resolved references.",
        schema: || {
            json!({ "type": "object", "required": ["id"], "additionalProperties": false, "properties": {
                "id": id_schema("Any record ID, legacy id or label.") } })
        },
        build: |args, _| {
            Ok(vec![
                "inspect".into(),
                text(args, "id", 300)?.ok_or("id is required")?,
            ])
        },
    },
    Tool {
        name: "research_history",
        description: "Open GitHub issues whose acceptance blocks name a record (`truth issues --for`), \
from the server's offline issue snapshot.",
        schema: || {
            json!({ "type": "object", "required": ["id"], "additionalProperties": false, "properties": {
                "id": id_schema("Result, statement, configuration, attempt or argument ID or label.") } })
        },
        build: |args, state| {
            let id = text(args, "id", 300)?.ok_or("id is required")?;
            if !state.config.open_issues.is_file() {
                return Err(
                    "no issue snapshot is loaded on this server; issue history is unknown".into(),
                );
            }
            Ok(vec![
                "issues".into(),
                "--from".into(),
                state.config.open_issues.display().to_string(),
                "--for".into(),
                id,
            ])
        },
    },
];

fn text(args: &Map<String, Value>, key: &str, max_chars: usize) -> Result<Option<String>, String> {
    let Some(value) = args.get(key) else {
        return Ok(None);
    };
    let Some(value) = value.as_str().map(str::trim) else {
        return Err(format!("{key} must be a string"));
    };
    if value.is_empty() {
        return Ok(None);
    }
    if value.chars().count() > max_chars {
        return Err(format!("{key} is longer than {max_chars} characters"));
    }
    if value.starts_with('-') {
        return Err(format!("{key} may not start with '-'"));
    }
    if value.chars().any(char::is_control) {
        return Err(format!("{key} may not contain control characters"));
    }
    Ok(Some(value.to_string()))
}

/// The most entries a list argument may hold.
const MAX_LIST: usize = 12;

/// A list of strings, each validated as [`text`]; empty entries are dropped.
fn texts(args: &Map<String, Value>, key: &str, max_chars: usize) -> Result<Vec<String>, String> {
    let items = match args.get(key) {
        None | Some(Value::Null) => return Ok(Vec::new()),
        Some(Value::Array(items)) => items,
        Some(_) => return Err(format!("{key} must be an array of strings")),
    };
    if items.len() > MAX_LIST {
        return Err(format!("{key} has more than {MAX_LIST} entries"));
    }
    let mut out = Vec::new();
    for item in items {
        let mut one = Map::new();
        one.insert(key.to_string(), item.clone());
        out.extend(text(&one, key, max_chars)?);
    }
    Ok(out)
}

fn limit(args: &Map<String, Value>) -> Result<Vec<String>, String> {
    match args.get("limit") {
        None | Some(Value::Null) => Ok(Vec::new()),
        Some(value) => match value.as_u64() {
            Some(n @ 1..=20) => Ok(vec!["--limit".into(), n.to_string()]),
            _ => Err("limit must be an integer from 1 to 20".into()),
        },
    }
}

fn snapshot(state: &State) -> Vec<String> {
    if state.has_snapshot() {
        vec![
            "--issues-from".into(),
            state.config.snapshot.display().to_string(),
        ]
    } else {
        Vec::new()
    }
}

fn reply(id: &Value, result: Value) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "result": result })
}

fn error(id: &Value, code: i64, message: &str) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "error": { "code": code, "message": message } })
}

/// Handles one JSON-RPC message; `None` for notifications and client responses (HTTP 202).
pub fn handle(state: &State, body: &[u8]) -> Option<Value> {
    let message: Value = match serde_json::from_slice(body) {
        Ok(message) => message,
        Err(_) => return Some(error(&Value::Null, -32700, "parse error")),
    };
    let Some(message) = message.as_object() else {
        return Some(error(
            &Value::Null,
            -32600,
            "expected one JSON-RPC request object (no batches)",
        ));
    };
    let id = message.get("id")?;
    let method = message.get("method").and_then(Value::as_str)?;
    let params = message
        .get("params")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    Some(match method {
        "initialize" => {
            let requested = params
                .get("protocolVersion")
                .and_then(Value::as_str)
                .unwrap_or("");
            let version = PROTOCOL_VERSIONS
                .iter()
                .find(|v| **v == requested)
                .unwrap_or(&PROTOCOL_VERSIONS[0]);
            reply(
                id,
                json!({
                    "protocolVersion": version,
                    "capabilities": { "tools": { "listChanged": false } },
                    "serverInfo": { "name": "truth-core-research", "version": env!("CARGO_PKG_VERSION") },
                    "instructions": INSTRUCTIONS,
                }),
            )
        }
        "ping" => reply(id, json!({})),
        "tools/list" => reply(
            id,
            json!({ "tools": TOOLS.iter().map(|tool| json!({
                "name": tool.name,
                "description": tool.description,
                "inputSchema": (tool.schema)(),
                "annotations": { "readOnlyHint": true, "destructiveHint": false, "idempotentHint": true, "openWorldHint": false },
            })).collect::<Vec<_>>() }),
        ),
        "tools/call" => call(state, id, &params),
        _ => error(id, -32601, "method not found"),
    })
}

/// Text only: clients that receive `structuredContent` may show the model that
/// instead of the text, so the binding lives in the text header.
fn tool_result(text: String, is_error: bool) -> Value {
    json!({ "content": [{ "type": "text", "text": text }], "isError": is_error })
}

fn call(state: &State, id: &Value, params: &Map<String, Value>) -> Value {
    let name = params.get("name").and_then(Value::as_str).unwrap_or("");
    let Some(tool) = TOOLS.iter().find(|tool| tool.name == name) else {
        return error(id, -32602, &format!("unknown tool {name:?}"));
    };
    let args = match params.get("arguments") {
        None | Some(Value::Null) => Map::new(),
        Some(Value::Object(args)) => args.clone(),
        Some(_) => return error(id, -32602, "arguments must be an object"),
    };
    if let Some(key) = args
        .keys()
        .find(|key| !(tool.schema)()["properties"].get(key.as_str()).is_some())
    {
        return reply(id, tool_result(format!("unknown argument {key:?}"), true));
    }
    let argv = match (tool.build)(&args, state) {
        Ok(argv) => argv,
        Err(message) => return reply(id, tool_result(message, true)),
    };
    if !state.take_rate_token() {
        return reply(
            id,
            tool_result("rate limit reached; retry in a minute".into(), true),
        );
    }
    let started = Instant::now();
    let outcome = state.run_truth(&argv);
    let binding = state.binding();
    let command = format!(
        "truth {}",
        argv.join(" ")
            .replace(
                &state.config.snapshot.display().to_string(),
                "<issue-snapshot>"
            )
            .replace(
                &state.config.open_issues.display().to_string(),
                "<open-issues>"
            )
    );
    eprintln!(
        "truth-mcp: {} {} in {:.1} s: {}",
        tool.name,
        match &outcome {
            Ok(output) => format!("exit {:?}", output.code),
            Err(message) => message.clone(),
        },
        started.elapsed().as_secs_f64(),
        command
    );
    let snapshot_line = match (&binding.snapshot_captured_at, binding.snapshot_items) {
        (Some(at), Some(items)) => format!("captured {at}, {items} issues and PRs"),
        _ => "unknown: no snapshot loaded, so issue history is not searched".into(),
    };
    let mut header = format!(
        "[truth-core research · read-only · advisory retrieval]\nrepository: {} @ {} ({})\ncommand: {command}\nissue snapshot: {snapshot_line}\n",
        state.config.repo_url,
        binding.head.as_deref().unwrap_or("unknown"),
        binding.head_time.as_deref().unwrap_or("unknown time"),
    );
    if let Some(error) = &binding.refresh_error {
        header.push_str(&format!(
            "WARNING last refresh failed, data may be stale: {error}\n"
        ));
    }
    header.push_str("---\n");
    match outcome {
        Err(message) => reply(id, tool_result(format!("{header}{message}"), true)),
        Ok(output) => {
            let failed = output.code != Some(0);
            let mut text = header + &output.stdout;
            if output.truncated {
                text.push_str(&format!(
                    "\n[output truncated at {} bytes; lower `limit` or narrow the query]\n",
                    state.config.max_output
                ));
            }
            if failed {
                text.push_str(&format!(
                    "\n[truth exited with {:?}]\n{}",
                    output.code,
                    output.stderr.trim()
                ));
            }
            reply(id, tool_result(text, failed))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runner::Config;
    use std::path::PathBuf;
    use std::time::Duration;

    fn state() -> State {
        State::new(Config {
            addr: "127.0.0.1:0".into(),
            token: None,
            allowed_origins: Vec::new(),
            truth_bin: PathBuf::from("/nonexistent/truth"),
            root: PathBuf::from("/nonexistent/root"),
            repo_url: "https://example.invalid/repo".into(),
            snapshot: PathBuf::from("/nonexistent/issues-snapshot.json"),
            open_issues: PathBuf::from("/nonexistent/issues-open.json"),
            refresh_cmd: None,
            refresh_interval: Duration::from_secs(3600),
            call_timeout: Duration::from_secs(5),
            max_output: 1_000,
            calls_per_minute: 20.0,
        })
    }

    fn rpc(state: &State, request: Value) -> Option<Value> {
        handle(state, request.to_string().as_bytes())
    }

    fn call_tool(state: &State, name: &str, arguments: Value) -> Value {
        let request = json!({"jsonrpc": "2.0", "id": 1, "method": "tools/call",
            "params": {"name": name, "arguments": arguments}});
        rpc(state, request).expect("reply")
    }

    fn build(name: &str, arguments: Value) -> Result<Vec<String>, String> {
        let tool = TOOLS.iter().find(|tool| tool.name == name).expect("tool");
        (tool.build)(arguments.as_object().expect("object"), &state())
    }

    #[test]
    fn notifications_and_batches() {
        let state = state();
        assert!(
            rpc(
                &state,
                json!({"jsonrpc": "2.0", "method": "notifications/initialized"})
            )
            .is_none()
        );
        let batch = rpc(
            &state,
            json!([{"jsonrpc": "2.0", "id": 1, "method": "ping"}]),
        )
        .unwrap();
        assert_eq!(batch["error"]["code"], -32600);
        let parse = handle(&state, b"{not json").unwrap();
        assert_eq!(parse["error"]["code"], -32700);
    }

    #[test]
    fn initialize_negotiates_supported_version() {
        let state = state();
        let init = |version: &str| {
            rpc(
                &state,
                json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"protocolVersion": version}}),
            )
            .unwrap()["result"]["protocolVersion"]
                .clone()
        };
        assert_eq!(init("2025-06-18"), "2025-06-18");
        assert_eq!(init("1999-01-01"), PROTOCOL_VERSIONS[0]);
    }

    #[test]
    fn tools_are_read_only_and_schemas_close_arguments() {
        let reply = rpc(
            &state(),
            json!({"jsonrpc": "2.0", "id": 1, "method": "tools/list"}),
        )
        .unwrap();
        for tool in reply["result"]["tools"].as_array().unwrap() {
            assert_eq!(tool["annotations"]["readOnlyHint"], true);
            assert_eq!(tool["inputSchema"]["additionalProperties"], false);
        }
    }

    #[test]
    fn arguments_cannot_inject_options() {
        assert!(build("research_inspect", json!({"id": "--root=/etc"})).is_err());
        assert!(build("research_search", json!({"query": "a\u{0}b"})).is_err());
        assert!(build("research_brief", json!({"target": "X", "question": "Y"})).is_err());
        assert!(build("research_brief", json!({})).is_err());
        assert!(build("research_dossier", json!({"statement": "X", "limit": 21})).is_err());
        assert_eq!(
            build("research_search", json!({"query": "act --limit potency"})).unwrap(),
            ["index", "search", "act", "potency"]
        );
        assert_eq!(
            build(
                "research_brief",
                json!({"question": "is God necessary", "limit": 3})
            )
            .unwrap(),
            ["brief", "--question", "is God necessary", "--limit", "3"]
        );
        assert_eq!(
            build("research_inspect", json!({"id": "STMT-X"})).unwrap(),
            ["inspect", "STMT-X"]
        );
    }

    #[test]
    fn semantics_maps_target_or_preflight() {
        assert_eq!(
            build(
                "research_semantics",
                json!({"target": "STMT-X", "limit": 4})
            )
            .unwrap(),
            ["semantics", "STMT-X", "--limit", "4"]
        );
        assert_eq!(
            build(
                "research_semantics",
                json!({"premises": ["A", "B"], "conclusion": "C", "bridges": ["B@T_1,T_2"]})
            )
            .unwrap(),
            [
                "semantics",
                "--premise",
                "A",
                "--premise",
                "B",
                "--conclusion",
                "C",
                "--bridge",
                "B@T_1,T_2"
            ]
        );
        let reject = |arguments: Value| build("research_semantics", arguments).is_err();
        assert!(reject(json!({})));
        assert!(reject(json!({"target": "X", "conclusion": "C"})));
        assert!(reject(json!({"target": "X", "premises": ["A"]})));
        assert!(reject(json!({"premises": ["A"]})));
        assert!(reject(json!({"premises": ["--strict"], "conclusion": "C"})));
        assert!(reject(json!({"premises": "A", "conclusion": "C"})));
        assert!(reject(json!({"premises": [1], "conclusion": "C"})));
        assert!(reject(
            json!({"premises": vec!["A"; 13], "conclusion": "C"})
        ));
        assert!(reject(
            json!({"premises": ["A"], "conclusion": "C", "limit": 3})
        ));
    }

    #[test]
    fn missing_snapshot_is_reported_not_hidden() {
        let state = state();
        assert!(build("research_history", json!({"id": "STMT-X"})).is_err());
        let reply = call_tool(&state, "research_inspect", json!({"id": "STMT-X"}));
        let text = reply["result"]["content"][0]["text"].as_str().unwrap();
        assert!(text.contains("issue snapshot: unknown"), "{text}");
        assert_eq!(
            reply["result"]["isError"], true,
            "the nonexistent binary must fail visibly"
        );
    }

    #[test]
    fn unknown_tools_and_arguments_are_rejected() {
        let state = state();
        assert_eq!(
            call_tool(&state, "shell", json!({}))["error"]["code"],
            -32602
        );
        let reply = call_tool(
            &state,
            "research_inspect",
            json!({"id": "X", "path": "/etc"}),
        );
        assert_eq!(reply["result"]["isError"], true);
    }
}
