//! Minimal HTTP/1.1 front for the MCP Streamable HTTP transport: stateless
//! JSON responses on `POST /mcp`, `GET /healthz`, one request per connection.

use crate::mcp;
use crate::runner::State;
use serde_json::{Value, json};
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::Duration;

const MAX_CONNECTIONS: usize = 32;
const MAX_HEADER_BYTES: usize = 16 * 1024;
const MAX_BODY_BYTES: usize = 64 * 1024;

struct Request {
    method: String,
    path: String,
    headers: Vec<(String, String)>,
    body: Vec<u8>,
}

impl Request {
    fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(key, _)| key.eq_ignore_ascii_case(name))
            .map(|(_, value)| value.as_str())
    }
}

struct Response {
    status: u16,
    body: Vec<u8>,
    extra: Vec<(&'static str, String)>,
}

impl Response {
    fn json(status: u16, value: &Value) -> Self {
        Response {
            status,
            body: value.to_string().into_bytes(),
            extra: Vec::new(),
        }
    }

    fn error(status: u16, message: &str) -> Self {
        Self::json(status, &json!({ "error": message }))
    }

    fn with(mut self, name: &'static str, value: impl Into<String>) -> Self {
        self.extra.push((name, value.into()));
        self
    }
}

pub fn serve(state: Arc<State>) {
    let listener = TcpListener::bind(&state.config.addr).unwrap_or_else(|e| {
        eprintln!("truth-mcp: cannot listen on {}: {e}", state.config.addr);
        std::process::exit(2);
    });
    eprintln!(
        "truth-mcp: listening on {} (root {}, auth {})",
        state.config.addr,
        state.config.root.display(),
        if state.config.token.is_some() {
            "bearer"
        } else {
            "DISABLED"
        }
    );
    let active = Arc::new(AtomicUsize::new(0));
    for stream in listener.incoming() {
        let Ok(mut stream) = stream else { continue };
        if active.fetch_add(1, Ordering::SeqCst) >= MAX_CONNECTIONS {
            active.fetch_sub(1, Ordering::SeqCst);
            let _ = write_response(&mut stream, Response::error(503, "too many connections"));
            continue;
        }
        let (state, active) = (Arc::clone(&state), Arc::clone(&active));
        thread::spawn(move || {
            handle(stream, &state);
            active.fetch_sub(1, Ordering::SeqCst);
        });
    }
}

fn handle(mut stream: TcpStream, state: &State) {
    let _ = stream.set_read_timeout(Some(Duration::from_secs(20)));
    let _ = stream.set_write_timeout(Some(Duration::from_secs(20)));
    let response = match read_request(&stream) {
        Ok(request) => route(&request, state),
        Err(response) => response,
    };
    let _ = write_response(&mut stream, response);
}

fn read_request(stream: &TcpStream) -> Result<Request, Response> {
    let mut reader = BufReader::new(stream.take((MAX_HEADER_BYTES + MAX_BODY_BYTES) as u64));
    let mut head_bytes = 0;
    let mut line = String::new();
    let mut next_line = |reader: &mut BufReader<_>| -> Result<String, Response> {
        line.clear();
        let read = reader
            .read_line(&mut line)
            .map_err(|_| Response::error(400, "unreadable request"))?;
        head_bytes += read;
        if read == 0 || head_bytes > MAX_HEADER_BYTES {
            return Err(Response::error(431, "request head too large or truncated"));
        }
        Ok(line.trim_end_matches(['\r', '\n']).to_string())
    };
    let request_line = next_line(&mut reader)?;
    let mut parts = request_line.split(' ');
    let (Some(method), Some(target), Some(_version)) = (parts.next(), parts.next(), parts.next())
    else {
        return Err(Response::error(400, "malformed request line"));
    };
    let path = target.split('?').next().unwrap_or("").to_string();
    let method = method.to_string();
    let mut headers = Vec::new();
    loop {
        let header = next_line(&mut reader)?;
        if header.is_empty() {
            break;
        }
        let Some((name, value)) = header.split_once(':') else {
            return Err(Response::error(400, "malformed header"));
        };
        headers.push((name.trim().to_string(), value.trim().to_string()));
    }
    let mut request = Request {
        method,
        path,
        headers,
        body: Vec::new(),
    };
    if request.header("transfer-encoding").is_some() {
        return Err(Response::error(411, "send a Content-Length body"));
    }
    let length: usize = match request.header("content-length") {
        None => 0,
        Some(value) => value
            .parse()
            .map_err(|_| Response::error(400, "bad Content-Length"))?,
    };
    if length > MAX_BODY_BYTES {
        return Err(Response::error(413, "request body too large"));
    }
    request.body.resize(length, 0);
    reader
        .read_exact(&mut request.body)
        .map_err(|_| Response::error(400, "truncated body"))?;
    Ok(request)
}

fn authorized(request: &Request, state: &State) -> bool {
    let Some(expected) = &state.config.token else {
        return true;
    };
    let Some(given) = request
        .header("authorization")
        .and_then(|value| value.strip_prefix("Bearer "))
    else {
        return false;
    };
    let (given, expected) = (given.trim().as_bytes(), expected.as_bytes());
    // Constant time in the token's content.
    given.len() == expected.len()
        && given
            .iter()
            .zip(expected)
            .fold(0u8, |acc, (a, b)| acc | (a ^ b))
            == 0
}

fn route(request: &Request, state: &State) -> Response {
    match (request.method.as_str(), request.path.as_str()) {
        ("GET", "/healthz") => {
            let binding = state.binding();
            let status = if binding.head.is_some() { 200 } else { 503 };
            Response::json(
                status,
                &json!({
                    "status": if status == 200 { "ok" } else { "no checkout" },
                    "head": binding.head,
                    "head_time": binding.head_time,
                    "issue_snapshot_captured_at": binding.snapshot_captured_at,
                    "refreshed_at": binding.refreshed_at,
                    "refresh_error": binding.refresh_error,
                }),
            )
        }
        (_, "/mcp") => {
            // DNS-rebinding guard required by the MCP transport: browsers send
            // Origin, agent clients do not.
            if let Some(origin) = request.header("origin")
                && !state
                    .config
                    .allowed_origins
                    .iter()
                    .any(|allowed| allowed == origin)
            {
                return Response::error(403, "origin not allowed");
            }
            if !authorized(request, state) {
                return Response::error(401, "missing or invalid bearer token")
                    .with("WWW-Authenticate", "Bearer realm=\"truth-mcp\"");
            }
            if request.method != "POST" {
                // No server-initiated stream: GET/DELETE are not offered.
                return Response::error(405, "use POST").with("Allow", "POST");
            }
            match mcp::handle(state, &request.body) {
                Some(reply) => Response::json(200, &reply),
                None => Response {
                    status: 202,
                    body: Vec::new(),
                    extra: Vec::new(),
                },
            }
        }
        _ => Response::error(404, "not found"),
    }
}

fn write_response(stream: &mut TcpStream, response: Response) -> std::io::Result<()> {
    let reason = match response.status {
        200 => "OK",
        202 => "Accepted",
        400 => "Bad Request",
        401 => "Unauthorized",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        411 => "Length Required",
        413 => "Payload Too Large",
        431 => "Request Header Fields Too Large",
        _ => "Service Unavailable",
    };
    let mut head = format!(
        "HTTP/1.1 {} {reason}\r\nContent-Length: {}\r\nConnection: close\r\nCache-Control: no-store\r\n",
        response.status,
        response.body.len()
    );
    if !response.body.is_empty() {
        head.push_str("Content-Type: application/json\r\n");
    }
    for (name, value) in &response.extra {
        head.push_str(&format!("{name}: {value}\r\n"));
    }
    head.push_str("\r\n");
    stream.write_all(head.as_bytes())?;
    stream.write_all(&response.body)?;
    stream.flush()
}
