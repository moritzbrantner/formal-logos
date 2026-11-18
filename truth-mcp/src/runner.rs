//! Configuration, the serialized `truth` runner, input binding and refresh.

use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, RwLock};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// Environment variables a `truth` child must not inherit.
const SECRET_VARS: [&str; 3] = ["TRUTH_MCP_TOKEN", "GH_TOKEN", "GITHUB_TOKEN"];
/// Callers waiting for the runner beyond this count get a busy error.
const MAX_WAITERS: usize = 4;
const QUEUE_WAIT: Duration = Duration::from_secs(90);
const REFRESH_TIMEOUT: Duration = Duration::from_secs(1800);

pub struct Config {
    pub addr: String,
    /// `None` only when `TRUTH_MCP_NO_AUTH=1` (public read-only data; rate limits only).
    pub token: Option<String>,
    pub allowed_origins: Vec<String>,
    pub truth_bin: PathBuf,
    pub root: PathBuf,
    pub repo_url: String,
    /// `{"captured_at", "items"}` snapshot of all issues and PRs (brief, novelty).
    pub snapshot: PathBuf,
    /// `gh issue list --state open` array (dossier, issues).
    pub open_issues: PathBuf,
    pub refresh_cmd: Option<PathBuf>,
    pub refresh_interval: Duration,
    pub call_timeout: Duration,
    pub max_output: usize,
    pub calls_per_minute: f64,
}

fn env(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

fn env_number(name: &str, default: u64) -> Result<u64, String> {
    match env(name) {
        None => Ok(default),
        Some(value) => value
            .parse()
            .map_err(|_| format!("{name} must be a non-negative integer, got {value:?}")),
    }
}

impl Config {
    pub fn from_env() -> Result<Self, String> {
        let token = match (env("TRUTH_MCP_TOKEN"), env("TRUTH_MCP_NO_AUTH")) {
            (Some(token), _) if token.len() >= 32 => Some(token),
            (Some(_), _) => return Err("TRUTH_MCP_TOKEN must have at least 32 characters".into()),
            (None, Some(flag)) if flag == "1" => None,
            (None, _) => {
                return Err(
                    "set TRUTH_MCP_TOKEN or TRUTH_MCP_NO_AUTH=1 to serve without authentication"
                        .into(),
                );
            }
        };
        let root = PathBuf::from(env("TRUTH_ROOT").unwrap_or_else(|| ".".into()));
        let state_dir = env("TRUTH_MCP_STATE")
            .map(PathBuf::from)
            .unwrap_or_else(|| root.join(".cache"));
        Ok(Config {
            addr: env("TRUTH_MCP_ADDR").unwrap_or_else(|| "127.0.0.1:8765".into()),
            token,
            allowed_origins: env("TRUTH_MCP_ALLOWED_ORIGINS")
                .map(|list| {
                    list.split(',')
                        .map(|item| item.trim().to_string())
                        .filter(|item| !item.is_empty())
                        .collect()
                })
                .unwrap_or_default(),
            truth_bin: PathBuf::from(env("TRUTH_BIN").unwrap_or_else(|| "truth".into())),
            repo_url: env("TRUTH_MCP_REPO_URL")
                .unwrap_or_else(|| "https://github.com/moritzbrantner/formal-logos".into()),
            snapshot: state_dir.join("issues-snapshot.json"),
            open_issues: state_dir.join("issues-open.json"),
            root,
            refresh_cmd: env("TRUTH_MCP_REFRESH_CMD").map(PathBuf::from),
            refresh_interval: Duration::from_secs(
                env_number("TRUTH_MCP_REFRESH_SECS", 3600)?.max(60),
            ),
            call_timeout: Duration::from_secs(
                env_number("TRUTH_MCP_CALL_TIMEOUT_SECS", 120)?.max(1),
            ),
            max_output: env_number("TRUTH_MCP_MAX_OUTPUT", 60_000)?.clamp(1_000, 1_000_000)
                as usize,
            calls_per_minute: env_number("TRUTH_MCP_CALLS_PER_MINUTE", 20)?.max(1) as f64,
        })
    }
}

/// What the answers are computed from; every tool result reports it.
#[derive(Clone, Default)]
pub struct Binding {
    pub head: Option<String>,
    pub head_time: Option<String>,
    pub snapshot_captured_at: Option<String>,
    pub snapshot_items: Option<usize>,
    pub refreshed_at: Option<String>,
    pub refresh_error: Option<String>,
}

pub struct Output {
    pub code: Option<i32>,
    pub stdout: String,
    pub stderr: String,
    pub truncated: bool,
}

struct Bucket {
    tokens: f64,
    last: Instant,
}

pub struct State {
    pub config: Config,
    exec: Mutex<()>,
    waiters: AtomicUsize,
    binding: RwLock<Binding>,
    rate: Mutex<Bucket>,
}

impl State {
    pub fn new(config: Config) -> Self {
        let rate = Bucket {
            tokens: config.calls_per_minute,
            last: Instant::now(),
        };
        let state = State {
            config,
            exec: Mutex::new(()),
            waiters: AtomicUsize::new(0),
            binding: RwLock::new(Binding::default()),
            rate: Mutex::new(rate),
        };
        state.reload_binding(None);
        state
    }

    pub fn binding(&self) -> Binding {
        self.binding
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    pub fn has_snapshot(&self) -> bool {
        self.config.snapshot.is_file()
    }

    /// Takes one call from the global bucket (`calls_per_minute`, refilled continuously).
    pub fn take_rate_token(&self) -> bool {
        let mut bucket = self.rate.lock().unwrap_or_else(|e| e.into_inner());
        let capacity = self.config.calls_per_minute;
        let now = Instant::now();
        let refill = now.duration_since(bucket.last).as_secs_f64() * capacity / 60.0;
        bucket.tokens = (bucket.tokens + refill).min(capacity);
        bucket.last = now;
        if bucket.tokens >= 1.0 {
            bucket.tokens -= 1.0;
            true
        } else {
            false
        }
    }

    fn acquire(&self, wait: Duration) -> Result<MutexGuard<'_, ()>, String> {
        if self.waiters.fetch_add(1, Ordering::SeqCst) >= MAX_WAITERS {
            self.waiters.fetch_sub(1, Ordering::SeqCst);
            return Err("server busy: too many queued research calls; retry shortly".into());
        }
        let deadline = Instant::now() + wait;
        let result = loop {
            match self.exec.try_lock() {
                Ok(guard) => break Ok(guard),
                Err(std::sync::TryLockError::Poisoned(e)) => break Ok(e.into_inner()),
                Err(std::sync::TryLockError::WouldBlock) if Instant::now() < deadline => {
                    thread::sleep(Duration::from_millis(100))
                }
                Err(std::sync::TryLockError::WouldBlock) => {
                    break Err(
                        "server busy: the research runner is occupied; retry shortly".into(),
                    );
                }
            }
        };
        self.waiters.fetch_sub(1, Ordering::SeqCst);
        result
    }

    /// Runs `truth --root ROOT ARGS...` alone: one corpus load at a time keeps
    /// memory bounded, and a refresh never changes the checkout mid-call.
    pub fn run_truth(&self, args: &[String]) -> Result<Output, String> {
        let _guard = self.acquire(QUEUE_WAIT)?;
        let mut command = Command::new(&self.config.truth_bin);
        command.arg("--root").arg(&self.config.root).args(args);
        for name in SECRET_VARS {
            command.env_remove(name);
        }
        run(command, self.config.call_timeout, self.config.max_output)
    }

    fn reload_binding(&self, refresh: Option<Result<(), String>>) {
        let mut binding = Binding::default();
        let log = Command::new("git")
            .arg("-C")
            .arg(&self.config.root)
            .args(["log", "-1", "--format=%H%n%cI"])
            .stderr(Stdio::null())
            .output();
        if let Some(log) = log.ok().filter(|log| log.status.success()) {
            let text = String::from_utf8_lossy(&log.stdout).into_owned();
            let mut lines = text.lines();
            binding.head = lines.next().map(str::to_string);
            binding.head_time = lines.next().map(str::to_string);
        }
        if let Ok(bytes) = std::fs::read(&self.config.snapshot)
            && let Ok(value) = serde_json::from_slice::<serde_json::Value>(&bytes)
        {
            binding.snapshot_captured_at = value
                .get("captured_at")
                .and_then(|v| v.as_str())
                .map(str::to_string);
            binding.snapshot_items = value.get("items").and_then(|v| v.as_array()).map(Vec::len);
        }
        let previous = self.binding();
        match refresh {
            None => {
                binding.refreshed_at = previous.refreshed_at;
                binding.refresh_error = previous.refresh_error;
            }
            Some(Ok(())) => binding.refreshed_at = Some(now_iso()),
            Some(Err(message)) => {
                binding.refreshed_at = previous.refreshed_at;
                binding.refresh_error = Some(format!("{} at {}", message, now_iso()));
            }
        }
        *self.binding.write().unwrap_or_else(|e| e.into_inner()) = binding;
    }

    fn refresh_phase(&self, command_path: &PathBuf, phase: &str) -> Result<(), String> {
        let mut command = Command::new(command_path);
        command
            .arg(phase)
            .env("TRUTH_ROOT", &self.config.root)
            .env("TRUTH_BIN", &self.config.truth_bin)
            .env("TRUTH_SNAPSHOT", &self.config.snapshot)
            .env("TRUTH_OPEN_ISSUES", &self.config.open_issues)
            .env_remove("TRUTH_MCP_TOKEN");
        let output = run(command, REFRESH_TIMEOUT, 20_000)?;
        if output.code == Some(0) {
            Ok(())
        } else {
            let tail: String = output
                .stderr
                .lines()
                .rev()
                .take(3)
                .collect::<Vec<_>>()
                .join(" | ");
            Err(format!(
                "refresh {phase} failed ({:?}): {tail}",
                output.code
            ))
        }
    }

    /// `prepare` fetches outside the lock; `apply` swaps the new checkout and
    /// snapshot in while no research call runs.
    fn refresh(&self, command_path: &PathBuf) {
        let result = self.refresh_phase(command_path, "prepare").and_then(|()| {
            let _guard = self.acquire(REFRESH_TIMEOUT)?;
            self.refresh_phase(command_path, "apply")
        });
        if let Err(message) = &result {
            eprintln!("truth-mcp: {message}");
        }
        self.reload_binding(Some(result));
    }
}

pub fn start_refresh(state: Arc<State>) {
    let Some(command_path) = state.config.refresh_cmd.clone() else {
        return;
    };
    thread::spawn(move || {
        loop {
            state.refresh(&command_path);
            thread::sleep(state.config.refresh_interval);
        }
    });
}

fn drain(
    mut source: impl Read + Send + 'static,
    cap: usize,
) -> thread::JoinHandle<(Vec<u8>, bool)> {
    thread::spawn(move || {
        let mut kept = Vec::new();
        let mut truncated = false;
        let mut buffer = [0u8; 65536];
        while let Ok(read) = source.read(&mut buffer) {
            if read == 0 {
                break;
            }
            let room = cap.saturating_sub(kept.len());
            kept.extend_from_slice(&buffer[..read.min(room)]);
            truncated |= read > room;
        }
        (kept, truncated)
    })
}

fn run(mut command: Command, timeout: Duration, cap: usize) -> Result<Output, String> {
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command
        .spawn()
        .map_err(|e| format!("cannot start {:?}: {e}", command.get_program()))?;
    let stdout = drain(child.stdout.take().expect("piped stdout"), cap);
    let stderr = drain(child.stderr.take().expect("piped stderr"), 8_000);
    let started = Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) if started.elapsed() < timeout => thread::sleep(Duration::from_millis(50)),
            Ok(None) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("timed out after {} s", timeout.as_secs()));
            }
            Err(e) => return Err(format!("wait failed: {e}")),
        }
    };
    let (out, truncated) = stdout.join().unwrap_or_default();
    let (err, _) = stderr.join().unwrap_or_default();
    Ok(Output {
        code: status.code(),
        stdout: String::from_utf8_lossy(&out).into_owned(),
        stderr: String::from_utf8_lossy(&err).into_owned(),
        truncated,
    })
}

/// Current UTC time as `YYYY-MM-DDTHH:MM:SSZ`.
pub fn now_iso() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0) as i64;
    let (days, rem) = (secs.div_euclid(86_400), secs.rem_euclid(86_400));
    // Howard Hinnant's civil_from_days.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        rem / 3600,
        rem % 3600 / 60,
        rem % 60
    )
}
