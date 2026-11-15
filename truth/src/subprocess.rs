//! Bounded subprocesses: Python's `subprocess.run(..., capture_output=True,
//! timeout=…)`, with the timeout covering the whole process tree.
//!
//! Killing only the immediate child on a timeout is not enough: a descendant
//! (a compiler that `lake build` started) inherits stdout and stderr, keeps
//! the pipes open, and a reader that drains them to the end blocks until it
//! exits. So on Unix the child leads its own process group and a timeout kills
//! the group; draining shares the deadline and, after a kill, waits only a
//! short grace period, so a descendant that left the group cannot hold the
//! call either. While a group runs, an interrupt or termination of `truth`
//! (SIGINT, SIGTERM) kills the group before `truth` exits as it would have,
//! because a separate group no longer receives the terminal's Ctrl-C itself.

use std::{
    io::{self, Read},
    process::{Command, Stdio},
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

/// How long draining continues after a timeout kill before the output is
/// abandoned (a descendant outside the process group may still hold a pipe).
const DRAIN_GRACE: Duration = Duration::from_secs(1);

/// A subprocess that exited within its deadline, with its captured output.
pub struct Finished {
    pub success: bool,
    pub code: Option<i32>,
    pub stdout: String,
    pub stderr: String,
}

/// Why a bounded subprocess produced no [`Finished`].
pub enum Failure {
    /// The program could not be started.
    Spawn(io::Error),
    /// Waiting for the started program failed; it has been killed.
    Wait(io::Error),
}

/// Runs `command` with stdin closed and stdout/stderr captured; `Ok(None)`
/// when the process tree is still running, or still holds the pipes, after
/// `timeout` (it is then killed).
pub fn run_bounded(mut command: Command, timeout: Duration) -> Result<Option<Finished>, Failure> {
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    let deadline = Instant::now() + timeout;
    let mut child = command.spawn().map_err(Failure::Spawn)?;
    let group = Group::register(child.id());
    let (sender, receiver) = mpsc::channel();
    let pipes: [Box<dyn Read + Send>; 2] = [
        Box::new(child.stdout.take().expect("piped stdout")),
        Box::new(child.stderr.take().expect("piped stderr")),
    ];
    for (index, mut reader) in pipes.into_iter().enumerate() {
        let sender = sender.clone();
        thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = reader.read_to_end(&mut bytes);
            let _ = sender.send((index, String::from_utf8_lossy(&bytes).into_owned()));
        });
    }
    drop(sender);
    let kill = |child: &mut std::process::Child| {
        group.kill();
        let _ = child.kill();
        let _ = child.wait();
    };
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) if Instant::now() >= deadline => break None,
            Ok(None) => thread::sleep(Duration::from_millis(20)),
            Err(error) => {
                kill(&mut child);
                return Err(Failure::Wait(error));
            }
        }
    };
    let mut output = [None, None];
    let drain_until = |output: &mut [Option<String>; 2], until: Instant| {
        while output.iter().any(Option::is_none) {
            let left = until.saturating_duration_since(Instant::now());
            match receiver.recv_timeout(left) {
                Ok((index, text)) => output[index] = Some(text),
                Err(_) => return false,
            }
        }
        true
    };
    if let Some(status) = status
        && drain_until(&mut output, deadline)
    {
        let [stdout, stderr] = output.map(Option::unwrap_or_default);
        return Ok(Some(Finished {
            success: status.success(),
            code: status.code(),
            stdout,
            stderr,
        }));
    }
    kill(&mut child);
    drain_until(&mut output, Instant::now() + DRAIN_GRACE);
    Ok(None)
}

#[cfg(unix)]
mod sys {
    pub const SIGINT: i32 = 2;
    pub const SIGKILL: i32 = 9;
    pub const SIGTERM: i32 = 15;
    pub const SIG_DFL: usize = 0;
    pub const SIG_IGN: usize = 1;
    unsafe extern "C" {
        pub fn kill(pid: i32, signal: i32) -> i32;
        pub fn signal(signal: i32, handler: usize) -> usize;
        pub fn raise(signal: i32) -> i32;
    }
}

/// The running process groups, for the signal handler (async-signal-safe:
/// atomics and `kill` only).
#[cfg(unix)]
static GROUPS: [std::sync::atomic::AtomicI32; 32] =
    [const { std::sync::atomic::AtomicI32::new(0) }; 32];

#[cfg(unix)]
extern "C" fn on_signal(signal: i32) {
    use std::sync::atomic::Ordering;
    for slot in &GROUPS {
        let group = slot.load(Ordering::SeqCst);
        if group > 0 {
            // SAFETY: kill, signal and raise are async-signal-safe.
            unsafe { sys::kill(-group, sys::SIGKILL) };
        }
    }
    unsafe {
        sys::signal(signal, sys::SIG_DFL);
        sys::raise(signal);
    }
}

/// A started child's process group, registered for the signal handler
/// while it runs.
struct Group {
    #[cfg(unix)]
    slot: Option<&'static std::sync::atomic::AtomicI32>,
    #[cfg(unix)]
    id: i32,
}

impl Group {
    #[cfg(unix)]
    fn register(pid: u32) -> Self {
        use std::sync::{Once, atomic::Ordering};
        static INSTALL: Once = Once::new();
        INSTALL.call_once(|| {
            for signal in [sys::SIGINT, sys::SIGTERM] {
                // SAFETY: installs a handler that only uses async-signal-safe
                // calls; an ignored signal stays ignored.
                unsafe {
                    if sys::signal(signal, on_signal as extern "C" fn(i32) as usize) == sys::SIG_IGN
                    {
                        sys::signal(signal, sys::SIG_IGN);
                    }
                }
            }
        });
        let id = i32::try_from(pid).unwrap_or(0);
        let slot = GROUPS.iter().find(|slot| {
            id > 0
                && slot
                    .compare_exchange(0, id, Ordering::SeqCst, Ordering::SeqCst)
                    .is_ok()
        });
        Group { slot, id }
    }

    #[cfg(not(unix))]
    fn register(_pid: u32) -> Self {
        Group {}
    }

    /// Kills every process of the group (Unix); elsewhere only the child
    /// itself is killed, by the caller.
    fn kill(&self) {
        #[cfg(unix)]
        if self.id > 0 {
            // SAFETY: the group was created for this child and still has it
            // as a member (not yet reaped), so the id is not reused.
            unsafe { sys::kill(-self.id, sys::SIGKILL) };
        }
    }
}

impl Drop for Group {
    fn drop(&mut self) {
        #[cfg(unix)]
        if let Some(slot) = self.slot {
            slot.store(0, std::sync::atomic::Ordering::SeqCst);
        }
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn shell(script: &str) -> Command {
        let mut command = Command::new("sh");
        command.args(["-c", script]);
        command
    }

    #[test]
    fn captures_output_and_status() {
        let done = run_bounded(
            shell("echo out; echo err >&2; exit 3"),
            Duration::from_secs(10),
        )
        .ok()
        .flatten()
        .expect("finished");
        assert!(!done.success);
        assert_eq!(done.code, Some(3));
        assert_eq!(
            (done.stdout.as_str(), done.stderr.as_str()),
            ("out\n", "err\n")
        );
    }

    /// A grandchild holding the pipes must not extend the timeout, whether
    /// the child is still waiting for it or has already exited.
    #[test]
    fn timeout_bounds_a_pipe_holding_grandchild() {
        for script in ["(sleep 30) & wait", "(sleep 30) & echo started"] {
            let start = Instant::now();
            let outcome = run_bounded(shell(script), Duration::from_millis(300));
            assert!(matches!(outcome, Ok(None)), "{script}: expected a timeout");
            let elapsed = start.elapsed();
            // Killing the group closes the pipes at once: no drain grace.
            assert!(
                elapsed < Duration::from_millis(300) + DRAIN_GRACE,
                "{script}: {elapsed:?}"
            );
        }
    }

    /// A descendant that left the process group still cannot hold the call
    /// past the deadline plus the drain grace.
    #[test]
    fn drain_is_bounded_for_an_escaped_descendant() {
        if !std::path::Path::new("/usr/bin/setsid").exists() {
            return;
        }
        let start = Instant::now();
        let outcome = run_bounded(
            shell("/usr/bin/setsid sleep 5 & wait"),
            Duration::from_millis(300),
        );
        assert!(matches!(outcome, Ok(None)));
        let elapsed = start.elapsed();
        assert!(
            elapsed < Duration::from_millis(300) + DRAIN_GRACE + Duration::from_millis(700),
            "{elapsed:?}"
        );
    }
}
