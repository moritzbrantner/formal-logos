"""Run the repository's Rust `truth` CLI (truth/README.md) from Python.

`TRUTH_CLI` names a prebuilt binary. Otherwise Cargo builds and runs the
checkout's release build (rebuilt only when its inputs changed), as
`scripts/agent_service.py` does; callers that accept an existing build (the
unit tests, which CI runs after `cargo build --locked --release -p truth`)
use `target/release/truth` when it exists."""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]


def command(root: Path | None = None, *, existing_build: bool = True) -> list[str]:
    """The command prefix that runs `truth` for the checkout at `root` (run it
    with `cwd=root`). `existing_build=False` always goes through Cargo, so the
    checkout's current sources are what runs."""
    root = ROOT if root is None else root
    binary = os.environ.get("TRUTH_CLI")
    if binary:
        return [binary]
    release = root / "target" / "release" / "truth"
    if existing_build and release.is_file() and os.access(release, os.X_OK):
        return [str(release)]
    return ["cargo", "run", "--quiet", "--locked", "--release", "-p", "truth", "--"]


def run(args: Iterable[str], *, root: Path | None = None, cwd: Path | None = None,
        input: str | None = None, timeout: float = 600) -> subprocess.CompletedProcess:
    """`truth --root ROOT ARGS...`, captured as text; never raises on exit status."""
    root = ROOT if root is None else root
    return subprocess.run([*command(root), "--root", str(root), *args], cwd=cwd or root, input=input,
                          capture_output=True, text=True, timeout=timeout, check=False)


def frontier_fixture(statements: Iterable[dict] = (), arguments: Iterable[dict] = (),
                     results: Iterable[dict] = (), relations: Iterable[dict] = (),
                     claims: Iterable[dict] = (), inferences: Iterable[dict] = (), *,
                     root: str | None = None, transcription_flags: Iterable[dict] = ()) -> dict[str, Any]:
    """`truth --json frontier --fixture -` on the given records: the frontier
    report the Rust rules compute for exactly these records, with no corpus
    validation and no Lean source read (#954 B12)."""
    fixture = {"statements": list(statements), "arguments": list(arguments), "results": list(results),
               "relations": list(relations), "claims": list(claims), "inferences": list(inferences),
               "transcription_flags": list(transcription_flags)}
    args = ["--json", "frontier", "--fixture", "-"]
    if root is not None:
        args += ["--frontier-root", root]
    completed = run(args, input=json.dumps(fixture))
    if completed.returncode != 0:
        raise RuntimeError(f"truth frontier --fixture failed ({completed.returncode}): {completed.stderr.strip()}")
    return json.loads(completed.stdout)
