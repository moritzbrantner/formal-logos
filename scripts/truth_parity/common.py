"""Shared helpers of the Rust/Python parity harness: fixture identity
(readable ids converted to uuids as the corpus was), Python text output and
the `ParityCase` base class whose `binary` the entry point sets."""
import json
import subprocess
import unittest

import corpus
from corpus_ids import Aliases, is_uuid, legacy_uuid
from migrate_uuid import Migration


def U(kind, legacy):
    """The uuid a fixture record of `kind` (singular) with readable id `legacy` gets."""
    return legacy_uuid(kind, legacy)


def migrate(root):
    """Convert a fixture tree written with readable ids to uuid identity."""
    (root / "docs" / "notes").mkdir(parents=True, exist_ok=True)
    Migration(root).run(write=True)


def humanize(text, root=None):
    """Python CLI text output (`corpus.humanize`) for the checkout at `root`."""
    if root is None:
        return corpus.humanize(text)
    saved = corpus._ALIASES
    corpus._ALIASES = Aliases.load(root)
    try:
        return corpus.humanize(text)
    finally:
        corpus._ALIASES = saved


def migrated_revision(revision):
    """Whether the corpus at a Git revision uses uuid ids (None: no such revision)."""
    listing = subprocess.run(["git", "-C", str(corpus.ROOT), "ls-tree", "--name-only", f"{revision}:corpus/statements"],
                             capture_output=True, text=True, check=False)
    if listing.returncode != 0:
        return None
    first = sorted(name for name in listing.stdout.split() if name.endswith(".json"))[0]
    text = subprocess.run(["git", "-C", str(corpus.ROOT), "show", f"{revision}:corpus/statements/{first}"],
                          capture_output=True, text=True, check=True).stdout
    return is_uuid(json.loads(text).get("id"))


# `truth context` adds the elaborated types of #960, read from the cache that
# `truth bind-check` writes; Python's `context` has no such section. Parity
# runs point Rust at an absent cache, so its only addition is the one-line
# notice (text) or the `bind_types` summary (JSON), which this removes.
NO_BIND_TYPES = {"TRUTH_BIND_TYPES_CACHE": ".cache/parity-absent-bind-types.json"}
BIND_TYPES_NOTICE = "  elaborated types: no bind-check cache at .cache/parity-absent-bind-types.json "


def without_bind_types(stdout):
    """Rust `context` stdout (text or JSON) without its #960 additions."""
    if stdout.startswith("{"):
        report = json.loads(stdout)
        summary = report.pop("bind_types", None)
        assert summary is None or summary["fresh"] == 0, summary
        assert not any("elaborated" in entry for entry in report.get("lean", [])), report
        return json.dumps(report)
    lines = stdout.split("\n")
    kept = [line for line in lines if not line.startswith(BIND_TYPES_NOTICE)]
    assert len(lines) - len(kept) <= 1, stdout
    return "\n".join(kept)


class ParityCase(unittest.TestCase):
    """A parity test; `binary` is the `truth` executable under test."""
    binary = None
