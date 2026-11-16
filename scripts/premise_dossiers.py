"""Validation of research attempt records (`corpus/attempts/`).

An attempt records work, never proof or closure. The dossier projection itself is
`truth dossier` (truth/README.md); its Python implementation was retired in #954 R2.
"""
from __future__ import annotations

from datetime import date
from typing import Any
import re
from corpus_ids import is_uuid  # noqa: E402


ATTEMPT_KINDS = {"derivation", "refutation", "reading", "countermodel", "source-search"}
ATTEMPT_OUTCOMES = {"succeeded", "failed", "blocked", "superseded", "rejected"}
PR_REFERENCE = re.compile(r"PR-[1-9][0-9]*\Z")


def validate_attempt(attempt: dict[str, Any], statements: set[str], evidence_ids: set[str]) -> None:
    """Validate local references; PR references have canonical syntax, not an online lookup."""
    if not is_uuid(attempt.get("id")):
        raise ValueError("id must be a uuid")
    ids = attempt.get("statement_ids")
    if not isinstance(ids, list) or not ids or any(not isinstance(sid, str) or sid not in statements for sid in ids):
        raise ValueError("statement_ids must be a non-empty list of known statements")
    if len(set(ids)) != len(ids):
        raise ValueError("statement_ids must not contain duplicates")
    try:
        value = attempt.get("date")
        if not isinstance(value, str) or date.fromisoformat(value).isoformat() != value:
            raise ValueError()
    except ValueError as exc:
        raise ValueError("date must be an ISO calendar date (YYYY-MM-DD)") from exc
    if not isinstance(attempt.get("kind"), str) or attempt["kind"] not in ATTEMPT_KINDS:
        raise ValueError(f"kind must be one of {', '.join(sorted(ATTEMPT_KINDS))}")
    if not isinstance(attempt.get("outcome"), str) or attempt["outcome"] not in ATTEMPT_OUTCOMES:
        raise ValueError(f"outcome must be one of {', '.join(sorted(ATTEMPT_OUTCOMES))}")
    if not isinstance(attempt.get("summary"), str) or not attempt["summary"].strip():
        raise ValueError("summary must be a non-empty string")
    evidence = attempt.get("evidence")
    if not isinstance(evidence, list) or any(
        not isinstance(ref, str) or (ref not in evidence_ids and not PR_REFERENCE.fullmatch(ref))
        for ref in evidence
    ):
        raise ValueError("evidence must list known result/claim IDs or PR-<positive number> references")
    if len(set(evidence)) != len(evidence):
        raise ValueError("evidence must not contain duplicates")
    blocker = attempt.get("blocker")
    if blocker is not None and (not isinstance(blocker, str) or not blocker.strip()):
        raise ValueError("blocker must be a non-empty string when present")
    if attempt.get("outcome") == "blocked" and blocker is None:
        raise ValueError("blocked attempts require a blocker")


