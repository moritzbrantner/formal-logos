"""Plain corpus record loading and the Comparator axiom policy, for the Python
helpers that remain after #954 R3 (scaffold_result.py, sense_index.py and
tests). It validates nothing else: `truth check` is the corpus validator."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


class CorpusError(Exception):
    pass


def load_dir(name: str, root: Path | None = None) -> list[tuple[Path, dict[str, Any]]]:
    """The JSON object records of `corpus/<name>/`, in path order."""
    root = ROOT if root is None else root
    records: list[tuple[Path, dict[str, Any]]] = []
    for path in sorted((root / "corpus" / name).glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise CorpusError(f"{path.relative_to(root)}: cannot read JSON: {exc}") from exc
        if not isinstance(data, dict):
            raise CorpusError(f"{path.relative_to(root)}: top-level JSON value must be an object")
        records.append((path, data))
    return records


def index_by_id(records: list[tuple[Path, dict[str, Any]]], kind: str) -> dict[str, tuple[Path, dict[str, Any]]]:
    """Records by id; a missing, non-string or duplicate id is an error."""
    result: dict[str, tuple[Path, dict[str, Any]]] = {}
    for path, record in records:
        record_id = record.get("id")
        if not isinstance(record_id, str) or not record_id:
            raise CorpusError(f"{path}: id must be a non-empty string")
        if record_id in result:
            raise CorpusError(f"{path}: duplicate {kind} id {record_id}; first seen in {result[record_id][0]}")
        result[record_id] = (path, record)
    return result


# The only axioms a Comparator config may permit, and only when the Solution
# transitively imports Mathlib (AGENTS.md invariant 14, docs/axiom-policy.md).
# Results that do not use Mathlib stay zero-axiom. `truth check` enforces the
# same rule on the corpus; scaffold_result.py applies it to a draft.
MATHLIB_PERMITTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
LEAN_IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+(\S+)", re.MULTILINE)


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def imports_mathlib(module: str) -> bool:
    """Whether a TruthCore module imports Mathlib, directly or through other
    TruthCore modules."""
    seen: set[str] = set()
    pending = [module]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        if current == "Mathlib" or current.startswith("Mathlib."):
            return True
        path = module_path(current)
        if not current.startswith("TruthCore") or not path.is_file():
            continue
        pending.extend(LEAN_IMPORT_RE.findall(path.read_text(encoding="utf-8")))
    return False


def permitted_axioms_error(config: dict[str, Any]) -> str | None:
    """Why a Comparator config's `permitted_axioms` violates the axiom policy,
    or None when it complies."""
    axioms = config.get("permitted_axioms")
    if axioms == []:
        return None
    if not isinstance(axioms, list) or sorted(axioms) != sorted(MATHLIB_PERMITTED_AXIOMS):
        return (
            "permitted_axioms must be [] or exactly "
            f"{list(MATHLIB_PERMITTED_AXIOMS)} (docs/axiom-policy.md)"
        )
    if not imports_mathlib(config.get("solution_module", "")):
        return (
            "only a Solution that imports Mathlib may permit "
            f"{list(MATHLIB_PERMITTED_AXIOMS)}; results without Mathlib stay zero-axiom"
        )
    return None
