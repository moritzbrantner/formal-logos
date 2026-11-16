#!/usr/bin/env python3
"""Sense-indexed terms: the one-shot label migration.

Owner direction (2026-11-07): each disambiguated term carries numbered senses
(PRIOR_1, PRIOR_2, ...) whose identity is an opaque uuid4; one argument uses
one sense per term, and an argument valid in several senses is recorded once
per sense. See docs/corpus-model.md, "Sense-indexed terms".

  migrate [--write]    give every disambiguation a term_label and uuid senses

The mixing report, the allowlist and its ratchet are `truth senses
report|allowlist|ratchet` (#954 B6); their Python versions were retired in R2.
"""
from __future__ import annotations

import argparse
import json
import re
import unicodedata
import uuid
from pathlib import Path
from typing import Any

import corpus


MAX_TERM_WORDS = 6
CONNECTORS = {"AND", "OR", "OF", "THE", "A", "AN", "IN", "TO", "VERSUS", "VS", "FROM", "BY", "AS", "AT", "ON", "FOR"}


def normalize_term(term: str) -> str:
    """`prior (simply, in time, or in substance)` -> PRIOR: parentheticals
    dropped, ASCII-folded, upper snake case."""
    text = re.sub(r"\([^()]*\)", " ", term)
    text = unicodedata.normalize("NFKD", text).encode("ascii", "ignore").decode()
    label = re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_").upper()
    if not label:
        return "TERM"
    return label if label[0].isalpha() else f"T_{label}"


def short_term_labels(terms: list[str]) -> dict[str, str]:
    """A short, unique term label per distinct `term` text.

    A long compound record term keeps its first six words, without trailing
    connectors ("reception of esse versus external cause of esse" ->
    RECEPTION_OF_ESSE_VERSUS_EXTERNAL_CAUSE). Records with the same term text
    share a label; when a cut label would merge two different terms, the
    longer one keeps more words until the labels differ."""
    full = {term: normalize_term(term) for term in terms}

    def trimmed(words: list[str]) -> str:
        while len(words) > 1 and words[-1] in CONNECTORS:
            words = words[:-1]
        return "_".join(words)

    labels: dict[str, str] = {}
    owner: dict[str, str] = {}
    for term in sorted(set(terms), key=lambda t: (len(full[t]), full[t])):
        words = full[term].split("_")
        candidates = [trimmed(words[:n]) for n in range(min(MAX_TERM_WORDS, len(words)), len(words) + 1)]
        choice = next((c for c in candidates if owner.get(c, full[term]) == full[term]), full[term])
        owner[choice] = full[term]
        labels[term] = choice
    return labels


def insert_fields(text: str, fields: dict[str, Any]) -> str:
    """Append top-level fields to a JSON object's text, leaving the rest byte-identical."""
    body = text.rstrip()
    assert body.endswith("}"), "a record is a JSON object"
    rendered = "".join(
        ",\n  " + json.dumps(key) + ": " + json.dumps(value, indent=2, ensure_ascii=False).replace("\n", "\n  ")
        for key, value in fields.items()
    )
    return body[:-1].rstrip() + rendered + "\n}\n"


def replace_senses(text: str, senses: list[dict[str, Any]]) -> str:
    """Rewrite the trailing `senses` field (the migration writes it last)."""
    head, marker, _ = text.rpartition(',\n  "senses": ')
    assert marker, "senses is the record's last field"
    return insert_fields(head + "\n}\n", {"senses": senses})


def migrate(write: bool) -> list[str]:
    """Label every disambiguation without senses and give each sense the Lean
    declaration of its definition when it has one; existing labels, uuids and
    declarations are kept."""
    records = corpus.load_dir("disambiguations")
    declarations = {record["id"]: record["lean_declaration"] for _, record in corpus.load_dir("definitions")
                    if record.get("lean_declaration")}
    assigned: dict[tuple[str, str], dict[str, str]] = {}
    counters: dict[str, int] = {}
    for _, record in records:
        term = record.get("term_label")
        for sense in record.get("senses", []):
            assigned[(term, sense["definition_id"])] = sense
            index = int(sense["label"].rsplit("_", 1)[1])
            counters[term] = max(counters.get(term, 0), index)
    changed = []
    taken = {record["term_label"] for _, record in records if "term_label" in record}
    fresh = short_term_labels([record["term"] for _, record in records if "term_label" not in record])
    if taken & set(fresh.values()):
        raise SystemExit(f"new term labels collide with existing ones: {sorted(taken & set(fresh.values()))}")
    for path, record in sorted(records, key=lambda item: item[1]["id"]):
        if "senses" in record:
            senses = [dict(sense, lean_declaration=declarations[sense["definition_id"]])
                      if "lean_declaration" not in sense and sense["definition_id"] in declarations else sense
                      for sense in record["senses"]]
            if senses != record["senses"]:
                changed.append(record["id"])
                if write:
                    path.write_text(replace_senses(path.read_text(encoding="utf-8"), senses), encoding="utf-8")
            continue
        term = record.get("term_label") or fresh[record["term"]]
        senses = []
        for definition_id in record["sense_definition_ids"]:
            key = (term, definition_id)
            if key not in assigned:
                counters[term] = counters.get(term, 0) + 1
                assigned[key] = {"id": str(uuid.uuid4()), "label": f"{term}_{counters[term]}",
                                 "definition_id": definition_id}
                if definition_id in declarations:
                    assigned[key]["lean_declaration"] = declarations[definition_id]
            senses.append(dict(assigned[key]))
        fields = {"senses": senses} if "term_label" in record else {"term_label": term, "senses": senses}
        changed.append(record["id"])
        if write:
            path.write_text(insert_fields(path.read_text(encoding="utf-8"), fields), encoding="utf-8")
    return changed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("migrate",))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)
    changed = migrate(args.write)
    print(f"{'labelled' if args.write else 'would label'} {len(changed)} disambiguation(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
