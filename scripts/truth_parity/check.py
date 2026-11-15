"""`truth check` against `corpus.py check`."""
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import corpus
import source_evidence
from corpus_ids import KIND_DIRS
from truth_parity.common import U, migrate, ParityCase


REVISION = "0" * 40
SENSE_X = "11111111-1111-4111-8111-111111111111"
SENSE_Y = "22222222-2222-4222-9222-222222222222"
SENSE_Z = "33333333-3333-4333-a333-333333333333"
CHECK_LEAN = {
    "TruthCore/Fix/Challenge.lean": "theorem fixAB (h : fixA) : fixB := sorry\n",
    "TruthCore/Fix/Solution.lean": (
        "def fixA : Prop := True\ndef fixB : Prop := True\ndef fixC : Prop := True\n"
        "def fixD : Prop := True\ndef fixE : Prop := True\n"
        "theorem fixAB (h : fixA) : fixB := trivial\ntheorem fixBC (h : fixB) : fixC := trivial\n"
        "def markConcrete (_ : Nat) : Prop := True\n"
        "-- category-constant: intended (the fixture's point)\ndef markAbstract (_ : Nat) : Prop := False\n"
    ),
}


def check_records():
    """A small corpus that passes `corpus.py check` with one warning of each
    ported kind: an unverified refutation, a supports relation without a
    note, a strong version used without `strong_version_needed`, a constant
    category predicate and an unmet floor basis."""
    def statement(sid, decl, **extra):
        return {"id": sid, "paraphrase": sid, "lean_declaration": f"TruthCore.Fix.{decl}", **extra}

    def result(rid, argument, theorem):
        return {"id": rid, "argument_id": argument, "challenge_module": "TruthCore.Fix.Challenge",
                "solution_module": "TruthCore.Fix.Solution", "theorem": f"TruthCore.Fix.{theorem}",
                "comparator_config": f"results/{rid}/comparator.json", "status": "verified"}

    def relation(rid, sk, subject, predicate, obj, **extra):
        return {"id": rid, "subject_kind": sk, "subject_id": subject, "predicate": predicate,
                "object_kind": "statement", "object_id": obj, **extra}

    return {
        "sources": [{"id": "SRC", "kind": "text", "author": "A", "work": "W", "citation_system": "n",
                     "work_urn": "urn:cts:fix:w", "catalog_url": "https://example.org",
                     "edition_urns": ["urn:cts:fix:w.a", "urn:cts:fix:w.b"]}],
        "passages": [{"snapshot": {
            "source_id": "SRC", "edition_urn": "urn:cts:fix:w.a", "language": "la", "repository": "org/repo",
            "revision": REVISION, "path": "w.xml", "git_blob_sha": REVISION,
            "source_url": f"https://raw.githubusercontent.com/org/repo/{REVISION}/w.xml", "license": "PD"},
            "passages": [{"id": "P-1", "locator": "1", "claim_locator_prefixes": ["1"]}]}],
        "statements": [
            statement("STMT-A", "fixA"), statement("STMT-B", "fixB", definition_ids=["DEF-X"]),
            statement("STMT-C", "fixC", definition_ids=["DEF-Y"]), statement("STMT-D", "fixD"),
            statement("STMT-E", "fixE", self_evident={"justification_ids": ["CLAIM-A"], "basis": "observation",
                                                      "disagreement": "none recorded"}),
        ],
        "claims": [{"id": "CLAIM-A", "statement_id": "STMT-A", "source_id": "SRC", "locator": "1.1",
                    "interpretation": "i", "status": "formalized"}],
        "definitions": [
            {"id": "DEF-X", "term": "t", "definition": "first sense", "basis": "sourced", "claim_ids": ["CLAIM-A"]},
            {"id": "DEF-Y", "term": "t", "definition": "second sense", "basis": "stipulative", "note": "why"},
        ],
        "disambiguations": [{"id": "DISAMB-T", "term": "t", "resolution": "DEF-X here, DEF-Y there",
                             "sense_definition_ids": ["DEF-X", "DEF-Y"], "term_label": "T",
                             "senses": [{"id": SENSE_X, "label": "T_1", "definition_id": "DEF-X",
                                         "lean_declaration": "TruthCore.Fix.fixB"},
                                        {"id": SENSE_Y, "label": "T_2", "definition_id": "DEF-Y"}]}],
        "inferences": [
            {"id": f"INF-{a}{b}", "input_statement_ids": [f"STMT-{a}"], "assumption_statement_ids": [],
             "discharged_statement_ids": [], "output_statement_id": f"STMT-{b}", "rule": "mp", "meaning": "m"}
            for a, b in (("A", "B"), ("B", "C"), ("A", "D"))
        ],
        "arguments": [
            {"id": "ARG-AB", "premise_statement_ids": ["STMT-A"], "inference_ids": ["INF-AB"],
             "conclusion_statement_id": "STMT-B", "meaning": "m"},
            {"id": "ARG-BC", "premise_statement_ids": ["STMT-B"], "inference_ids": ["INF-BC"],
             "conclusion_statement_id": "STMT-C", "meaning": "m", "disambiguation_ids": ["DISAMB-T"],
             "term_senses": {"T": SENSE_Y},
             "sense_bridges": [{"term": "T", "from": SENSE_X, "to": SENSE_Y, "statement_id": "STMT-B"}]},
            {"id": "ARG-BC-OLD", "premise_statement_ids": ["STMT-B"], "inference_ids": ["INF-BC"],
             "conclusion_statement_id": "STMT-C", "meaning": "m", "disambiguation_ids": ["DISAMB-T"]},
            {"id": "ARG-AD", "premise_statement_ids": ["STMT-A"], "inference_ids": ["INF-AD"],
             "conclusion_statement_id": "STMT-D", "meaning": "m"},
        ],
        "results": [result("RES-AB", "ARG-AB", "fixAB"), result("RES-BC", "ARG-BC", "fixBC")],
        "relations": [
            relation("REL-STR", "statement", "STMT-A", "strengthens", "STMT-B",
                     verification_result_id="RES-AB", note="A is the strong version"),
            relation("REL-SUP", "claim", "CLAIM-A", "supports", "STMT-C"),
            relation("REL-ALT", "statement", "STMT-E", "alternative_to", "STMT-C"),
            relation("REL-REF", "argument", "ARG-AD", "refutes", "STMT-E"),
        ],
        "candidates": [{"id": "CAND-1", "source_id": "SRC", "locator": "2", "priority": 1, "goal": "g",
                        "reason": "r", "status": "candidate"}],
        "attempts": [{"id": "ATTEMPT-ONE", "statement_ids": ["STMT-A"], "date": "2026-11-07",
                      "kind": "derivation", "outcome": "succeeded", "summary": "Derived STMT-B.",
                      "evidence": ["RES-AB", "PR-1"]}],
        "models": [{"id": "MODEL-FIX", "description": "d", "vocabulary": "fix",
                    "lean_declaration": "TruthCore.Fix.model", "modules": ["TruthCore.Fix.Solution"],
                    "bindings": {"W": "Bool"},
                    "carriers": [{"binding": "W", "theorem": "TruthCore.Fix.enum", "elements": ["true", "false"]}],
                    "evaluations": [{"statement_id": "STMT-A", "value": "satisfies",
                                     "theorem": "TruthCore.Fix.eval", "arguments": ["W"]}]}],
        "configurations": [{"id": "CONFIG-FIX", "seed_statement_id": "STMT-A",
                            "semantics": {"id": "p", "logic": "l", "frame": "f", "domain": "d", "identity": "i",
                                          "vocabulary": "fix", "parameters": [{"name": "W", "type": "Type"}],
                                          "applications": {"STMT-A": ["W"]},
                                          "modules": ["TruthCore.Fix.Solution"], "permitted_axioms": []},
                            "configurations": [{"id": "base", "statement_ids": ["STMT-A"]}],
                            "incompatibility_result_ids": [],
                            "model_bindings": [{"model_id": "MODEL-FIX", "parameters": {"W": "W"}}]}],
        "sense_allowlist": {"arguments": {"ARG-BC-OLD": {"T": [SENSE_X, SENSE_Y]}},
                            "senses_without_lean_declaration": [SENSE_Y]},
    }


def by_id(records, kind, rid):
    """The fixture record of directory `kind` whose readable id was `rid`."""
    uid = U(KIND_DIRS[kind], rid)
    return next(record for record in records[kind] if record.get("id") in (rid, uid))


def mutate(kind, rid, **changes):
    def apply(records):
        record = by_id(records, kind, rid)
        for key, value in changes.items():
            if value is None:
                record.pop(key, None)
            else:
                record[key] = value
    return apply


def add(kind, record):
    return lambda records: records[kind].append(dict(record))


def new(kind, legacy, label, **fields):
    """A migrated-looking record of directory `kind` (uuid id, legacy_id and label)."""
    return {"id": U(KIND_DIRS[kind], legacy), "label": label, "legacy_id": legacy, **fields}


def bridge(**changes):
    if changes.get("statement_id") == "STMT-C":
        changes["statement_id"] = U("statement", "STMT-C")
    def apply(records):
        by_id(records, "arguments", "ARG-BC")["sense_bridges"][0].update(changes)
    return apply


def sense(index, **changes):
    def apply(records):
        by_id(records, "disambiguations", "DISAMB-T")["senses"][index].update(changes)
    return apply


def second_disambiguation(senses):
    return add("disambiguations", {"id": U("disambiguation", "DISAMB-U"), "label": "second term", "term": "t again", "resolution": "r", "term_label": "T",
                                   "sense_definition_ids": [s["definition_id"] for s in senses], "senses": senses})


def comparator(change):
    def apply(records, configs):
        change(configs["RES-AB"])
    return apply


def allowlisted(kind, rid):
    """Flag a record `untagged-sense` in docs/notes/label-cleanup.json."""
    def apply(records):
        records["_cleanup"].append({"kind": KIND_DIRS[kind], "id": U(KIND_DIRS[kind], rid),
                                    "legacy_id": rid, "label": "x", "flags": ["untagged-sense"]})
    return apply


def both(*changes):
    def apply(records):
        for change in changes:
            change(records)
    return apply


GHOST = "00000000-0000-4000-8000-000000000000"

# One deliberately broken corpus per rule; both implementations must report
# the same first error. Mutations run on the migrated (uuid) fixture.
def passage(*bases, **overrides):
    """Change the fixture's one passage entry (it overrides the snapshot):
    the fields of `bases`, then `overrides`; a None value removes the field
    from both."""
    changes = {key: value for base in bases for key, value in base.items()} | overrides

    def apply(records):
        manifest = records["passages"][0]
        for key, value in changes.items():
            if value is None:
                manifest["snapshot"].pop(key, None)
                manifest["passages"][0].pop(key, None)
            else:
                manifest["passages"][0][key] = value
    return apply


MEDIA = {"kind": "media_span", "youtube_id": "abcdefghijk", "transcript_source": "asr", "producer": "youtube-corpus",
         "producer_revision": "git:" + REVISION, "export_schema": "source_span_interchange@1",
         "source_url": "https://www.youtube.com/watch?v=abcdefghijk", "start_seconds": 0, "end_seconds": 1.5,
         "segment_count": 1, "span_sha256": "sha256:" + "a" * 64}
WEB = {"kind": "web_snapshot", "source_url": "https://example.org/page", "retrieved_at": "2026-11-10T00:00:00Z",
       "sha256": "sha256:" + "b" * 64, "text_sha256": "sha256:" + "c" * 64, "encoding": "ISO_8859-1",
       "raw_text": True}
# Valid except that the snapshot's git_blob_sha is still present.
BIB = {"kind": "bibliographic_span", "author": "A", "title": "T", "year": 2001, "publisher": "P",
       "isbn": "0-306-40615-2", "doi": "10.1000/xyz", "pages": "1-2",
       "why_bibliographic": "copyrighted; no legitimately hosted copy"}


CHECK_FAILURES = {
    "duplicate id": add("statements", {"id": U("statement", "STMT-A"), "label": "again", "paraphrase": "again"}),
    "unknown claim statement reference": mutate("claims", "CLAIM-A", statement_id=GHOST),
    "unknown inference reference": mutate("arguments", "ARG-AB", inference_ids=[GHOST]),
    "argument not grounded": mutate("arguments", "ARG-BC", inference_ids=[U("inference", "INF-AB")]),
    "missing disambiguation link for two senses": mutate("arguments", "ARG-BC", disambiguation_ids=None),
    "empty disambiguation_ids": mutate("statements", "STMT-C", disambiguation_ids=[]),
    "unknown definition link": mutate("statements", "STMT-C", definition_ids=[GHOST]),
    "disambiguation with one sense": mutate("disambiguations", "DISAMB-T",
                                            sense_definition_ids=[U("definition", "DEF-X")] * 2),
    "unused definition": add("definitions", new("definitions", "DEF-Z", "zed", term="z", definition="z",
                                                basis="stipulative", note="n")),
    "stipulative definition without note": mutate("definitions", "DEF-Y", note=None),
    "prose cites unknown legacy id": mutate("disambiguations", "DISAMB-T", resolution="see STMT-GHOST"),
    "prose cites unknown uuid": mutate("disambiguations", "DISAMB-T", resolution=f"see {GHOST}"),
    "bad strengthens registration": mutate("relations", "REL-STR", verification_result_id=U("result", "RES-BC")),
    "sense coverage statement does not link the term": mutate("disambiguations", "DISAMB-T",
                                                              coverage_statement_id=U("statement", "STMT-A")),
    "sense fork without coverage premise": mutate("disambiguations", "DISAMB-T", fork_result_ids=[U("result", "RES-BC")]),
    "strengthens without note": mutate("relations", "REL-STR", note=" "),
    "duplicate strength registration": add("relations", new(
        "relations", "REL-STR-DUP", "duplicate strength", subject_kind="statement",
        subject_id=U("statement", "STMT-A"), predicate="strengthens", object_kind="statement",
        object_id=U("statement", "STMT-B"), verification_result_id=U("result", "RES-AB"), note="n")),
    "strong_version_needed names a non-premise": mutate("arguments", "ARG-BC",
                                                        strong_version_needed={U("statement", "STMT-A"): "why"}),
    "unknown attempt outcome": mutate("attempts", "ATTEMPT-ONE", outcome="maybe"),
    "attempt date not ISO": mutate("attempts", "ATTEMPT-ONE", date="2026-02-30"),
    "attempt evidence unknown": mutate("attempts", "ATTEMPT-ONE", evidence=["PR-0"]),
    "attempt id not a uuid": mutate("attempts", "ATTEMPT-ONE", id="ATTEMPT-ONE"),
    "blocked attempt without blocker": mutate("attempts", "ATTEMPT-ONE", outcome="blocked"),
    "self_evident without basis": mutate("statements", "STMT-E",
                                         self_evident={"justification_ids": [U("claim", "CLAIM-A")]}),
    "self_evident unknown rival": mutate("statements", "STMT-E", self_evident={
        "justification_ids": [U("claim", "CLAIM-A")], "basis": "observation",
        "disagreement": {"rival_statement_ids": [GHOST]}}),
    "owner approval with a bad URL": mutate("statements", "STMT-E", self_evident={
        "justification_ids": [U("claim", "CLAIM-A")], "basis": "observation", "disagreement": "none recorded",
        "owner_approval": {"decision": "https://example.org", "date": "2026-11-05"}}),
    "relation kind mismatch": mutate("relations", "REL-SUP", subject_kind="statement",
                                     subject_id=U("statement", "STMT-A")),
    "root_route to another conclusion": add("relations", new(
        "relations", "REL-ROUTE", "route", subject_kind="argument", subject_id=U("argument", "ARG-AB"),
        predicate="root_route", object_kind="statement", object_id=U("statement", "STMT-C"))),
    "candidate priority not an integer": mutate("candidates", "CAND-1", priority="1"),
    "claim status": mutate("claims", "CLAIM-A", status="accepted"),
    "claim attribution shape": mutate("claims", "CLAIM-A", attribution="The passage says so."),
    "claim resolves to no passage": mutate("claims", "CLAIM-A", locator="9"),
    "basis on a non-translation claim": mutate("claims", "CLAIM-A", basis="translation"),
    "unsorted edition_urns": mutate("sources", "SRC", edition_urns=["urn:cts:fix:w.b", "urn:cts:fix:w.a"]),
    "source missing field": mutate("sources", "SRC", catalog_url=""),
    "Lean declaration tail not found": mutate("statements", "STMT-D", lean_declaration="TruthCore.Fix.nowhere"),
    "shared Lean declaration": mutate("statements", "STMT-D", lean_declaration="TruthCore.Fix.fixA"),
    "settlement action shape": mutate("statements", "STMT-D", settlement_actions=[{"kind": "other"}]),
    "transcription label without field": mutate("results", "RES-BC", description="Transcription of BC."),
    "unknown transcription kind": mutate("results", "RES-BC", transcription="echo"),
    "comparator path": mutate("results", "RES-BC", comparator_config="elsewhere.json"),
    "comparator path of a new result is its uuid": mutate("results", "RES-BC", legacy_id=None),
    "case_split without target": mutate("results", "RES-BC", case_split={"cases": []}),
    "NanoDa disabled": comparator(lambda config: config.update(enable_nanoda=False)),
    "axioms permitted without Mathlib": comparator(
        lambda config: config.update(permitted_axioms=["propext", "Classical.choice", "Quot.sound"])),
    "theorem not in Comparator config": comparator(lambda config: config.update(theorem_names=[])),
    "bad model id": mutate("models", "MODEL-FIX", id="MODEL-FIX"),
    "model evaluation of unknown statement": mutate("models", "MODEL-FIX", evaluations=[
        {"statement_id": GHOST, "value": "satisfies", "theorem": "T.e", "arguments": []}]),
    "configuration id not a uuid": mutate("configurations", "CONFIG-FIX", id="CONFIG-FIX"),
    "configuration unknown seed": mutate("configurations", "CONFIG-FIX", seed_statement_id=GHOST),
    "configuration omits a model": mutate("configurations", "CONFIG-FIX", model_bindings=[]),
    "strength comparison without evidence": add("relations", new(
        "relations", "REL-CMP", "comparison", subject_kind="statement", subject_id=U("statement", "STMT-A"),
        predicate="strength_comparison", object_kind="statement", object_id=U("statement", "STMT-B"),
        delta_statement_id=U("statement", "STMT-C"), background_statement_ids=[],
        statement_parameter_indices={"stronger": [], "weaker": [], "delta": []},
        comparison_spec="s", note="n", evidence_result_ids={})),
    "disambiguation without term_label": mutate("disambiguations", "DISAMB-T", term_label=None),
    "senses not sense objects": mutate("disambiguations", "DISAMB-T", senses=[{"id": SENSE_X}]),
    "sense id not a uuid4": sense(0, id="T-1"),
    "sense label not TERM_n": sense(0, label="T_0"),
    "senses out of order": mutate("disambiguations", "DISAMB-T", sense_definition_ids=[U("definition", "DEF-Y"), U("definition", "DEF-X")]),
    "duplicate sense labels": sense(1, label="T_1"),
    "sense uuid reused for another definition": second_disambiguation([
        {"id": SENSE_X, "label": "T_1", "definition_id": U("definition", "DEF-Y")},
        {"id": SENSE_Z, "label": "T_3", "definition_id": U("definition", "DEF-X")}]),
    "definition given two senses under one term": second_disambiguation([
        {"id": SENSE_Z, "label": "T_3", "definition_id": U("definition", "DEF-X")},
        {"id": SENSE_Y, "label": "T_2", "definition_id": U("definition", "DEF-Y")}]),
    "sense label naming two senses": lambda records: (
        add("definitions", {"id": U("definition", "DEF-W"), "label": "third term", "term": "t", "definition": "third sense", "basis": "stipulative",
                            "note": "n"})(records),
        second_disambiguation([{"id": SENSE_Y, "label": "T_2", "definition_id": U("definition", "DEF-Y")},
                               {"id": SENSE_Z, "label": "T_1", "definition_id": U("definition", "DEF-W")}])(records)),
    "sense_bridges not a list": mutate("arguments", "ARG-BC", sense_bridges={"T": SENSE_X}),
    "sense bridge shape": bridge(note="extra"),
    "sense bridge end not a sense of its term": bridge(to=SENSE_Z),
    "sense bridge relating one sense": bridge(to=SENSE_X),
    "sense bridge statement not a premise": bridge(statement_id=U("statement", "STMT-C")),
    "sense bridge with an unknown role": bridge(role="lemma"),
    "conclusion sense bridge naming a premise": bridge(role="conclusion"),
    "sense_mixing_control on an argument with premises": mutate("arguments", U("argument", "ARG-BC-OLD"), sense_mixing_control=True),
    "sense_mixing_control not true": mutate("arguments", "ARG-AB", sense_mixing_control="yes"),
    "term_senses not a map": mutate("arguments", "ARG-BC", term_senses=[SENSE_Y]),
    "term_senses names no sense of the term": mutate("arguments", "ARG-BC", term_senses={"T": "T_2"}),
    "term_senses names an unused sense": mutate("arguments", "ARG-AB", term_senses={"T": SENSE_Y}),
    "two senses without a bridge": mutate("arguments", "ARG-BC", sense_bridges=None),
    "allowlist does not cover the senses": lambda records: records["sense_allowlist"]["arguments"].update(
        {U("argument", "ARG-BC-OLD"): {"T": [SENSE_X]}}),
    "malformed allowlist": lambda records: records.update(sense_allowlist={U("argument", "ARG-BC-OLD"): {"T": [SENSE_X]}}),
    "sense without a Lean declaration": lambda records: records["sense_allowlist"].update(
        senses_without_lean_declaration=[]),
    "two senses with one Lean declaration": sense(1, lean_declaration="TruthCore.Fix.fixB"),
    "sense Lean declaration not found": sense(0, lean_declaration="TruthCore.Fix.nowhere"),
    "sense with an unknown field": sense(0, note="n"),
    "candidate/result id collision": add("candidates", {"id": U("result", "RES-AB"), "label": "collision",
                                                        "source_id": U("source", "SRC"), "locator": "2",
                                                        "priority": 1, "goal": "g", "reason": "r",
                                                        "status": "candidate"}),
    # Identity rules (scripts/identity_check.py).
    "statement id not a uuid": mutate("statements", "STMT-D", id="STMT-D"),
    "passage id not a uuid": lambda records: records["passages"][0]["passages"][0].update(id="P-1"),
    "legacy_id mismatch": mutate("statements", "STMT-D", legacy_id="STMT-OTHER"),
    "legacy_id empty": mutate("statements", "STMT-D", legacy_id=""),
    "missing label": mutate("statements", "STMT-D", label=None),
    "blank label": mutate("statements", "STMT-D", label="  "),
    "label too long": mutate("statements", "STMT-D", label="é" * 101),
    "label with surrounding whitespace": mutate("statements", "STMT-D", label=" d "),
    "id-like label": mutate("statements", "STMT-D", label="d after STMT-A and 0123abcd-ffff"),
    "duplicate label within a kind": mutate("statements", "STMT-D", label="a"),
    "several identity errors": both(mutate("statements", "STMT-D", label="a"),
                                    mutate("claims", "CLAIM-A", label=None)),
    "untagged linked sense": mutate("statements", "STMT-B", label="the t of b"),
    # Passage manifest schema (source_evidence.validate_manifest).
    "text witness missing field": passage(license=""),
    "text witness unknown kind": passage(kind="scroll"),
    "text witness bad prefixes": passage(claim_locator_prefixes=["1", ""]),
    "text witness bad revision": passage(revision="abc"),
    "text witness bad blob sha": passage(git_blob_sha="g" * 40),
    "text witness unpinned url": passage(source_url="https://example.org/w.xml"),
    "text witness empty tei id": passage(tei_xml_id=""),
    "text witness tei id and cts path": passage(tei_xml_id="x", cts_path=[{"subtype": "s", "n": "1"}]),
    "text witness cts path not a list": passage(cts_path={"subtype": "s"}),
    "text witness bad cts selector": passage(cts_path=[{"subtype": "s", "n": 1}]),
    "media span missing field": passage(kind="media_span"),
    "media span bad youtube id": passage(MEDIA, youtube_id="short"),
    "media span bad transcript source": passage(MEDIA, transcript_source="memory"),
    "media span bad schema": passage(MEDIA, export_schema="x@2"),
    "media span bad producer": passage(MEDIA, producer="other"),
    "media span bad producer revision": passage(MEDIA, producer_revision="abc"),
    "media span url without id": passage(**{**MEDIA, "source_url": "https://youtu.be/"}),
    "media span bad times": passage(MEDIA, start_seconds=5, end_seconds=5),
    "media span boolean time": passage(MEDIA, start_seconds=True),
    "media span bad count": passage(MEDIA, segment_count=1.0),
    "media span bad hash": passage(MEDIA, span_sha256="sha256:x"),
    "media span with text": passage(MEDIA, transcript="t"),
    "web snapshot missing field": passage(kind="web_snapshot"),
    "web snapshot bad url": passage(WEB, source_url="ftp://example.org"),
    "web snapshot bad timestamp": passage(WEB, retrieved_at="2026-11-10"),
    "web snapshot bad hash": passage(WEB, text_sha256="sha256:" + "A" * 64),
    "web snapshot unknown encoding": passage(WEB, encoding="utf-9"),
    "web snapshot invalid iso encoding suffix": passage(WEB, encoding="iso-8859-1-typo"),
    "web snapshot invalid compact iso encoding suffix": passage(WEB, encoding="iso8859-1-typo"),
    "web snapshot two formats": passage(WEB, pdf_pages={"first": 1, "last": 1}),
    "web snapshot no format": passage(**{**WEB, "raw_text": None}),
    "web snapshot raw_text false": passage(WEB, raw_text=False),
    "web snapshot bad pdf pages": passage(**{**WEB, "raw_text": None},
                                          pdf_pages={"first": 2, "last": 1}),
    "web snapshot bad normalization": passage(**{**WEB, "raw_text": None},
                                              pdf_pages={"first": 1, "last": 1, "text_normalization": "x"}),
    "web snapshot empty selector": passage(**{**WEB, "raw_text": None}, html_selector={}),
    "web snapshot bad selector value": passage(**{**WEB, "raw_text": None}, html_selector={"heading": ""}),
    "web snapshot bad selector marker": passage(**{**WEB, "raw_text": None},
                                                html_selector={"from": {"anchor": "a"}, "to": {"id": "b"}}),
    "web snapshot bad selector keys": passage(**{**WEB, "raw_text": None}, html_selector={"to": {"text": "b"}}),
    "web snapshot bad translation": passage(WEB, translation={"translator": "T", "year": 2000}),
    "web snapshot translation not an object": passage(WEB, translation="T"),
    "web snapshot bad wayback": passage(WEB, wayback_url="https://web.archive.org/web/1id_/x"),
    "web snapshot wayback without hash": passage(
        **WEB, wayback_url="https://web.archive.org/web/20260101000000id_/https://example.org/page"),
    "web snapshot hash without wayback": passage(WEB, wayback_sha256=WEB["sha256"]),
    "web snapshot long incipit": passage(WEB, incipit="é" * 81),
    "web snapshot with text": passage(WEB, text="t"),
    "web snapshot bad unavailable": passage(WEB, unavailable={"since": "2026-11-05", "reason": "gone"}),
    "bibliographic missing field": passage(kind="bibliographic_span"),
    "bibliographic author not a string": passage(BIB, author=["A"]),
    "bibliographic bad year": passage(BIB, year=99),
    "bibliographic no publisher": passage(**{**BIB, "publisher": None}),
    "bibliographic no isbn or doi": passage(BIB, isbn=None, doi=None),
    "bibliographic bad isbn": passage(BIB, isbn="978-0-306-40615-8"),
    "bibliographic bad doi": passage(BIB, doi="11.1/x"),
    "bibliographic no locator": passage(**{**BIB, "pages": None}),
    "bibliographic short reason": passage(BIB, why_bibliographic="  copyrighted  "),
    "bibliographic long quotation": passage(BIB, quotation="q" * 301),
    "bibliographic bad translation": passage(BIB, translation={"translator": "", "year": 1, "edition": "e"}),
    "bibliographic with hash": passage(**BIB),
}

# Rules that leave the corpus valid: both report the same warnings.
CHECK_WARNINGS = {
    "allowlisted untagged sense": both(mutate("statements", "STMT-B", label="the t of b"),
                                       allowlisted("statements", "STMT-B")),
    "same label in two kinds": mutate("claims", "CLAIM-A", label="A"),
}


def write_check_fixture(root, change=None):
    """Write the fixture checkout with readable ids, convert it to uuid
    identity, apply `change` to the migrated records, and copy `scripts/*.py`
    so the unmodified Python validator runs against it."""
    records = check_records()
    configs = {result["id"]: {"challenge_module": result["challenge_module"],
                              "solution_module": result["solution_module"],
                              "theorem_names": [result["theorem"]], "permitted_axioms": [],
                              "enable_nanoda": True} for result in records["results"]}
    if change is not None and change.__code__.co_argcount == 2:
        change(None, configs)
        change = None
    allowlist = records.pop("sense_allowlist")
    (root / "corpus").mkdir(parents=True, exist_ok=True)
    (root / "corpus" / "sense-index-allowlist.json").write_text(json.dumps(allowlist))
    for kind, items in records.items():
        directory = root / "corpus" / kind
        directory.mkdir(parents=True, exist_ok=True)
        for index, record in enumerate(items):
            name = record.get("id", "x") if kind != "passages" else "p"
            (directory / f"{index:02d}-{name}.json").write_text(json.dumps(record, indent=2))
    for rid, config in configs.items():
        (root / "results" / rid).mkdir(parents=True, exist_ok=True)
        (root / "results" / rid / "comparator.json").write_text(json.dumps(config))
    for path, text in CHECK_LEAN.items():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_text(text)
    migrate(root)
    if change is not None:
        files = {kind: sorted((root / "corpus" / kind).glob("*.json")) for kind in records}
        migrated = {kind: [json.loads(path.read_text()) for path in paths] for kind, paths in files.items()}
        cleanup = root / "docs" / "notes" / "label-cleanup.json"
        migrated["_cleanup"] = json.loads(cleanup.read_text()) if cleanup.is_file() else []
        sense_path = root / "corpus" / "sense-index-allowlist.json"
        migrated["sense_allowlist"] = json.loads(sense_path.read_text())
        change(migrated)
        sense_path.write_text(json.dumps(migrated.pop("sense_allowlist")))
        cleanup.write_text(json.dumps(migrated.pop("_cleanup")))
        for kind, items in migrated.items():
            for index, record in enumerate(items):
                path = files[kind][index] if index < len(files[kind]) else root / "corpus" / kind / f"{index:02d}-new.json"
                path.write_text(json.dumps(record, indent=2))
    (root / "scripts").mkdir(exist_ok=True)
    for script in (corpus.ROOT / "scripts").glob("*.py"):
        shutil.copy(script, root / "scripts" / script.name)


def python_check(root):
    return subprocess.run([sys.executable, str(root / "scripts" / "corpus.py"), "check"],
                          capture_output=True, text=True, check=False)


class TruthCheckParity(ParityCase):
    """`truth check` against `corpus.py check`."""

    def truth_check(self, root):
        return subprocess.run([self.binary, "--root", str(root), "check"],
                              capture_output=True, text=True, check=False)

    def assert_same(self, root):
        python, rust = python_check(root), self.truth_check(root)
        if python.returncode == 0:
            self.assertEqual(rust.returncode, 0, rust.stderr)
            self.assertEqual(rust.stdout, python.stdout)
            self.assertEqual(rust.stderr, python.stderr)
            return python.stdout.strip()
        self.assertEqual(python.returncode, 2, python.stderr)
        self.assertEqual(rust.returncode, 1, rust.stderr)
        self.assertEqual(rust.stdout, "")
        self.assertEqual(rust.stderr, python.stderr)
        return python.stderr.strip()

    def test_real_corpus(self):
        python = subprocess.run([sys.executable, str(corpus.ROOT / "scripts" / "corpus.py"), "check"],
                                capture_output=True, text=True, check=False)
        rust = self.truth_check(corpus.ROOT)
        self.assertEqual(python.returncode, rust.returncode, rust.stderr)
        self.assertEqual(rust.stdout, python.stdout)
        # The lexicon check (#1652) is Rust-only; its summary line is appended last.
        lexicon = "warning: lexicon: "
        self.assertEqual("".join(line for line in rust.stderr.splitlines(keepends=True)
                                 if not line.startswith(lexicon)), python.stderr)
        machine = subprocess.run([self.binary, "--json", "check"], cwd=corpus.ROOT,
                                 capture_output=True, text=True, check=False)
        report = json.loads(machine.stdout)
        self.assertEqual(report["summary"], python.stdout.strip())
        self.assertEqual(report["warnings"], [line.removeprefix("warning: ")
                                              for line in python.stderr.splitlines()])

    def test_fixture_opaque_atom_warning(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_check_fixture(root)
            solution = root / "TruthCore" / "Fix" / "Solution.lean"
            solution.write_text(solution.read_text().replace(
                "theorem fixAB (h : fixA) : fixB := trivial",
                "theorem fixAB (A B : Prop) (h : A → B) (a : A) : B := h a"))
            self.assert_same(root)
            self.assertIn("looks like an unconstrained `Prop` atom", python_check(root).stderr)

    def test_fixture_reports_passing_label_cleanup_entries(self):
        def add_passing_entry(records):
            source = records["sources"][0]
            records["_cleanup"] = [{
                "kind": "source", "id": source["id"], "label": "Old mechanical source label",
                "flags": ["duplicate-label"],
            }]

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_check_fixture(root, add_passing_entry)
            self.assert_same(root)
            self.assertIn("label clean-up entry passes (label rewritten)", python_check(root).stderr)

    def test_fixture_passes_with_warnings(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_check_fixture(root)
            self.assertTrue(self.assert_same(root).startswith("corpus ok: 1 sources, 1 passages"))
            warnings = python_check(root).stderr
            for expected in ("does not count for closure rule (c)", "supports relation has no note",
                             "without strong_version_needed", "category predicate markConcrete",
                             "self_evident basis observation is not met",
                             "1 pre-existing argument(s) use several senses of one term",
                             "1 pre-existing sense(s) have no distinct Lean declaration"):
                self.assertIn(expected, warnings)
            self.assertNotIn("markAbstract", warnings)

    def test_fixture_identity_warnings(self):
        for name, change in CHECK_WARNINGS.items():
            with self.subTest(name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                write_check_fixture(root, change)
                self.assertTrue(self.assert_same(root).startswith("corpus ok: "), name)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_check_fixture(root, CHECK_WARNINGS["allowlisted untagged sense"])
            self.assertIn("allowlisted in docs/notes/label-cleanup.json", python_check(root).stderr)
    def test_conclusion_bridge_and_control_are_accepted(self):
        def change(records):
            # ARG-BC derives STMT-C (T_2) from STMT-B (T_1): its conclusion is a declared bridge.
            by_id(records, "arguments", "ARG-BC")["sense_bridges"] = [
                {"term": "T", "from": SENSE_X, "to": SENSE_Y, "statement_id": U("statement", "STMT-C"), "role": "conclusion"}]
            # A premise-free control mixing both senses is exempt, without an allowlist entry.
            records["inferences"].append({"id": U("inference", "INF-0C"), "label": "control inference", "input_statement_ids": [], "assumption_statement_ids": [],
                                          "discharged_statement_ids": [], "output_statement_id": U("statement", "STMT-C"),
                                          "rule": "model", "meaning": "m"})
            records["arguments"].append({"id": U("argument", "ARG-CONTROL"), "label": "control argument", "premise_statement_ids": [], "inference_ids": [U("inference", "INF-0C")],
                                         "conclusion_statement_id": U("statement", "STMT-C"), "meaning": "m",
                                         "definition_ids": [U("definition", "DEF-X")], "disambiguation_ids": [U("disambiguation", "DISAMB-T")],
                                         "sense_mixing_control": True})
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_check_fixture(root, change)
            self.assertTrue(self.assert_same(root).startswith("corpus ok: "))

    def test_uuid_identities_are_accepted(self):
        uuid = "44444444-4444-4444-8444-444444444444"
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            def change(records):
                mutate("attempts", "ATTEMPT-ONE", id=uuid, legacy_id=None)(records)
                records["_cleanup"] = [entry for entry in records["_cleanup"]
                                       if entry["id"] != U("attempt", "ATTEMPT-ONE")]
            write_check_fixture(root, change)
            self.assertTrue(self.assert_same(root).startswith("corpus ok: "))

    def test_fixture_failures(self):
        for name, change in CHECK_FAILURES.items():
            with self.subTest(name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                write_check_fixture(root, change)
                message = self.assert_same(root)
                self.assertTrue(message.startswith("corpus error: "), (name, message))
