"""Replay the #1937 closure experiment using a snapshot and its frontier export."""

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from corpus_records import load_dir

ROOT = "53964cbe-5831-5812-af33-4d87896d47a7"
GOD = "8626f8a5-9531-5da7-9ebd-f901e74b1129"
GENUS = "d9fad785-40ab-555a-a1c1-5e39c9d50497"
GENUS_SIBLING = "12dc2662-e160-4031-bc7b-0772c2ed2476"
ASCENT = "d5a94eb1-72d2-53e0-9a52-9787b5b61a8d"
ASSEMBLIES = {
    "0acc8761-d1a5-45c7-9e66-5dbd92fe7a83",
    "65435527-e463-4895-8cec-e71bb4545736",
    "827fa9cd-2bfc-46b2-b8b4-476c18e85af1",
}


def close(seeds, rules, excluded):
    known = seeds - excluded
    while True:
        additions = {conclusion for _, conclusion, premises in rules
                     if conclusion not in excluded and premises <= known} - known
        if not additions:
            return known
        known.update(additions)


def compare(snapshot, frontier, modal_names, attributes_only):
    def records(kind):
        return [record for _, record in load_dir(kind, snapshot)]

    statements = {s["id"]: s for s in records("statements")}
    results = records("results")
    if attributes_only:
        results = [r for r in results if r["argument_id"] not in ASSEMBLIES]
    registered = {r["argument_id"] for r in results}
    arguments = {a["id"]: a for a in records("arguments")}
    rules = [(i, arguments[i]["conclusion_statement_id"], set(arguments[i]["premise_statement_ids"]))
             for i in sorted(registered)]

    transcriptions = set(frontier["transcription_results"])
    derived = {arguments[r["argument_id"]]["conclusion_statement_id"]
               for r in results if r["id"] not in transcriptions}
    ordinary = statements.keys() - derived
    cycles = {row["statement_id"] for row in frontier["items"] if row["ungrounded_cycle"]}
    fixed_seeds = set(frontier["established_statements"]) | cycles
    stated = {c["statement_id"] for c in records("claims") if c.get("statement_id")}
    supported = {r["object_id"] for r in records("relations") if r["predicate"] == "supports"}
    closed_transcriptions = {r["statement_id"] for r in frontier["closed_via_transcription"]}
    bases = {
        "route": fixed_seeds | stated | supported | ordinary,
        "strict": fixed_seeds | (ordinary - closed_transcriptions),
    }
    modal = {i for i, s in statements.items() if s.get("lean_declaration") in modal_names}
    both = {GENUS, GENUS_SIBLING}
    cuts = {"none": set(), "genus": {GENUS}, "both": both, "modal": modal,
            "modal+genus": modal | {GENUS}, "joint": modal | both,
            "joint+ascent": modal | both | {ASCENT}}
    rows = {}
    for basis, seeds in bases.items():
        for cut, excluded in cuts.items():
            known = close(seeds, rules, excluded)
            before_god = close(seeds, rules, excluded | {GOD})
            rows[f"{basis} {cut}"] = {
                "root": [i for i, c, p in rules if c == ROOT and c not in excluded and p <= known],
                "first_G": [i for i, c, p in rules if c == GOD and c not in excluded and p <= before_god],
            }
    return {"modal_statements": sorted(modal), "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path, help="Checkout containing corpus/")
    parser.add_argument("frontier", type=Path, help="truth frontier --json for that checkout")
    parser.add_argument("markers", type=Path, help="ModalBodies.lean output for the comparison roster")
    parser.add_argument("--attributes-only", action="store_true",
                        help="Withhold the three new assemblies before computing candidate leaves.")
    args = parser.parse_args()
    modal_names = set()
    for line in args.markers.read_text().splitlines():
        if not line.startswith("modal "):
            parser.error(f"unexpected classifier output: {line!r}")
        modal_names.add(line.removeprefix("modal "))
    report = compare(args.snapshot, json.loads(args.frontier.read_text()), modal_names,
                     args.attributes_only)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
