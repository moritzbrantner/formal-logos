"""Reference integrity of the #1660 reconciliation.

Two inference records with identical inputs, output and Lean step were
consolidated; their legacy ids must keep resolving to the survivors and no
argument may still name a retired id. The two Tractatus sources share a
Gutenberg work_urn but are distinct pinned witnesses and stay separate.
"""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from corpus_ids import Aliases, legacy_uuid  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
MERGED = {
    "INF-POE-EVIL-FROM-DUE-DEFICIENCY": "INF-CATHOLIC-EVIL-EXISTS",
    "INF-NO-SELF-CAUSE-FROM-PRIORITY": "INF-AQUINAS-ST-I-Q2-A3-NOTHING-EFFICIENT-CAUSE-OF-ITSELF",
}


def records(directory: str) -> list[dict]:
    return [json.loads(path.read_text(encoding="utf-8")) for path in sorted((ROOT / "corpus" / directory).glob("*.json"))]


class MergedLegacyIds(unittest.TestCase):
    def test_merged_inferences_resolve_to_survivors(self) -> None:
        aliases = Aliases.load(ROOT)
        for merged, survivor in MERGED.items():
            self.assertEqual(aliases.resolve(merged, ["inference"]), legacy_uuid("inference", survivor))

    def test_no_argument_names_a_retired_inference(self) -> None:
        retired = {legacy_uuid("inference", merged) for merged in MERGED}
        inferences = {record["id"] for record in records("inferences")}
        self.assertFalse(retired & inferences)
        for argument in records("arguments"):
            self.assertFalse(retired & set(argument.get("inference_ids", [])), argument["id"])

    def test_tractatus_witnesses_stay_distinct(self) -> None:
        sources = {record.get("legacy_id"): record for record in records("sources")}
        ogden, latex = sources["WITTGENSTEIN-TLP-OGDEN"], sources["WITTGENSTEIN-TRACTATUS"]
        self.assertEqual(ogden["work_urn"], latex["work_urn"])
        snapshots = {}
        for passage_file in records("passages"):
            snapshot = passage_file.get("snapshot", {})
            if snapshot.get("source_id") in (ogden["id"], latex["id"]):
                snapshots[snapshot["source_id"]] = snapshot
        self.assertNotEqual(snapshots[ogden["id"]]["source_url"], snapshots[latex["id"]]["source_url"])
        self.assertNotEqual(snapshots[ogden["id"]]["sha256"], snapshots[latex["id"]]["sha256"])


if __name__ == "__main__":
    unittest.main()
