"""The Lean proof-use exporter behind `truth unused-premises` (#571) on a fixture.

`truth unused-premises` runs `scripts/UnusedPremises.lean` and joins its
per-hypothesis usage with bind-check (the join has the frozen goldens
`truth/tests/golden/proof_use/`). This test checks the exporter itself on
`scripts/testdata/unused-premises/Fixture.lean`, which imports only Init.
It restores the Lean-backed case of the retired `test_unused_premises.py`
(#954 R2), which tested the exporter through `corpus.py`.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "UnusedPremises.lean"
FIXTURE = ROOT / "scripts" / "testdata" / "unused-premises" / "Fixture.lean"
FIXTURE_NS = "TruthCore.UnusedPremisesFixture."


@unittest.skipUnless(shutil.which("lake"), "needs the Lean toolchain (lake)")
class UnusedPremisesToolTest(unittest.TestCase):
    def test_fixture_usage(self):
        with tempfile.TemporaryDirectory() as tmp:
            module_dir = Path(tmp) / "TruthCore"
            module_dir.mkdir()
            shutil.copy(FIXTURE, module_dir / "UnusedPremisesFixture.lean")
            names = ["plain", "viaHelper", "obt", "proj", "mtch", "haveUnused", "both"]
            tool_input = Path(tmp) / "input.json"
            tool_input.write_text(json.dumps({
                "modules": ["TruthCore.UnusedPremisesFixture"],
                "theorems": [FIXTURE_NS + name for name in names],
                "bundle_prefixes": [FIXTURE_NS + "Th"],
            }))
            script = (
                'lean --root="$1" -o "$1/TruthCore/UnusedPremisesFixture.olean" "$1/TruthCore/UnusedPremisesFixture.lean"'
                ' && LEAN_PATH="$1:$LEAN_PATH" lean --run "$2" "$3"'
            )
            completed = subprocess.run(
                ["lake", "env", "sh", "-c", script, "sh", tmp, str(TOOL), str(tool_input)],
                cwd=ROOT, capture_output=True, text=True, check=False,
            )
        self.assertEqual(completed.returncode, 0, completed.stderr or completed.stdout)
        described = {entry["theorem"].removeprefix(FIXTURE_NS): entry["hypotheses"]
                     for entry in json.loads(completed.stdout)}

        def flags(name: str) -> list:
            return [item.get("conjuncts_used", item["used"]) for item in described[name]]

        self.assertEqual(flags("plain"), [True, False])
        self.assertEqual(flags("viaHelper"), [True, False])
        self.assertEqual(flags("obt"), [[False, True, False]])
        self.assertEqual(flags("proj"), [[False, False, True]])
        self.assertEqual(flags("mtch"), [[True, False, False]])
        self.assertEqual(flags("haveUnused"), [True, False])
        self.assertEqual(flags("both"), [True, True])


if __name__ == "__main__":
    unittest.main()
