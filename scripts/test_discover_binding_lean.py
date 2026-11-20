"""The binding policy of `scripts/Discover.lean` (`truth discover`) on fixtures.

A sense tag on a whole binder identifies two binders of different modules; a
tag with fixed arguments (`CausesIn _ _ esse`, key `sense|_ _ esse`) describes
only that partial application and must never identify the full relations
(Codex P1 on #1796, AGENTS.md invariant 9). The fixture modules in
`scripts/testdata/discover-binding/` import only Init; the scratch file is
assembled as `truth discover` assembles it (`scratch_text` in
`truth/src/discover.rs`), with the transcription probe stubbed because no
target here reaches it as a finding.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "Discover.lean"
FIXTURES = ROOT / "scripts" / "testdata" / "discover-binding"
DUPER = ROOT / ".lake" / "packages" / "Duper" / ".lake" / "build" / "lib" / "lean" / "Duper.olean"
MODULES = ["DiscoverFixtureTarget", "DiscoverFixturePremise"]
TARGET = "TruthCore.DiscoverFixtureTarget.Target"
PREMISE = "TruthCore.DiscoverFixturePremise.Premise"


def skip_reason() -> str | None:
    if os.environ.get("TRUTH_CORE_LEAN_TESTS") == "false":
        return "Lean integration tests are outside this metadata-only CI job"
    if not shutil.which("lake"):
        return "needs the Lean toolchain (lake)"
    if not DUPER.is_file() and not os.environ.get("CI"):
        return "needs Duper built (`lake build Duper`)"
    return None


def lean_string(text: str) -> str:
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def tags(relation_key: str) -> list[list[str]]:
    rows = []
    for decl, relation in ((TARGET, "CausesIn"), (PREMISE, "Causes")):
        rows += [[decl, "B", "carrier"], [decl, "a", "element"], [decl, relation, relation_key]]
    return rows


def scratch(commands: list[str]) -> str:
    body = "\n".join(line for line in TOOL.read_text().splitlines() if not line.startswith("import "))
    imports = ["Duper", "Lean"] + [f"TruthCore.{m}" for m in MODULES]
    return (
        "".join(f"import {m}\n" for m in imports)
        + '\nmacro "prove_sweep_probe" : tactic => `(tactic| fail "stub")\n\n'
        + body
        + "\nset_option maxHeartbeats 0\n\n"
        + "\n".join(commands)
        + "\n"
    )


def run(commands: list[str]) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        module_dir = Path(tmp) / "TruthCore"
        module_dir.mkdir()
        compile_steps = []
        for module in MODULES:
            shutil.copy(FIXTURES / f"{module}.lean", module_dir / f"{module}.lean")
            compile_steps.append(
                f'lean --root="$1" -o "$1/TruthCore/{module}.olean" "$1/TruthCore/{module}.lean"'
            )
        path = Path(tmp) / "Scratch.lean"
        path.write_text(scratch(commands))
        script = " && ".join(compile_steps) + ' && LEAN_PATH="$1:$LEAN_PATH" lean "$2"'
        completed = subprocess.run(
            ["lake", "env", "sh", "-c", script, "sh", tmp, str(path)],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
    if completed.returncode != 0:
        raise AssertionError(completed.stderr or completed.stdout)
    outcomes: dict = {}
    for line in completed.stdout.splitlines():
        if "DISCOVER-JSON " in line:
            value = json.loads(line.split("DISCOVER-JSON ", 1)[1])
            outcomes[value["label"]] = value
    return outcomes


@unittest.skipIf(skip_reason() is not None, skip_reason() or "")
class DiscoverBindingTest(unittest.TestCase):
    def test_partial_application_tags_never_identify_whole_binders(self):
        commands = [
            f'#discover "{label}" 20000 "" {lean_string(json.dumps({"tags": tags(key)}))} '
            f"{TARGET} from {PREMISE}"
            for label, key in (("whole", "cause"), ("partial", "cause|_ _ 0"))
        ]
        outcomes = run(commands)

        def froms(label: str) -> list[str]:
            return sorted(b["from"] for b in outcomes[label]["binders"])

        # A whole-binder tag identifies the two relations: one shared binder, so
        # the premise proves the target.
        self.assertEqual(froms("whole"), [f"{TARGET}.B", f"{TARGET}.CausesIn", f"{TARGET}.a"])
        self.assertIsNotNone(outcomes["whole"]["closed"])
        # The same tag only at `_ _ 0` leaves both full relations separate
        # binders: nothing equates them at respect `1`, which the goal needs,
        # so it is not found.
        self.assertEqual(
            froms("partial"),
            [f"{PREMISE}.Causes", f"{TARGET}.B", f"{TARGET}.CausesIn", f"{TARGET}.a"],
        )
        self.assertIsNone(outcomes["partial"]["closed"])
        self.assertEqual(outcomes["partial"]["domain_identified_by_name"], [])

    def test_premise_free_check_ignores_premise_only_binders(self):
        target = "TruthCore.DiscoverFixtureTarget.Inhabited'"
        premise = "TruthCore.DiscoverFixturePremise.HasElement"
        config = lean_string(json.dumps({"tags": [[premise, "B", "carrier"], [target, "B", "carrier"]]}))
        outcome = run([f'#discover "nonempty" 20000 "" {config} {target} from {premise}'])["nonempty"]
        # `x : B` comes only from the premise: the target is no theorem of its
        # vocabulary, though the goal with the premise (which binds `x`) closes.
        self.assertIsNone(outcome["alone"])
        self.assertIsNotNone(outcome["closed"])


if __name__ == "__main__":
    unittest.main()
