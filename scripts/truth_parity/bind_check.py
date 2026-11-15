"""`truth bind-check` against `corpus.py bind-check`.

Both run on the `check` fixture checkout (with a copy of `scripts/*.py`)
from the same recorded `scripts/BindTypes.lean` output (`--lean-json`), so
no Lean runs here: stdout must be byte-identical in text and `--json` mode,
and stderr and the exit code must agree. The cases cover a scoped success,
the full run's stale pins, unbound and missing hypotheses, theory-bundle
unfolding, consistency conclusions and their commitments, pinned and
undeclared logical-form bindings, schema registrations, sense problems and
aliases, exact-expression contracts, scoped runs and validate-first. One
real-corpus test compares the exporter input byte for byte and, given
`TRUTH_BIND_LEAN_JSON` (a recorded exporter output for this checkout), both
reports."""
import copy
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import corpus
from truth_parity.check import SENSE_X, SENSE_Y, by_id, write_check_fixture
from truth_parity import golden
from truth_parity.common import U, ParityCase

FIX = "TruthCore.Fix."


def hyp(name, decl, senses=(), **extra):
    """A propositional binder whose type has head `TruthCore.Fix.<decl>`."""
    head = decl if decl is None or "." in decl or decl in ("Exists", "Not") else FIX + decl
    return {"name": name, "prop": True, "head": head, "type": extra.pop("type", decl), "senses": list(senses), **extra}


def outcome(decl, senses=(), **extra):
    return hyp("", decl, senses, **extra) | {"name": None}


def described():
    """The exporter output for the fixture's two results, as Lean prints it."""
    return [
        {"theorem": FIX + "fixAB", "binders": [hyp("h", "fixA")], "result": outcome("fixB", [FIX + "fixB"])},
        {"theorem": FIX + "fixBC", "binders": [hyp("h", "fixB", [FIX + "fixB"])], "result": outcome("fixC")},
        {"sense_aliases": {}},
    ]


def entry(lean, theorem):
    return next(item for item in lean if item.get("theorem") == FIX + theorem)


def lean_change(function):
    """A case that changes only the recorded exporter output."""
    def apply(records, lean):
        function(lean)
    return apply


def record_change(function):
    """A case that changes the migrated records (and maybe the exporter output)."""
    def apply(records, lean):
        if records is not None:
            function(records, lean)
    apply.records = True
    return apply


def set_binders(theorem, *binders):
    return lean_change(lambda lean: entry(lean, theorem).update(binders=list(binders)))


def set_result(theorem, result):
    return lean_change(lambda lean: entry(lean, theorem).update(result=result))


def with_declared_y(records, lean):
    """Give sense T_2 the declaration fixC and drop it from the allowlist."""
    sense = by_id(records, "disambiguations", "DISAMB-T")["senses"][1]
    sense["lean_declaration"] = FIX + "fixC"
    records["sense_allowlist"]["senses_without_lean_declaration"] = []


def declared_y(extra=None):
    def apply(records, lean):
        with_declared_y(records, lean)
        entry(lean, "fixBC")["result"]["senses"] = [FIX + "fixC"]
        if extra is not None:
            extra(records, lean)
    return record_change(apply)


def without_declaration(name):
    def apply(records, lean):
        by_id(records, "statements", name).pop("lean_declaration")
    return apply


def commitments(records, lean):
    by_id(records, "arguments", "ARG-BC")["commitment_statement_ids"] = [U("statement", "STMT-D")]


def schema_registration(records, lean):
    records["relations"].append({
        "id": U("relation", "REL-SCHEMA"), "label": "fixture schema registration",
        "subject_kind": "statement", "subject_id": U("statement", "STMT-B"),
        "predicate": "instance_of_schema", "object_kind": "statement", "object_id": U("statement", "STMT-C"),
        "verification_result_id": U("result", "RES-AB"), "instance_theorem": FIX + "fixAB",
        "schema_theorem": FIX + "fixAB", "note": "fixture"})


# name -> (change, extra command-line arguments)
RES_AB = ["--result", "RES-AB"]
RES_BC = ["--result", "RES-BC"]
CASES = {
    "full run reports the unused pins as stale": (None, []),
    "scoped success": (None, RES_AB),
    "scoped run by label and uuid": (None, ["--result", "RES-AB", "--result", "RES-BC"]),
    "extra hypothesis and missing premise": (set_binders("fixAB", hyp("h", "fixD"), hyp("k", "fixE")), RES_AB),
    "vocabulary parameters are not premises": (
        set_binders("fixAB", {"name": "W", "prop": False, "head": None, "type": "Type", "senses": []},
                    hyp("h", "fixA")), RES_AB),
    "theory bundle unfolds to its conjuncts": (
        set_binders("fixAB", hyp("T", "TruthCore.Comparison.Theory", bundle=[hyp("", "fixA")])), RES_AB),
    "theory bundle with an unbound conjunct": (
        set_binders("fixAB", hyp("T", "TruthCore.Comparison.Theory",
                                 bundle=[hyp("", "fixA"), hyp("", "fixE")])), RES_AB),
    "theory bundle that failed to unfold": (
        set_binders("fixAB", hyp("T", "TruthCore.Comparison.Theory", bundle="unfold failed")), RES_AB),
    "theory conclusion without commitments": (
        set_result("fixAB", outcome("TruthCore.Comparison.Theory", bundle=[hyp("", "fixB")])), RES_AB),
    "consistency conclusion binds its commitments": (record_change(lambda records, lean: (
        commitments(records, lean),
        entry(lean, "fixBC").update(result=outcome("TruthCore.Comparison.Theory",
                                                   bundle=[hyp("", "fixD"), hyp("", "fixE")]))))
        , RES_BC),
    "commitments without a bundle": (record_change(commitments), RES_BC),
    "conclusion mismatch and non-Prop result": (
        set_result("fixAB", outcome("fixC") | {"prop": False}), RES_AB),
    "conclusion head of another declaration": (set_result("fixAB", outcome("fixC")), RES_AB),
    "logical-form conclusion without a pin": (record_change(lambda records, lean: (
        without_declaration("STMT-B")(records, lean),
        entry(lean, "fixAB").update(result=outcome("Exists", type="∃ x, fixB")))), RES_AB),
    "corpus head for an undeclared conclusion": (record_change(lambda records, lean: (
        without_declaration("STMT-B")(records, lean),
        entry(lean, "fixAB").update(result=outcome("fixC"))))
        , RES_AB),
    "logical-form premise without a pin": (record_change(lambda records, lean: (
        without_declaration("STMT-B")(records, lean),
        entry(lean, "fixBC").update(binders=[hyp("h", "Not", type="¬ fixE", senses=[])])))
        , RES_BC),
    "theorem missing from the exporter output": (
        lean_change(lambda lean: lean.remove(entry(lean, "fixAB"))), RES_AB),
    "exporter error entry": (lean_change(lambda lean: entry(lean, "fixAB").update(error="unknown constant")), RES_AB),
    "schema registration": (record_change(schema_registration), RES_AB),
    "sense without a Lean declaration": (None, ["--result", "RES-BC"]),
    "declared sense binds": (declared_y(), ["--result", "RES-BC"]),
    "declared sense description missing": (
        declared_y(lambda records, lean: entry(lean, "fixBC")["result"].pop("senses")), ["--result", "RES-BC"]),
    "declared sense not mentioned": (
        declared_y(lambda records, lean: entry(lean, "fixBC")["result"].update(senses=[])), ["--result", "RES-BC"]),
    "other sense mentioned outside a bridge": (declared_y(lambda records, lean: entry(lean, "fixBC").update(
        binders=[hyp("h", "fixB", [FIX + "fixB"]), hyp("k", "fixE", [FIX + "fixB"])])), ["--result", "RES-BC"]),
    "statement sense not instantiated": (declared_y(lambda records, lean: by_id(
        records, "statements", "STMT-C").update(definition_ids=[U("definition", "DEF-Y")]) or entry(
        lean, "fixBC")["binders"][0]["senses"].append(FIX + "fixC") or entry(
        lean, "fixBC")["result"].update(senses=[])), ["--result", "RES-BC"]),
    "sense aliases": (declared_y(lambda records, lean: lean[-1].update(
        sense_aliases={FIX + "fixB": FIX + "fixZ", FIX + "fixC": FIX + "fixZ"})), ["--result", "RES-BC"]),
    "affected without a base": (None, ["--affected"]),
    "base without affected": (None, ["--base", "HEAD"]),
    "unknown result": (None, ["--result", "RES-NONE"]),
    "validate first": (record_change(lambda records, lean: by_id(records, "arguments", "ARG-AB").update(
        conclusion_statement_id="STMT-MISSING")), RES_AB),
}


def write_contract(root, lean, *, tamper=False):
    """An exact-expression contract for RES-AB whose fingerprints match the
    recorded expression (or, with `tamper`, a changed dependency)."""
    expression = {"encoding": "closed-expression-v1", "universe_parameters": [],
                  "type": ["constant", FIX + "fixAB", []],
                  "dependencies": [{"declaration": FIX + "fixA", "value": ["sort", ["zero"]]},
                                   {"declaration": FIX + "fixB", "value": ["é"]}]}
    entry(lean, "fixAB")["expression_contract"] = expression

    def fingerprint(value):
        return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                         ensure_ascii=False).encode()).hexdigest()

    frozen = root / "TruthCore" / "Fix" / "Challenge.lean"
    contract = {
        "result_id": U("result", "RES-AB"), "theorem": FIX + "fixAB",
        "frozen_inputs": [{"path": "TruthCore/Fix/Challenge.lean",
                           "sha256": hashlib.sha256(frozen.read_bytes()).hexdigest()},
                          {"path": "TruthCore/Fix/Missing.lean", "sha256": "0" * 64}],
        "type_sha256": fingerprint([[], expression["type"]]),
        "dependencies": {item["declaration"]: fingerprint(item) for item in expression["dependencies"]},
    }
    if tamper:
        contract["dependencies"][FIX + "fixB"] = "0" * 64
        contract["type_sha256"] = "1" * 64
    (root / "scripts" / "contracts").mkdir(parents=True, exist_ok=True)
    (root / "scripts" / "contracts" / "fix.json").write_text(json.dumps(contract))


FAKE_LAKE = """#!/bin/sh
# Stands in for `lake`: requires every file argument to exist from the
# working directory it is run in, as the real Lean would.
if [ "$1" = build ]; then exit 0; fi
if [ "$3" = --run ]; then
  [ -f "$4" ] || { echo "missing exporter $4" >&2; exit 1; }
  [ -f "$5" ] || { echo "missing input $5" >&2; exit 1; }
  cat "$FAKE_DESCRIBED"; exit 0
fi
[ -f "$3" ] || { echo "missing certificates $3" >&2; exit 1; }
sed -n "s/^#print axioms \\(.*\\)/'FiniteModelCertificates.\\1' does not depend on any axioms/p" "$3"
"""


class TruthBindCheckParity(ParityCase):
    """`truth bind-check` against `corpus.py bind-check` from one exporter output."""

    def run_both(self, root, lean, extra):
        lean_path = root / "described.json"
        lean_path.write_text(json.dumps(lean, ensure_ascii=False))
        outputs = []
        for json_flag in ([], ["--json"]):
            arguments = ["bind-check", "--lean-json", str(lean_path), *json_flag, *extra]
            python = subprocess.run([sys.executable, str(root / "scripts" / "corpus.py"), *arguments],
                                    capture_output=True, text=True, check=False)
            # A corpus error is a JSON error object on stderr under --json.
            corpus_error = python.returncode == 2 and json_flag
            golden.record(self, ["--root", root, *arguments], root=root, code=python.returncode, stdout=python.stdout,
                          **({"error_message": python.stderr.removeprefix("corpus error: ").removesuffix("\n")}
                             if corpus_error else {"stderr": python.stderr}))
            rust = subprocess.run([self.binary, "--root", str(root), *arguments],
                                  capture_output=True, text=True, check=False)
            self.assertEqual(rust.returncode, python.returncode, (extra, python.stderr, rust.stderr))
            if python.returncode == 2 and json_flag:
                # Rust reports a corpus error as a JSON error object under --json.
                error = json.loads(rust.stderr)["error"]
                self.assertEqual(f"corpus error: {error['message']}\n", python.stderr)
            else:
                self.assertEqual(rust.stderr, python.stderr)
            self.assertEqual(rust.stdout, python.stdout)
            outputs.append(python)
        return outputs

    def resolve(self, extra):
        return [U("result", token) if token.startswith("RES-") and index % 2 else token
                for index, token in enumerate(extra)]

    def test_fixture_cases(self):
        for name, (change, extra) in CASES.items():
            with self.subTest(name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                lean = described()
                records_change = getattr(change, "records", False)
                write_check_fixture(root, (lambda records: change(records, lean)) if records_change else None)
                if change is not None and not records_change:
                    change(None, lean)
                arguments = self.resolve(extra)
                if name == "scoped run by label and uuid":
                    arguments[1] = "RES-AB"  # a legacy alias, resolved by both
                text, machine = self.run_both(root, lean, arguments)
                if name == "full run reports the unused pins as stale":
                    self.assertEqual(text.returncode, 1)
                    self.assertEqual(len(json.loads(machine.stdout)["stale_pins"]), 2)
                if name in ("scoped success", "declared sense binds",
                            "theory bundle unfolds to its conjuncts", "vocabulary parameters are not premises"):
                    self.assertEqual(text.returncode, 0, text.stdout)
                if name == "validate first":
                    self.assertTrue(text.stderr.startswith("corpus error: "), text.stderr)

    def test_expression_contracts(self):
        for tamper in (False, True):
            with self.subTest(tamper=tamper), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                lean = described()
                write_check_fixture(root)
                write_contract(root, lean, tamper=tamper)
                text, machine = self.run_both(root, lean, self.resolve(RES_AB))
                kinds = {problem["kind"] for problem in json.loads(machine.stdout)["results"][0]["problems"]}
                expected = {"expression-contract-frozen-input"}
                if tamper:
                    expected |= {"expression-contract-type", "expression-contract-dependencies"}
                self.assertEqual(kinds, expected)
                broken = copy.deepcopy(lean)
                entry(broken, "fixAB")["expression_contract"]["encoding"] = "other"
                self.run_both(root, broken, self.resolve(RES_AB))

    def test_relative_root_runs_the_exporter_and_models(self):
        """A relative `--root` other than `.` (PR #1650 review): the exporter
        and certificate paths must name the files from the child's working
        directory, the checkout itself."""
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            root = parent / "checkout"
            root.mkdir()
            write_check_fixture(root)
            (root / "scripts" / "BindTypes.lean").write_text("-- exporter stand-in\n")
            described_path = parent / "described.json"
            described_path.write_text(json.dumps(described()))
            tools = parent / "bin"
            tools.mkdir()
            (tools / "lake").write_text(FAKE_LAKE)
            (tools / "lake").chmod(0o755)
            env = dict(os.environ, PATH=f"{tools}{os.pathsep}{os.environ['PATH']}",
                       FAKE_DESCRIBED=str(described_path))
            rust = subprocess.run([self.binary, "--root", "checkout", "--json", "bind-check"], cwd=parent,
                                  env=env, capture_output=True, text=True, check=False)
            self.assertEqual(rust.returncode, 1, rust.stderr)  # the fixture's unused pins are stale
            report = json.loads(rust.stdout)
            self.assertEqual(report["models"], {"models": 1, "certificates": 3, "axioms": []})
            self.assertEqual(len(report["stale_pins"]), 2)

    def test_real_corpus_exporter_input(self):
        """The exporter input is Python's byte for byte; with a recorded
        exporter output, the reports agree too."""
        sys.path.insert(0, str(corpus.ROOT / "scripts"))
        results = corpus.load_dir("results")
        schema = corpus.schema_binding_records([relation for _, relation in corpus.load_dir("relations")],
                                               {record["id"]: record for _, record in results})
        expected = json.dumps(corpus.bind_tool_input(results + [(corpus.ROOT, binding) for binding, _ in schema],
                                                     senses=True))
        rust = subprocess.run([self.binary, "--root", str(corpus.ROOT), "bind-check", "--print-lean-input"],
                              capture_output=True, text=True, check=True)
        self.assertEqual(rust.stdout, expected + "\n")
        recorded = os.environ.get("TRUTH_BIND_LEAN_JSON")
        if not recorded:
            self.skipTest("set TRUTH_BIND_LEAN_JSON to a recorded BindTypes output for this checkout")
        for json_flag in ([], ["--json"]):
            arguments = ["bind-check", "--lean-json", recorded, *json_flag]
            python = subprocess.run([sys.executable, str(corpus.ROOT / "scripts" / "corpus.py"), *arguments],
                                    capture_output=True, text=True, check=False)
            rust = subprocess.run([self.binary, "--root", str(corpus.ROOT), *arguments],
                                  capture_output=True, text=True, check=False)
            self.assertEqual(rust.returncode, python.returncode)
            self.assertEqual(rust.stdout, python.stdout)
