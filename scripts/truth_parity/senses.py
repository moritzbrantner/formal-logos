"""`truth senses report|allowlist|ratchet` against `scripts/sense_index.py`
(#1233, #954 slice B6).

A fixture checkout (a Git repository) has arguments that mix the senses of a
term, one bridged by `sense_bridges`, one `sense_mixing_control`, a compound
term and senses without a distinct Lean declaration. Both sides read the same
tree: `report` text is byte-identical and its `--json` carries Python's
`corpus.sense_mixing` and `senses_without_distinct_declaration` entries;
`allowlist` (fresh, stale, `--write`) and `ratchet --base` (shrink-only: an
added entry fails, a removable one is listed, an allowlist new at the base, a
legacy-id key resolved through the aliases) match in stdout, stderr and exit
code. The real corpus is compared against a few base revisions."""
import contextlib
import io
import json
import shutil
import subprocess
import tempfile
import uuid
from pathlib import Path

import corpus
import sense_index
from truth_parity import golden
from truth_parity.common import U, ParityCase

S = {name: str(uuid.UUID(int=index + 1, version=4)) for index, name in enumerate(("P1", "P2", "P3", "M1", "M2"))}
D = {name: U("definition", name) for name in ("P1", "P2", "P3", "M1", "M2")}


def write(root, relative, value):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n" if not isinstance(value, str) else value)


def git(root, *args):
    subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True)


def commit(root, message="base"):
    git(root, "add", "-A")
    git(root, "-c", "user.name=t", "-c", "user.email=t@example.org", "commit", "-q", "-m", message)


def sense(name, label, declaration=None):
    record = {"id": S[name], "label": label, "definition_id": D[name]}
    if declaration:
        record["lean_declaration"] = declaration
    return record


def statement(legacy, *definitions):
    return {"id": U("statement", legacy), "label": legacy.lower(), "paraphrase": f"Statement {legacy}.",
            "definition_ids": [D[name] for name in definitions]}


def argument(legacy, conclusion, premises=(), **extra):
    record = {"id": U("argument", legacy), "label": legacy.lower(), "legacy_id": legacy,
              "conclusion_statement_id": U("statement", conclusion),
              "premise_statement_ids": [U("statement", p) for p in premises], "meaning": "m",
              "inference_ids": [str(U("inference", legacy))]}
    record.update(extra)
    return record


def fixture(root):
    for name in D:
        write(root, f"corpus/definitions/{name.lower()}.json", {"id": D[name], "label": f"def {name}", "term": "t",
                                                                  "definition": "d", "basis": "stipulative"})
    write(root, "corpus/disambiguations/prior.json", {
        "id": U("disambiguation", "PRIOR"), "label": "prior", "term": "prior", "resolution": "r", "term_label": "PRIOR",
        "sense_definition_ids": [D["P1"], D["P2"], D["P3"]],
        "senses": [sense("P1", "PRIOR_1", "TruthCore.Prior.one"), sense("P2", "PRIOR_2"),
                   sense("P3", "PRIOR_3", "TruthCore.Prior.one")]})
    write(root, "corpus/disambiguations/potency.json", {
        "id": U("disambiguation", "POTENCY"), "label": "potency", "term": "potency and mutability", "resolution": "r",
        "term_label": "POTENCY_AND_MUTABILITY",
        "sense_definition_ids": [D["M1"], D["M2"]],
        "senses": [sense("M1", "POTENCY_AND_MUTABILITY_1", "TruthCore.M.one"),
                   sense("M2", "POTENCY_AND_MUTABILITY_2", "TruthCore.M.two")]})
    for legacy, definitions in (("A", ("P1",)), ("B", ("P2",)), ("C", ("P1", "M1")), ("E", ("M2", "P3"))):
        write(root, f"corpus/statements/{legacy.lower()}.json", statement(legacy, *definitions))
    write(root, "corpus/arguments/mixed.json", argument("ARG-MIXED", "C", ("A", "B")))
    write(root, "corpus/arguments/three.json", argument("ARG-THREE", "E", ("A", "C")))
    write(root, "corpus/arguments/bridged.json", argument(
        "ARG-BRIDGED", "C", ("A", "B"),
        sense_bridges=[{"term": "PRIOR", "from": S["P1"], "to": S["P2"], "statement_id": U("statement", "B")}]))
    write(root, "corpus/arguments/control.json", argument("ARG-CONTROL", "E", definition_ids=[D["P1"]],
                                                            sense_mixing_control=True))
    write(root, "corpus/arguments/single.json", argument("ARG-SINGLE", "A"))


@contextlib.contextmanager
def checkout(root):
    saved = (corpus.ROOT, corpus.CORPUS, corpus._ALIASES)
    corpus.ROOT, corpus.CORPUS, corpus._ALIASES = root, root / "corpus", None
    try:
        yield
    finally:
        corpus.ROOT, corpus.CORPUS, corpus._ALIASES = saved


def python(args, root=None):
    """`sense_index.py ARGS`: exit code, stdout and stderr."""
    stdout, stderr = io.StringIO(), io.StringIO()
    with contextlib.ExitStack() as stack:
        if root is not None:
            stack.enter_context(checkout(root))
        stack.enter_context(contextlib.redirect_stdout(stdout))
        stack.enter_context(contextlib.redirect_stderr(stderr))
        code = sense_index.main(list(args))
    return code, stdout.getvalue(), stderr.getvalue()


class TruthSensesParity(ParityCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        fixture(self.root)
        git(self.root, "init", "-q")

    def rust(self, args, root=None, machine=False):
        root = root or self.root
        result = subprocess.run([self.binary, "--root", str(root), *(["--json"] if machine else []),
                                 "senses", *args], capture_output=True, text=True)
        return result.returncode, result.stdout, result.stderr

    def compare(self, *args, root=None, code=None):
        root = root or self.root
        expected = python(args, root=None if root == corpus.ROOT else root)
        if root != corpus.ROOT:
            golden.record(self, ["--root", root, "senses", *args], root=root, code=expected[0], stdout=expected[1],
                          stderr=expected[2])
            golden.record(self, ["--root", root, "--json", "senses", *args], root=root, code=expected[0])
        self.assertEqual(self.rust(args, root=root), expected)
        if code is not None:
            self.assertEqual(expected[0], code, expected)
        machine_code, _, _ = self.rust(args, root=root, machine=True)
        self.assertEqual(machine_code, expected[0])
        return expected

    def report_json(self, root):
        with checkout(root):
            mixing = sense_index.mixing()
            undeclared = sense_index.undeclared()
            disambiguations = corpus.load_dir("disambiguations")

        def relative(entry):
            return {**entry, "path": Path(entry["path"]).relative_to(root).as_posix()}

        golden.record(self, ["--root", root, "--json", "senses", "report"], root=root, code=0, json_paths={
            "mixing": [relative(entry) for entry in mixing],
            "senses_without_lean_declaration": [relative(entry) for entry in undeclared],
            "disambiguations": len(disambiguations)})
        code, out, err = self.rust(["report"], root=root, machine=True)
        self.assertEqual(code, 0, err)
        report = json.loads(out)

        self.assertEqual(report["mixing"], [relative(entry) for entry in mixing])
        self.assertEqual(report["senses_without_lean_declaration"], [relative(entry) for entry in undeclared])
        self.assertEqual(report["disambiguations"], len(disambiguations))
        return report

    def allowlist(self):
        """Write the allowlist both sides need now (Python `--write`)."""
        self.assertEqual(python(["allowlist", "--write"], root=self.root)[0], 0)
        return json.loads((self.root / corpus.SENSE_ALLOWLIST).read_text())

    def test_report(self):
        out = self.compare("report", code=0)[1]
        self.assertIn("| PRIOR_1, PRIOR_2 |", out)
        self.assertIn("POTENCY_AND_MUTABILITY_1, POTENCY_AND_MUTABILITY_2", out)
        report = self.report_json(self.root)
        self.assertEqual({entry["argument_id"] for entry in report["mixing"]},
                         {U("argument", "ARG-MIXED"), U("argument", "ARG-THREE")})
        self.assertEqual(sorted(entry["label"] for entry in report["senses_without_lean_declaration"]),
                         ["PRIOR_1", "PRIOR_2", "PRIOR_3"])

    def test_report_write(self):
        (self.root / "docs" / "notes").mkdir(parents=True)
        expected = python(["report"], root=self.root)[1]
        golden.record(self, ["--root", self.root, "senses", "report", "--write"], root=self.root, code=0, stdout="",
                      files={str(self.root / sense_index.NOTE): expected})
        self.assertEqual(self.rust(["report", "--write"])[:2], (0, ""))
        self.assertEqual((self.root / sense_index.NOTE).read_text(), expected)

    def test_allowlist_missing_stale_and_written(self):
        self.compare("allowlist", code=1)
        self.allowlist()
        self.compare("allowlist", code=0)
        write(self.root, "corpus/arguments/single.json", argument("ARG-SINGLE", "C", ("B",)))
        self.compare("allowlist", code=1)
        expected = python(["allowlist"], root=self.root)
        if golden.RECORDING:  # the file Python's `--write` leaves, on a copy of the checkout
            with tempfile.TemporaryDirectory() as temporary:
                copy = Path(temporary) / "copy"
                shutil.copytree(self.root, copy)
                written = python(["allowlist", "--write"], root=copy)
                golden.record(self, ["--root", self.root, "senses", "allowlist", "--write"], root=self.root,
                              code=written[0], stdout=written[1], stderr=written[2],
                              files={str(self.root / corpus.SENSE_ALLOWLIST): (copy / corpus.SENSE_ALLOWLIST).read_text()})
        self.assertEqual(self.rust(["allowlist", "--write"])[0], 0)
        self.assertEqual(python(["allowlist"], root=self.root)[0], 0, expected)
        self.compare("allowlist", code=0)

    def test_ratchet(self):
        self.compare("ratchet", "--base", "HEAD", code=0)  # no commit yet: nothing to compare
        data = self.allowlist()
        commit(self.root)
        self.compare("ratchet", "--base", "HEAD", code=0)
        # A removable entry: the argument no longer mixes.
        write(self.root, "corpus/arguments/mixed.json", argument("ARG-MIXED", "A"))
        out = self.compare("ratchet", "--base", "HEAD", code=0)[1]
        self.assertIn("no longer needed", out)
        # An added entry fails, also under a legacy-id key.
        grown = json.loads(json.dumps(data))
        grown["arguments"]["ARG-SINGLE"] = {"PRIOR": [S["P1"], S["P2"]]}
        write(self.root, corpus.SENSE_ALLOWLIST.as_posix(), json.dumps(grown, indent=2) + "\n")
        err = self.compare("ratchet", "--base", "HEAD", code=1)[2]
        self.assertIn("entry added", err)
        # The same entry under the uuid at the base is not an addition.
        rekeyed = json.loads(json.dumps(data))
        rekeyed["arguments"][str(U("argument", "ARG-SINGLE"))] = {"PRIOR": [S["P1"], S["P2"]]}
        write(self.root, corpus.SENSE_ALLOWLIST.as_posix(), json.dumps(rekeyed, indent=2) + "\n")
        commit(self.root, "rekeyed")
        write(self.root, corpus.SENSE_ALLOWLIST.as_posix(), json.dumps(grown, indent=2) + "\n")
        self.compare("ratchet", "--base", "HEAD", code=0)
        # A new undeclared sense allowlisted at head fails.
        grown["senses_without_lean_declaration"].append(S["M1"])
        write(self.root, corpus.SENSE_ALLOWLIST.as_posix(), json.dumps(grown, indent=2) + "\n")
        self.compare("ratchet", "--base", "HEAD", code=1)
        self.compare("ratchet", "--base", "no-such-revision", code=0)

    def test_real_corpus(self):
        self.compare("report", root=corpus.ROOT, code=0)
        self.compare("allowlist", root=corpus.ROOT)
        self.report_json(corpus.ROOT)
        compared = 0
        for revision in ("HEAD", "HEAD~1", "HEAD~25", "origin/main~40"):
            if subprocess.run(["git", "-C", str(corpus.ROOT), "rev-parse", "--verify", "-q", f"{revision}^{{commit}}"],
                              capture_output=True).returncode:
                continue
            with self.subTest(revision=revision):
                self.compare("ratchet", "--base", revision, root=corpus.ROOT)
                compared += 1
        self.assertGreater(compared, 0)
