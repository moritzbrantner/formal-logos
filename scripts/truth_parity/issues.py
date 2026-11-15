"""`truth issues` and `truth dossier --issues-from` against `corpus.py issues`
and `corpus.py dossier --issues-from` (#949, #954 slice B3).

Both sides read the same offline snapshot: the recorded `gh issue list --json
number,title,body,url,comments` fixture in `fixtures/issues-snapshot.json`,
extended with acceptance blocks naming real corpus records, and the cases of
`test_issue_acceptance.py` on a fixture checkout. Neither side calls GitHub."""
import contextlib
import io
import json
import subprocess
import tempfile
from pathlib import Path

import corpus
from truth_parity.common import ParityCase

SNAPSHOT = Path(__file__).resolve().parent / "fixtures" / "issues-snapshot.json"


def acceptance(body, crlf=False):
    text = f"Notes before the contract.\n\n```truth-core-acceptance\n{body}\n```\n"
    return text.replace("\n", "\r\n") if crlf else text


@contextlib.contextmanager
def checkout(root):
    """`corpus.py` reading the checkout at `root` (its corpus, Lean files and aliases)."""
    saved = corpus.ROOT, corpus.CORPUS, corpus._ALIASES
    corpus.ROOT, corpus.CORPUS, corpus._ALIASES = root, root / "corpus", None
    try:
        yield
    finally:
        corpus.ROOT, corpus.CORPUS, corpus._ALIASES = saved


def python(args, root=None):
    """`corpus.py ARGS` exit code, stdout and stderr, on the checkout at `root`."""
    stdout, stderr = io.StringIO(), io.StringIO()
    with contextlib.ExitStack() as stack:
        if root is not None:
            stack.enter_context(checkout(root))
        stack.enter_context(contextlib.redirect_stdout(stdout))
        stack.enter_context(contextlib.redirect_stderr(stderr))
        code = corpus.main_with(args)
    return code, stdout.getvalue(), stderr.getvalue()


def write_fixture(root):
    """The records of `test_issue_acceptance.records()` as a checkout, with a
    proved STMT-P, a self-evident STMT-SE and a Solution module for RESULT-1."""
    def write(kind, record):
        directory = root / "corpus" / kind
        directory.mkdir(parents=True, exist_ok=True)
        (directory / f"{record['id']}.json").write_text(json.dumps(record))

    for statement in ("STMT-P", "STMT-Q", "STMT-R"):
        write("statements", {"id": statement, "paraphrase": statement})
    write("statements", {"id": "STMT-SE", "paraphrase": "SE", "self_evident": {"basis": None}})
    write("arguments", {"id": "ARG-P", "premise_statement_ids": [], "conclusion_statement_id": "STMT-P",
                        "inference_ids": ["INF"], "meaning": "m"})
    common = {"argument_id": "ARG-P", "challenge_module": "Demo.Challenge", "comparator_config": "c.json"}
    write("results", {"id": "RESULT-1", **common, "theorem": "TruthCore.Demo.proof",
                      "status": "solution-present", "solution_module": "Demo.Solution"})
    write("results", {"id": "RESULT-PENDING", **common, "theorem": "TruthCore.Demo.pending",
                      "status": "pending", "solution_module": "Demo.Solution"})
    # `verified` is not `solution-present`; its Solution module does not exist.
    write("results", {"id": "RESULT-NOSTATUS", **common, "theorem": "TruthCore.Demo.other",
                      "status": "verified", "solution_module": "Demo.Missing"})
    write("claims", {"id": "CLAIM-Q", "statement_id": "STMT-Q", "source_id": "SOURCE-1", "locator": "section 1",
                     "interpretation": "Reading", "status": "accepted"})
    write("configurations", {"id": "CONFIG-1", "seed_statement_id": "STMT-R",
                             "semantics": {"id": "SEM-1", "applications": {}}})
    write("attempts", {"id": "ATTEMPT-1", "outcome": "failed", "statement_ids": ["STMT-P"], "date": "2026-11-15",
                       "kind": "derivation", "summary": "s", "evidence": [], "blocker": "b"})
    write("attempts", {"id": "ATTEMPT-2", "statement_ids": [], "date": "2026-11-15",
                       "kind": "countermodel", "summary": "s"})
    (root / "corpus" / "relations").mkdir(parents=True, exist_ok=True)
    lean = root / "Demo" / "Solution.lean"
    lean.parent.mkdir(parents=True, exist_ok=True)
    lean.write_text("namespace TruthCore\nsection\nnamespace Demo\n"
                    "/- theorem pending : True := trivial -/\n"
                    "theorem proof : True := by trivial -- theorem other\n"
                    "end Demo\nend\nend TruthCore\n")


def issue(number, body="", **extra):
    return {"number": number, "title": f"Research #{number}", "body": body,
            "url": f"https://github.com/moritzbrantner/formal-logos/issues/{number}", **extra}


def fixture_issues():
    """Every case of `test_issue_acceptance.py`, plus fence, shape and status edge cases."""
    malformed = [
        "results: RESULT-1", "results: [RESULT-1]\nresults: [RESULT-1]", "unknown: [THING]",
        "statements: [STMT-P: magic]", "results: [RESULT-1, RESULT-1]",
        "statements: [STMT-P: closed, STMT-P: proved]", "results: []", "statements: [STMT-P]",
        "results: [bad id]", "# only a comment", "theorems: [TruthCore.Demo.proof, ]",
    ]
    items = [
        issue(9, acceptance("results: [RESULT-1]\ntheorems: [TruthCore.Demo.proof]\n"
                            "statements: [STMT-P: proved, STMT-Q: sourced]\n"
                            "configurations: [CONFIG-1]\nattempts: [ATTEMPT-1]")),
        issue(10, acceptance("results: [RESULT-PENDING]\nstatements: [STMT-R: closed]")),
        issue(11, "Needs research; no acceptance block yet."),
        issue(12, "Prose only", comments=[{"body": acceptance("statements: [STMT-Q: sourced]")}]),
        issue(4, acceptance("results: [RESULT-1]\nstatements: [STMT-Q: sourced]")),
        issue(7, acceptance("statements: [STMT-P: proved, STMT-Q: closed, STMT-R: sourced, STMT-SE: closed]\n"
                            "attempts: [ATTEMPT-2, ATTEMPT-MISSING]")),
        issue(13, acceptance("theorems: [TruthCore.Demo.pending, TruthCore.Demo.other, TruthCore.Demo.nosuch]")),
        issue(14, acceptance("results: [RESULT-1]", crlf=True)),
        issue(15, acceptance("results: [RESULT-1]"),
              comments=[{"body": acceptance("results: [RESULT-PENDING]", crlf=True)}]),
        issue(16, "```truth-core-acceptance\nresults: [RESULT-1]\n"),
        issue(17, acceptance("results: [RESULT-1]"), comments={"body": "not a list"}),
        issue(18, None, title=None, comments=None),
        issue(19, "```truth-core-acceptance  \n  results:\t[ RESULT-NOSTATUS ,RESULT-MISSING ]  \n\n```  \n",
              comments=["not an object", {"author": {"login": "x"}}]),
        issue(3, "```truth-core-acceptance\n```\n"),
    ]
    items += [issue(100 + index, acceptance(body)) for index, body in enumerate(malformed)]
    items.append(issue(20, acceptance("results: [RESULT-1]"),
                       comments=[{"body": acceptance("attempts: [ATTEMPT-1]")}]))
    duplicate = issue(9, acceptance("statements: [STMT-P: closed]"))
    duplicate.pop("url")
    items.append(duplicate)
    return items


class TruthIssuesParity(ParityCase):
    def truth(self, *args, code=0, root=None):
        result = subprocess.run([self.binary, *(["--root", str(root)] if root else []), *args],
                                cwd=corpus.ROOT, capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, code, (args, result.stderr))
        return result.stdout, result.stderr

    def truth_json(self, *args, root=None):
        value = json.loads(self.truth("--json", *args, root=root)[0])
        self.assertTrue(value.pop("input_identity").startswith("fnv1a64:"))
        return value

    def assert_issues(self, snapshot, root=None, extra=()):
        """Text and JSON of `issues --from SNAPSHOT [extra]` on both sides."""
        args = ["issues", "--from", str(snapshot), *extra]
        code, text, _ = python(args, root)
        self.assertEqual(code, 0)
        self.assertEqual(self.truth(*args, root=root)[0], text, extra)
        code, machine, _ = python([*args, "--json"], root)
        self.assertEqual(code, 0)
        expected = json.loads(machine)
        self.assertEqual(self.truth_json(*args, root=root), expected, extra)
        return expected

    def test_fixture_cases(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_fixture(root)
            snapshot = root / "issues.json"
            snapshot.write_text(json.dumps(fixture_issues()))
            before = snapshot.read_bytes()
            report = self.assert_issues(snapshot, root)
            self.assertEqual(snapshot.read_bytes(), before)
            # The fixture exercises what test_issue_acceptance.py checks.
            statuses = {}
            for entry in report["issues"]:
                statuses.setdefault(entry["number"], []).append(entry["status"])
            self.assertEqual(statuses[9], ["delivered", "delivered"])
            self.assertEqual([statuses[n] for n in (10, 11, 4, 12, 14)],
                             [["missing"], ["untracked"], ["delivered"], ["delivered"], ["delivered"]])
            self.assertTrue(all(statuses[100 + i] == ["malformed"] for i in range(11)))
            self.assertEqual([statuses[n] for n in (15, 16, 17, 20, 3)], [["malformed"]] * 5)
            self.assertEqual(statuses[13], ["missing"])
            seven = next(entry for entry in report["issues"] if entry["number"] == 7)
            self.assertEqual([(r["id"], r["met"]) for r in seven["requirements"]],
                             [("STMT-P", True), ("STMT-Q", False), ("STMT-R", False), ("STMT-SE", True),
                              ("ATTEMPT-2", True), ("ATTEMPT-MISSING", False)])
            self.assertEqual(report["reverse_index"]["STMT-Q"], [4, 7, 9, 12])
            for selected in ("STMT-Q", "RESULT-1", "NOT-REFERENCED", ""):
                self.assert_issues(snapshot, root, ["--for", selected])
            # The Solution source decides a theorem requirement: without it, not delivered.
            (root / "Demo" / "Solution.lean").write_text("namespace TruthCore.Other\n"
                                                         "theorem proof : True := trivial\nend TruthCore.Other\n")
            report = self.assert_issues(snapshot, root)
            self.assertEqual(next(e for e in report["issues"] if e["number"] == 9)["status"], "missing")

    def test_dossier_issue_targets_on_the_fixture(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_fixture(root)
            snapshot = root / "issues.json"
            snapshot.write_text(json.dumps(fixture_issues()))
            for statement in ("STMT-Q", "STMT-P", "STMT-SE"):
                args = ["dossier", statement, "--issues-from", str(snapshot)]
                # Python's dossier names its frontier root --root; Rust's --root is the checkout.
                code, text, _ = python([*args, "--root", "STMT-P"], root)
                self.assertEqual(code, 0)
                self.assertIn("Issue targets (offline acceptance snapshot): ", text)
                args += ["--frontier-root", "STMT-P"]
                self.assertEqual(self.truth(*args, root=root)[0], text, statement)
                code, machine, _ = python([*args[:-2], "--root", "STMT-P", "--json"], root)
                self.assertEqual(self.truth_json(*args, root=root), json.loads(machine), statement)

    def real_snapshot(self, directory):
        """The recorded snapshot with acceptance blocks naming real records, by
        uuid, legacy id and label, in bodies and comments."""
        records = {kind: [record for _, record in corpus.load_dir(kind)]
                   for kind in ("statements", "claims", "results", "configurations", "attempts")}
        frontier = json.loads(subprocess.run([self.binary, "--json", "frontier"], cwd=corpus.ROOT,
                                             capture_output=True, text=True, check=True).stdout)
        closed = frontier["closed_statements"]
        proved = sorted(sid for sid, reason in closed.items() if reason == "proved")[:3]
        other = sorted(sid for sid, reason in closed.items() if reason != "proved")[:2]
        sourced = sorted({c["statement_id"] for c in records["claims"] if c.get("source_id") and c.get("locator")})
        present = [r for r in records["results"] if r.get("status") == "solution-present"][:4]
        absent = [r for r in records["results"] if r.get("status") != "solution-present"][:2]
        legacy = next(s for s in records["statements"] if s.get("legacy_id"))
        labelled = records["statements"][len(records["statements"]) // 2]
        issues = json.loads(SNAPSHOT.read_text())
        issues[0]["comments"].append({"body": acceptance(
            "results: [" + ", ".join(r["id"] for r in present + absent) + "]\n"
            "theorems: [" + ", ".join(r["theorem"] for r in present + absent) + ", TruthCore.NoSuch.theorem]\n"
            "statements: [" + ", ".join(f"{sid}: proved" for sid in proved + other) +
            f", {sourced[0]}: sourced, {sourced[-1]}: closed]")})
        issues[1]["body"] += "\n\n" + acceptance(
            f"statements: [{proved[0]}: closed, {legacy['legacy_id']}: closed]\n"
            "configurations: [" + ", ".join(r["id"] for r in records["configurations"][:3]) + "]\n"
            "attempts: [" + ", ".join(r["id"] for r in records["attempts"][:3]) + "]", crlf=True)
        issues.append(issue(2000, acceptance(f"statements: [{sourced[0]}: sourced]\nresults: [{present[0]['id']}]")))
        issues.append(issue(2001, acceptance("statements: [label with spaces: closed]")))
        path = Path(directory) / "issues.json"
        path.write_text(json.dumps(issues, ensure_ascii=False))
        return path, {"proved": proved[0], "sourced": sourced[0], "legacy": legacy, "labelled": labelled,
                      "result": present[0]["id"]}

    def test_real_corpus(self):
        with tempfile.TemporaryDirectory() as temporary:
            snapshot, picks = self.real_snapshot(temporary)
            report = self.assert_issues(snapshot)
            self.assertEqual(report["summary"], {"delivered": 1, "missing": 2, "malformed": 1, "untracked": 1})
            legacy = picks["legacy"]
            for token in (picks["proved"], picks["result"], legacy["legacy_id"], legacy["label"],
                          picks["labelled"]["id"], "NOT-REFERENCED"):
                self.assert_issues(snapshot, extra=["--for", token])
            for sid in (picks["proved"], picks["sourced"], picks["labelled"]["id"]):
                args = ["dossier", sid, "--issues-from", str(snapshot)]
                code, text, _ = python(args)
                self.assertEqual(code, 0)
                self.assertEqual(self.truth(*args)[0], text, sid)
                code, machine, _ = python([*args, "--json"])
                self.assertEqual(self.truth_json(*args), json.loads(machine), sid)
            code, machine, _ = python(["dossier", "--all", "--issues-from", str(snapshot)])
            everything = json.loads(self.truth("dossier", "--all", "--issues-from", str(snapshot))[0])
            self.assertEqual(everything, json.loads(machine))
            self.assertEqual([entry["number"] for entry in everything[picks["proved"]]["targeting_issues"]],
                             [8, 143])
            self.assertTrue(everything[picks["sourced"]]["targeting_issues"])
            # Without the flag the dossier is unchanged (no targeting_issues key).
            self.assertNotIn("targeting_issues", self.truth_json("dossier", picks["proved"]))
            # The recorded snapshot alone: every issue is untracked.
            self.assert_issues(SNAPSHOT)

    def test_errors(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            cases = {
                "missing.json": None,
                "invalid.json": "{not json",
                "object.json": json.dumps({"number": 1}),
                "scalar-item.json": json.dumps([1]),
                "zero.json": json.dumps([issue(0)]),
                "bool.json": json.dumps([issue(True)]),
                "float.json": json.dumps([issue(2.0)]),
                "no-number.json": json.dumps([{"title": "t"}]),
            }
            sid = corpus.DEFAULT_FRONTIER_ROOT
            for name, content in cases.items():
                path = directory / name
                if content is not None:
                    path.write_text(content)
                for args in (["issues", "--from", str(path)], ["dossier", sid, "--issues-from", str(path)]):
                    code, _, stderr = python(args)
                    self.assertEqual(code, 2, (name, args))
                    actual = self.truth(*args, code=2)[1]
                    if name == "invalid.json":
                        # serde_json words its parse errors differently from Python's json module.
                        prefix = "corpus error: issue list is not valid JSON: "
                        self.assertTrue(stderr.startswith(prefix) and actual.startswith(prefix), (stderr, actual))
                    else:
                        self.assertEqual(actual, stderr, (name, args))
                    error = json.loads(self.truth("--json", *args, code=2)[1])["error"]
                    self.assertEqual(error["code"], "corpus_error")
            # An unknown statement is reported before the snapshot is read, as in Python.
            args = ["dossier", "STMT-NO-SUCH", "--issues-from", str(directory / "missing.json")]
            self.assertEqual(python(args)[0], 2)
            self.assertEqual(json.loads(self.truth("--json", *args, code=3)[1])["error"]["code"], "unknown_id")

    def test_usage(self):
        snapshot = str(SNAPSHOT)
        for args in (["issues"], ["issues", "--from", ""], ["issues", "extra", "--from", snapshot],
                     ["issues", "--from", snapshot, "--frontier-root", "X"],
                     ["issues", "--from", snapshot, "--issues-from", snapshot],
                     ["issues", "--from", snapshot, "--limit", "2"],
                     ["status", "--from", snapshot], ["frontier", "--for", "X"],
                     ["related", "X", "--issues-from", snapshot], ["context", "X", "--issues-from", snapshot],
                     ["dossier", "X", "--from", snapshot], ["check", "--issues-from", snapshot],
                     ["thickness", "--issues-from", snapshot], ["issues", "--from"]):
            result = subprocess.run([self.binary, "--json", *args], cwd=corpus.ROOT,
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 2, args)
            self.assertEqual(json.loads(result.stderr)["error"]["code"], "usage", args)
        self.assertIn("never calls GitHub", self.truth("issues", code=2)[1])
