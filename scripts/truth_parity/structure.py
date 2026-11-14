"""`truth status`, `inspect` and `bridges`: the structural view, errors,
the corpus boundary and the bridges contract."""
import json
import subprocess
import tempfile
from pathlib import Path

import corpus
import source_evidence
from truth_parity.common import U, migrate, ParityCase


class TruthParity(ParityCase):
    def invoke(self, *args, code=0):
        result = subprocess.run(
            [self.binary, "--json", *args], cwd=corpus.ROOT,
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(result.returncode, code, result.stderr)
        return json.loads(result.stderr if code else result.stdout)

    def test_real_status_and_inspect(self):
        expected = corpus.validate()
        status = self.invoke("status")
        for kind, count in status["counts"].items():
            oracle = expected[kind] if kind in expected else len(corpus.load_dir(kind))
            self.assertEqual(count, oracle, kind)

        records = {}
        for kind in status["counts"]:
            entries = source_evidence.load_passages() if kind == "passages" else corpus.load_dir(kind)
            for path, record in entries:
                records.setdefault(record["id"], []).append({
                    "kind": kind, "path": path.relative_to(corpus.ROOT).as_posix(), "record": record,
                })
        # Ids are uuids, unique across kinds.
        self.assertFalse([key for key, entries in records.items() if len(entries) > 1])
        # Cover every kind with bounded CLI invocations.
        ids = {next(key for key, entries in records.items()
                    if any(entry["kind"] == kind for entry in entries))
               for kind, count in status["counts"].items() if count}
        for key in sorted(ids):
            result = self.invoke("inspect", key)
            self.assertEqual(result["matches"], records[key])
            self.assertEqual(result["input_identity"], status["input_identity"])
        # A legacy id or a label names the same record as its uuid.
        statement = records[corpus.DEFAULT_FRONTIER_ROOT][0]["record"]
        for token in (statement["legacy_id"], statement["label"], statement["label"].upper()):
            result = self.invoke("inspect", token)
            self.assertEqual((result["id"], result["matches"]),
                             (corpus.DEFAULT_FRONTIER_ROOT, records[corpus.DEFAULT_FRONTIER_ROOT]))
        # A legacy id shared by an argument and its result names two records.
        legacy = {}
        for key, entries in records.items():
            alias = entries[0]["record"].get("legacy_id")
            if alias:
                legacy.setdefault(alias, set()).add(key)
        shared = next(alias for alias, keys in sorted(legacy.items()) if len(keys) > 1)
        error = self.invoke("inspect", shared, code=3)["error"]
        self.assertEqual(error["code"], "unknown_id")
        self.assertEqual({candidate["id"] for candidate in error["candidates"]}, legacy[shared])

    def test_errors_and_input_changes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / "corpus" / "statements"
            directory.mkdir(parents=True)
            path = directory / "a.json"
            args = ("--root", str(root))
            record = {"id": U("statement", "STMT-FIXTURE"), "label": "fixture", "paraphrase": "One"}
            path.write_text(json.dumps(record))
            first = self.invoke(*args, "status")["input_identity"]
            path.write_text(json.dumps({**record, "paraphrase": "Two"}))
            second = self.invoke(*args, "status")["input_identity"]
            self.assertNotEqual(first, second)
            self.assertEqual(self.invoke(*args, "inspect", "UNKNOWN", code=3)["error"]["code"],
                             "unknown_id")
            duplicate = directory / "z.json"
            duplicate.write_text(json.dumps(record))
            with self.assertRaisesRegex(corpus.CorpusError, "duplicate statement id"):
                corpus.index_by_id([(p, record) for p in (corpus.ROOT / "a.json", corpus.ROOT / "z.json")],
                                   "statement")
            error = self.invoke(*args, "status", code=1)["error"]
            self.assertEqual((error["code"], error["path"]),
                             ("duplicate_id", "corpus/statements/z.json"))
            duplicate.unlink()
            for value, error_code in [
                ("{", "invalid_json_object"), ("[]", "invalid_json_object"),
                ('{"id": 1}', "invalid_field"), (json.dumps({"id": record["id"]}), "invalid_field"),
            ]:
                path.write_text(value)
                self.assertEqual(self.invoke(*args, "status", code=1)["error"]["code"], error_code)

    def test_symlinks_cannot_escape_the_corpus_boundary(self):
        with tempfile.TemporaryDirectory() as temporary, tempfile.TemporaryDirectory() as outside:
            root = Path(temporary)
            directory = root / "corpus" / "statements"
            directory.mkdir(parents=True)
            foreign = Path(outside) / "foreign.json"
            foreign.write_text(json.dumps({"id": U("statement", "STMT-FOREIGN"), "label": "foreign",
                                           "paraphrase": "Not in corpus"}))
            link = directory / "linked.json"
            link.symlink_to(foreign)
            result = self.invoke("--root", str(root), "status", code=1)
            self.assertEqual(result["error"]["code"], "invalid_path")
            self.assertEqual(result["error"]["path"], "corpus/statements/linked.json")
            link.unlink()
            directory.rmdir()
            directory.symlink_to(Path(outside), target_is_directory=True)
            result = self.invoke("--root", str(root), "status", code=1)
            self.assertEqual(result["error"]["code"], "invalid_path")
            # The corpus directory itself may not be a symlink either.
            directory.unlink()
            (Path(outside) / "statements").mkdir()
            (Path(outside) / "statements" / "foreign.json").write_text(foreign.read_text())
            (root / "corpus").rmdir()
            (root / "corpus").symlink_to(Path(outside), target_is_directory=True)
            result = self.invoke("--root", str(root), "status", code=1)
            self.assertEqual((result["error"]["code"], result["error"]["path"]), ("invalid_path", "corpus"))

    def test_bridges_contract(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "corpus" / "statements").mkdir(parents=True)
            for sid, decl in [("STMT-T", "N.T"), ("STMT-A", "N.A")]:
                (root / "corpus" / "statements" / f"{sid}.json").write_text(
                    json.dumps({"id": sid, "paraphrase": sid, "lean_declaration": decl}))
            migrate(root)
            constants = root / "constants.json"
            constants.write_text(json.dumps([
                {"declaration": "N.T", "constants": ["N.P", "N.T"]},
                {"declaration": "N.A", "constants": ["N.A", "N.P"]},
            ]))
            args = ("--root", str(root), "bridges", "--constants", str(constants))
            # A target may be named by legacy id or uuid.
            for target in ("STMT-T", U("statement", "STMT-T")):
                report = self.invoke(*args, "--target", target)
                self.assertEqual(report["targets"][0]["statement_id"], U("statement", "STMT-T"))
                self.assertEqual(report["targets"][0]["singles"][0]["statement_ids"],
                                 [U("statement", "STMT-A")])
            self.assertIn("NOT a proof", report["mode"])
            self.assertEqual(self.invoke(*args, code=2)["error"]["code"], "usage")
            self.assertEqual(self.invoke(*args, "--target", "STMT-X", code=3)["error"]["code"],
                             "unknown_id")
            self.assertEqual(self.invoke("--root", str(root), "status", "--top", "2", code=2)
                             ["error"]["code"], "usage")

    def test_non_utf8_root_path_is_accepted(self):
        import os

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(os.fsdecode(os.fsencode(temporary) + b"/root-\xff"))
            (root / "corpus" / "statements").mkdir(parents=True)
            (root / "corpus" / "statements" / "a.json").write_text(
                json.dumps({"id": U("statement", "STMT-FIXTURE"), "label": "fixture", "paraphrase": "One"})
            )
            result = subprocess.run(
                [self.binary, "--json", "--root", os.fsencode(str(root)), "status"],
                capture_output=True, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)["counts"]["statements"], 1)
