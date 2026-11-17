"""Offline fixtures exercise the public preparation boundaries without downloads."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("prepare_worker", Path(__file__).with_name("prepare-worker.py"))
worker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(worker)


def fixture_clone(root):
    root.mkdir()
    subprocess.run(["git", "init", "-q", str(root)], check=True)
    subprocess.run(["git", "-C", str(root), "remote", "add", "origin",
                    "https://github.com/moritzbrantner/truth-core.git"], check=True)
    subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                    "commit", "--allow-empty", "-qm", "fixture"], check=True)
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "bun.lock", "scripts/bootstrap-verifier.sh"):
        path = root / name
        path.parent.mkdir(exist_ok=True)
        path.touch()
    return root


class PreparationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = fixture_clone(Path(self.temp.name) / "clone")
        (self.root / "package.json").write_text(json.dumps({"workspaces": ["apps/*"]}))
        self.app = self.root / "apps/explorer"
        self.app.mkdir(parents=True)
        (self.app / "package.json").write_text("{}")

    def linked_worktree(self):
        # Runtime owns checkout creation; only this disposable Git fixture creates one.
        subprocess.run(["git", "-C", str(self.root), "add", "."], check=True)
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Fixture",
                        "-c", "user.email=fixture@example.invalid", "commit", "-qm", "inputs"], check=True)
        linked = self.root.parent / "linked"
        subprocess.run(["git", "-C", str(self.root), "worktree", "add", "--detach", str(linked)],
                       check=True, capture_output=True)
        return linked

    def test_linked_receipt_is_private_and_shared_config_unchanged(self):
        linked = self.linked_worktree()
        config = (self.root / ".git/config").read_bytes()
        self.assertEqual(worker.worker_clone(linked), linked)
        worker.reconcile(self.root, "bun", "main", lambda: "main", lambda: None)
        worker.reconcile(linked, "bun", "linked", lambda: "linked", lambda: None)
        main = self.root / ".git/truth-core-preparation.json"
        private = worker.git_directory(linked) / "truth-core-preparation.json"
        self.assertNotEqual(main, private)
        self.assertEqual(json.loads(main.read_text())["bun"]["inputs"], "main")
        self.assertEqual(json.loads(private.read_text())["bun"]["inputs"], "linked")
        self.assertEqual((self.root / ".git/config").read_bytes(), config)
        worker.validate_outputs(linked)

    def test_linked_target_accepts_independent_standalone_build_seed(self):
        linked = self.linked_worktree()
        warm = fixture_clone(self.root.parent / "independent-warm")
        for name in worker.SEED_INPUTS:
            (warm / name).write_bytes((linked / name).read_bytes())
        artifact = warm / ".lake/build/lib/lean/TruthCore.olean"
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"warm")
        worker.seed_build(linked, warm)
        copied = linked / ".lake/build/lib/lean/TruthCore.olean"
        self.assertEqual(copied.read_bytes(), b"warm")
        self.assertNotEqual(copied.stat().st_ino, artifact.stat().st_ino)
        self.assertFalse((self.root / ".lake").exists())

    def test_linked_preparation_runs_cache_and_cli_without_project_build(self):
        linked = self.linked_worktree()
        (linked / "lean-toolchain").write_text("leanprover/lean4:v4.35.0")
        calls = []

        def command(root, *args, **kwargs):
            calls.append(args)
            return "Lean (version 4.35.0, fixture)" if args == ("lean", "--version") else ""

        with patch.object(worker, "run", side_effect=command), \
                patch.object(worker.shutil, "which", return_value="tool"), \
                patch.object(worker, "check_packages") as packages, \
                patch.object(worker, "prepare_verifier"), \
                patch.object(worker, "prepare_bun"), \
                patch.object(worker, "prepare_cli") as cli:
            worker.prepare(linked)
        self.assertEqual([call for call in calls if call[0] != "git"],
                         [("lean", "--version"), ("lake", "exe", "cache", "get")])
        self.assertEqual(packages.call_count, 2)
        cli.assert_called_once_with(linked, None)

    def test_output_and_package_escape_rejected_before_acquisition(self):
        outside = self.root.parent / "outside"
        outside.mkdir()
        (self.root / "target").symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "unsafe checkout path"):
            worker.validate_outputs(self.root)
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "packagesDir": "../outside", "packages": [{"name": "pkg", "type": "git", "rev": "pin"}]}))
        with self.assertRaisesRegex(ValueError, "boundary"):
            worker.check_packages(self.root, acquiring=True)

    def test_verifier_tag_fetch_is_retained_for_offline_warm_reuse(self):
        upstream = self.root.parent / "upstream"
        subprocess.run(["git", "init", "-q", str(upstream)], check=True)
        subprocess.run(["git", "-C", str(upstream), "-c", "user.name=Fixture",
                        "-c", "user.email=fixture@example.invalid", "commit", "--allow-empty", "-qm", "fixture"], check=True)
        subprocess.run(["git", "-C", str(upstream), "tag", "v0.0.1"], check=True)
        cache = self.root.parent / "verifier-cache"
        subprocess.run(["git", "clone", "--quiet", "--no-tags", str(upstream), str(cache)], check=True)
        script = Path(__file__).with_name("bootstrap-verifier.sh").read_text()
        function = script[script.index("clone_at() {"):script.index("# lean4export tags")]
        command = ["bash", "-c", "set -euo pipefail\n" + function + 'clone_at "$1" "$2" "$3"',
                   "fixture", str(upstream), "v0.0.1", str(cache)]
        subprocess.run(command, check=True, capture_output=True)
        self.assertEqual(subprocess.check_output(["git", "-C", str(cache), "rev-parse", "HEAD"], text=True),
                         subprocess.check_output(["git", "-C", str(cache), "rev-parse", "v0.0.1^{commit}"], text=True))
        upstream.rename(upstream.with_name("unavailable-upstream"))
        subprocess.run(command, check=True, capture_output=True)

    def test_explicit_clone_and_symlink_guards(self):
        self.assertEqual(worker.worker_clone(self.root), self.root)
        for invalid in (self.root.parent, Path.home(), Path("/")):
            with self.assertRaises(ValueError):
                worker.worker_clone(invalid)
        link = self.root.parent / "alias"
        link.symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(ValueError):
            worker.worker_clone(link)
        (self.root / ".git").rename(self.root / "git-directory")
        (self.root / ".git").write_text("gitdir: ../git-directory")
        with self.assertRaises(ValueError):
            worker.worker_clone(self.root)

    def test_receipt_and_build_aliases_refused(self):
        outside = self.root.parent / "outside"
        outside.write_text("keep")
        receipt = self.root / ".git/truth-core-preparation.json"
        receipt.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "receipt"):
            worker.reconcile(self.root, "bun", "in", lambda: "out", lambda: None)
        self.assertEqual(outside.read_text(), "keep")
        receipt.unlink()
        os.link(outside, receipt)
        with self.assertRaisesRegex(ValueError, "receipt"):
            worker.reconcile(self.root, "bun", "in", lambda: "out", lambda: None)
        artifact = self.root / "target/release/truth"
        artifact.parent.mkdir(parents=True)
        os.link(outside, artifact)
        with self.assertRaisesRegex(ValueError, "aliased mutable"):
            worker.validate_outputs(self.root)

    def test_verifier_cache_cannot_target_shared_main_checkout(self):
        linked = self.linked_worktree()
        with patch.dict(os.environ, {"TRUTH_CORE_VERIFIER_HOME": str(self.root / "cache")}):
            with self.assertRaisesRegex(ValueError, "outside the checkout"):
                worker.prepare_verifier(linked)
        self.assertFalse((self.root / "cache").exists())

    def test_git_override_refused(self):
        with patch.dict("os.environ", {"GIT_DIR": str(self.root / ".git")}):
            with self.assertRaisesRegex(ValueError, "unset GIT_DIR"):
                worker.worker_clone(self.root)

    def test_stale_layout_removed_and_warm_layout_preserved(self):
        installs = [self.root / "node_modules", self.app / "node_modules"]
        for path in installs:
            (path / ".bun").mkdir(parents=True)
            (path / "stale").touch()
        calls = []

        def bun(root, *command, capture=False, env=None):
            if command == ("bun", "--version"):
                return "1.4.3\n"
            self.assertEqual(env["NODE_ENV"], "development")
            calls.append(command)
            for path in installs:
                self.assertFalse((path / "stale").exists())
            installs[0].mkdir(exist_ok=True)
            (installs[0] / "installed").touch(exist_ok=True)

        original_run = worker.run
        with patch.object(worker, "run", side_effect=lambda root, *cmd, **kw:
                          bun(root, *cmd, **kw) if cmd[0] == "bun" else original_run(root, *cmd, **kw)):
            worker.prepare_bun(self.root)
            before = (installs[0] / "installed").stat().st_ino
            worker.prepare_bun(self.root)
            self.assertEqual(before, (installs[0] / "installed").stat().st_ino)
            self.assertEqual(len(calls), 1)
        self.assertEqual(calls, [("bun", "--config=/dev/null", "install", "--linker=hoisted", "--frozen-lockfile")])

    def test_receipt_invalidates_missing_changed_outputs_and_inputs(self):
        installed = self.root / "installed"
        calls = []

        def acquire():
            calls.append("acquire")
            installed.write_text("valid")

        output = lambda: worker.install_digest([self.root / "output"])
        # Use the same real file-tree boundary as the Bun receipt.
        directory = self.root / "output"
        directory.mkdir()
        installed = directory / "installed"
        worker.reconcile(self.root, "bun", "inputs", output, acquire)
        receipt = self.root / ".git/truth-core-preparation.json"
        before = receipt.stat().st_mtime_ns
        worker.reconcile(self.root, "bun", "inputs", output, acquire)
        self.assertEqual(len(calls), 1)
        self.assertEqual(receipt.stat().st_mtime_ns, before)
        installed.unlink()
        worker.reconcile(self.root, "bun", "inputs", output, acquire)
        installed.write_text("changed output")
        worker.reconcile(self.root, "bun", "inputs", output, acquire)
        worker.reconcile(self.root, "bun", "new inputs", output, acquire)
        self.assertEqual(len(calls), 4)

    def test_all_cleanup_targets_checked_before_deletion(self):
        modules = self.root / "node_modules"
        (modules / ".bun").mkdir(parents=True)
        outside = self.root.parent / "outside"
        outside.mkdir()
        sentinel = outside / "keep"
        sentinel.touch()
        (self.app / "node_modules").symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ValueError):
            worker.prepare_bun(self.root)
        self.assertTrue((modules / ".bun").exists())
        self.assertTrue(sentinel.exists())

    def test_tracked_install_content_refused(self):
        path = self.root / "node_modules/keep"
        path.parent.mkdir()
        path.touch()
        subprocess.run(["git", "-C", str(self.root), "add", "node_modules/keep"], check=True)
        with self.assertRaises(ValueError):
            worker.prepare_bun(self.root)
        self.assertTrue(path.exists())

    def test_absent_post_install_output_never_records_readiness(self):
        with self.assertRaisesRegex(ValueError, "did not produce required artifacts"):
            worker.reconcile(self.root, "verifier", "inputs", lambda: None, lambda: None)
        self.assertFalse((self.root / ".git/truth-core-preparation.json").exists())

    def test_dirty_or_wrong_revision_dependency_refused(self):
        package = self.root / ".lake/packages/mathlib"
        (package / ".git").mkdir(parents=True)
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "packagesDir": ".lake/packages", "packages": [{"name": "mathlib", "type": "git", "rev": "pinned"}]}))
        # Use a real dependency checkout so Git cannot silently discover the parent repo.
        (package / ".git").rmdir()
        package.rmdir()
        fixture_clone(package)
        pin = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
        with self.assertRaisesRegex(ValueError, "revision mismatch"):
            worker.check_packages(self.root)
        worker.check_packages(self.root, acquiring=True)
        manifest = json.loads((self.root / "lake-manifest.json").read_text())
        manifest["packages"][0]["rev"] = pin
        (self.root / "lake-manifest.json").write_text(json.dumps(manifest))
        worker.check_packages(self.root)
        tracked = package / "tracked"
        tracked.write_text("original")
        subprocess.run(["git", "-C", str(package), "add", "tracked"], check=True)
        with self.assertRaisesRegex(ValueError, "modified pinned"):
            worker.check_packages(self.root)



class SeedBuildTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = fixture_clone(Path(self.temp.name) / "clone")
        self.warm = fixture_clone(Path(self.temp.name) / "warm")
        self.olean = self.warm / ".lake/build/lib/lean/TruthCore/Leaf.olean"
        self.olean.parent.mkdir(parents=True)
        self.olean.write_bytes(b"olean")

    def test_cli_seed_requires_matching_receipt_and_inputs(self):
        for root in (self.root, self.warm):
            (root / "Cargo.toml").write_text("workspace")
            (root / "Cargo.lock").write_text("locked")
            (root / "truth/src").mkdir(parents=True)
            (root / "truth/src/main.rs").write_text("fn main() {}")
        original_run = worker.run
        builds = []

        def fake(root, *command, **kwargs):
            if command == ("rustc", "-vV"):
                return "same compiler and host"
            if command[0] == "cargo":
                builds.append(root)
                binary = root / "target/release/truth"
                binary.parent.mkdir(parents=True, exist_ok=True)
                binary.write_bytes(b"CLI")
                binary.chmod(0o755)
                return None
            return original_run(root, *command, **kwargs)

        with patch.object(worker, "run", side_effect=fake):
            worker.prepare_cli(self.warm)
            worker.prepare_cli(self.root, self.warm)
            self.assertEqual(builds, [self.warm])
            copied = self.root / "target/release/truth"
            origin = self.warm / "target/release/truth"
            self.assertNotEqual(copied.stat().st_ino, origin.stat().st_ino)
            worker.prepare_cli(self.root, self.warm)
            self.assertEqual(builds, [self.warm])
            (self.root / "truth/src/main.rs").write_text("changed")
            worker.prepare_cli(self.root, self.warm)
            self.assertEqual(builds, [self.warm, self.root])

    def test_copies_absent_build_output_without_changing_the_source(self):
        before = worker.build_fingerprint(self.warm / ".lake/build")
        worker.seed_build(self.root, self.warm)
        copy = self.root / ".lake/build/lib/lean/TruthCore/Leaf.olean"
        self.assertEqual(copy.read_bytes(), b"olean")
        self.assertNotEqual(copy.stat().st_ino, self.olean.stat().st_ino)
        self.assertEqual(worker.build_fingerprint(self.warm / ".lake/build"), before)
        self.assertEqual(worker.build_fingerprint(self.root / ".lake/build"), before)
        self.assertFalse((self.root / ".lake/build.seeding").exists())

    def test_existing_build_output_is_kept(self):
        existing = self.root / ".lake/build/keep"
        existing.parent.mkdir(parents=True)
        existing.write_text("own")
        worker.seed_build(self.root, self.warm)
        self.assertEqual(existing.read_text(), "own")
        self.assertFalse((self.root / ".lake/build/lib").exists())

    def test_mismatched_build_inputs_refused(self):
        for name in worker.SEED_INPUTS:
            (self.warm / name).write_text("other")
            with self.assertRaisesRegex(ValueError, f"different {name}"):
                worker.seed_build(self.root, self.warm)
            (self.warm / name).write_text("")
        self.assertFalse((self.root / ".lake/build").exists())

    def test_unsafe_sources_refused(self):
        with self.assertRaisesRegex(ValueError, "different clone"):
            worker.seed_build(self.root, self.root)
        (self.olean.parent / "escape").symlink_to(self.root)
        with self.assertRaisesRegex(ValueError, "symlink"):
            worker.seed_build(self.root, self.warm)
        (self.olean.parent / "escape").unlink()
        external = self.root.parent / "external-cache"
        (self.warm / ".lake").rename(external)
        (self.warm / ".lake").symlink_to(external, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlinked build path"):
            worker.seed_build(self.root, self.warm)
        (self.warm / ".lake").unlink()
        (external).rename(self.warm / ".lake")
        own = self.root.parent / "own-lake"
        own.mkdir()
        (self.root / ".lake").symlink_to(own, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlinked build path"):
            worker.seed_build(self.root, self.warm)
        (self.root / ".lake").unlink()
        alias = self.root.parent / "alias"
        alias.symlink_to(self.warm, target_is_directory=True)
        with self.assertRaises(ValueError):
            worker.seed_build(self.root, alias)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_source_written_during_copy_discards_the_copy(self):
        original_run = worker.run

        def concurrent_writer(root, *command, **kwargs):
            result = original_run(root, *command, **kwargs)
            if command[0] == "cp":
                self.olean.write_bytes(b"rebuilt by another writer")
            return result

        with patch.object(worker, "run", side_effect=concurrent_writer):
            with self.assertRaisesRegex(ValueError, "changed during the copy"):
                worker.seed_build(self.root, self.warm)
        self.assertFalse((self.root / ".lake/build").exists())
        self.assertFalse((self.root / ".lake/build.seeding").exists())


if __name__ == "__main__":
    unittest.main()
