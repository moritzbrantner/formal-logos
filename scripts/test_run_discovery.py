"""Smoke tests for the local Duper runner, using a stub truth CLI."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / 'scripts/run-discovery.sh'


class RunDiscoveryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.work = Path(self.tmp.name)
        self.stub = self.work / 'truth-stub'
        self.stub.write_text('''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
Path(os.environ['DISCOVERY_TEST_ARGS']).write_text(json.dumps(sys.argv[1:]))
print(json.dumps({'summary': {
    'targets': 2, 'proved': 1, 'discoveries': 1,
    'incompatibilities': 0, 'missing_bridges': 3,
    'unresolved': 1, 'errors': int(os.environ.get('DISCOVERY_TEST_ERRORS', '0')),
}}))
print('discover: stub progress', file=sys.stderr)
sys.exit(int(os.environ.get('DISCOVERY_TEST_EXIT', '0')))
''')
        self.stub.chmod(0o755)
        self.out = self.work / 'reports with spaces'
        self.args_file = self.work / 'args.json'
        self.env = {**os.environ,
                    'TRUTH_CORE_VERIFIER_HOME': str(self.work / 'verifier'),
                    'TRUTH_DISCOVER_BIN': str(self.stub),
                    'TRUTH_DISCOVER_REPORT_DIR': str(self.out),
                    'TRUTH_DISCOVER_LOCK': str(self.work / 'heavy.lock'),
                    'DISCOVERY_TEST_ARGS': str(self.args_file)}

    def invoke(self, *args, **env):
        return subprocess.run(['bash', str(RUNNER), *args], cwd=self.work,
                              env={**self.env, **env}, text=True, capture_output=True)

    def test_default_selection_and_saved_report(self):
        completed = self.invoke()
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(json.loads(self.args_file.read_text()),
                         ['--json', 'discover', '--targets', 'next-tests', '--limit', '30',
                          '--premise-pool', 'all'])
        runs = list(self.out.iterdir())
        self.assertEqual(len(runs), 1)
        self.assertEqual(json.loads((runs[0] / 'report.json').read_text())['summary']['discoveries'], 1)
        self.assertIn('stub progress', (runs[0] / 'stderr.log').read_text())
        self.assertIn('missing bridges: 3', completed.stdout)
        self.assertTrue((runs[0] / 'revision.txt').exists())

    def test_passes_custom_arguments_without_reinterpretation(self):
        completed = self.invoke('--target', 'abc', '--module', 'TruthCore.Causality',
                                '--premise-pool', 'closed')
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(json.loads(self.args_file.read_text()),
                         ['--json', 'discover', '--target', 'abc', '--module',
                          'TruthCore.Causality', '--premise-pool', 'closed'])

    def test_missing_cli_reports_build_command(self):
        completed = self.invoke(TRUTH_DISCOVER_BIN=str(self.work / 'missing'))
        self.assertEqual(completed.returncode, 2)
        self.assertIn('cargo build --locked --release -p truth', completed.stderr)
        self.assertFalse(self.out.exists())

    def test_preserves_failed_run_and_nonzero_status(self):
        completed = self.invoke(DISCOVERY_TEST_EXIT='19')
        self.assertEqual(completed.returncode, 19)
        self.assertIn('Discovery failed', completed.stderr)
        self.assertTrue(next(self.out.iterdir()).joinpath('stderr.log').exists())

    def test_reported_internal_errors_fail(self):
        completed = self.invoke(DISCOVERY_TEST_ERRORS='1')
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn('internal errors', completed.stderr)


if __name__ == '__main__':
    unittest.main()
