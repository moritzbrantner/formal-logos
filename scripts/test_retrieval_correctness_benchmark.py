"""Harness oracle checks; no remote snapshot or installed truth binary needed."""
import importlib.util
import json
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / 'retrieval_correctness_benchmark.py'
spec = importlib.util.spec_from_file_location('retrieval_correctness_benchmark', SCRIPT)
bench = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bench)


class FixtureTests(unittest.TestCase):
    def test_fixture_excludes_oracle_and_exceeds_old_caps(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            shape = bench.fixture(root)
            self.assertGreater(shape['stress_records'], 200)
            self.assertGreater(shape['linked_note_files'], 16)
            self.assertGreater(shape['linked_note_sections'], 80)
            self.assertFalse((root / bench.ORACLE.name).exists())
            self.assertEqual(len(list((root / 'docs/notes').glob('witness-*.md'))), 24)
            self.assertIn('witness-00.md', (root / 'docs/notes/witness-23.md').read_text())

    def test_graph_recall_uses_node_identity_not_prose_tokens(self):
        oracle = {'graph_record_ids': ['wanted'], 'source_ids': ['source']}
        value = {'nodes': [{'id': 'decoy', 'kind': 'statements', 'label': 'wanted source', 'path': 'x'}],
                 'edges': []}
        metrics = bench.graph_metrics(value, oracle)
        self.assertEqual(metrics['explicit_graph_recall']['hits'], 0)
        self.assertEqual(metrics['source_coverage']['hits'], 0)

    def test_graph_failure_is_not_missing_capability(self):
        oracle = {'semantic_cases': []}
        failure = {'exit': 1, 'stderr': 'graph crashed', 'value': None}
        with patch.object(bench, 'invoke', return_value=failure):
            with self.assertRaises(RuntimeError):
                bench.evaluate(SCRIPT, SCRIPT.parent, oracle)

    def test_old_cli_is_reported_unavailable(self):
        oracle = {'semantic_cases': []}
        usage = {'exit': 2, 'stderr': json.dumps({'error': {
            'code': 'usage', 'message': 'Usage: truth status'}}), 'value': None}
        with patch.object(bench, 'invoke', return_value=usage):
            result = bench.evaluate(SCRIPT, SCRIPT.parent, oracle)
        self.assertEqual(result['graph']['capability'], 'unavailable')

    def test_oracle_distinguishes_all_semantic_traps(self):
        oracle = json.loads(bench.ORACLE.read_text())
        cases = {c['id']: c for c in oracle['semantic_cases']}
        self.assertTrue(cases['exact']['identical'])
        for name in ['converse', 'negation', 'temporal-sense', 'quantifier', 'timeless-endless']:
            self.assertFalse(cases[name]['identical'])
            self.assertTrue(cases[name]['reason'])


if __name__ == '__main__':
    unittest.main()
