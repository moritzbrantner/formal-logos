#!/usr/bin/env python3
"""Offline retrieval tier with an oracle outside the indexed fixture.

Run: python3 scripts/retrieval_correctness_benchmark.py --truth BIN
     [--baseline BIN --json REPORT]. Timings are informational single samples.
The historical 24-case lexical benchmark remains in retrieval_benchmark.py.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ORACLE = ROOT / 'scripts/testdata/retrieval-correctness-oracle.json'
SEED = 'a8459a54-228d-545e-9e81-bf462fcca7a6'
SOURCE = 'd6c94a12-c779-59ba-90aa-2d42e1bbf47f'
PASSAGE = 'f450808a-6294-510d-ba2c-e5483c261dda'
CLAIM = 'b17df86a-c3a1-58b4-a0f7-7a391ef46cd1'


def write(root: Path, relative: str, value: str | dict) -> None:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value if isinstance(value, str) else json.dumps(value), encoding='utf-8')


def fixture(root: Path) -> dict:
    """Input content only: no expected rankings, classes, or answer key."""
    base = json.loads((ROOT / 'truth/tests/golden/research/test_fixture.json').read_text())['base']
    for relative, content in base.items():
        write(root, relative, content)
    sentences = [
        'Every mover moves only insofar as it is in act.',
        'Whatever begins to exist has a cause.',
        'God exists outside time.',
        'Act is prior to potency in account.',
        'Some contingent beings have explanations.',
    ]
    for i, sentence in enumerate(sentences):
        write(root, f'corpus/statements/semantic-{i}.json', {
            'id': f'90000000-0000-4000-8000-{i:012d}', 'label': sentence,
            'paraphrase': sentence, 'lean_declaration': f'Fixture.semantic{i}'})
    # More than the former 200-record expansion ceiling; every node points
    # back to the seed, so traversal must follow reverse references too.
    for i in range(220):
        sid = f'91000000-0000-4000-8000-{i:012d}'
        write(root, f'corpus/statements/stress-{i}.json', {
            'id': sid, 'label': f'Independent witness {i}',
            'paraphrase': f'An independent witness {i} cites {SEED}.',
            'lean_declaration': f'Fixture.witness{i}'})
    # 24 files / 96 explicitly linked sections, beyond both old note caps.
    for i in range(24):
        nxt = (i + 1) % 24
        sections = [f'## Witness {j}\n\nSeed `{SEED}`. Next '
                    f'[note](witness-{nxt:02d}.md).\n' for j in range(4)]
        write(root, f'docs/notes/witness-{i:02d}.md', '# Witness\n\n' + '\n'.join(sections))
    write(root, 'issues.json', {'captured_at': '2026-11-17T00:00:00Z', 'items': [
        {'number': 7001, 'title': 'Witness issue', 'body': f'Seed {SEED}. See #7002.',
         'state': 'CLOSED', 'url': 'https://example.org/issues/7001', 'comments': []},
        {'number': 7002, 'title': 'Witness pull request', 'body': 'See #7001.',
         'state': 'MERGED', 'url': 'https://example.org/pull/7002', 'comments': []}]})
    # The oracle is deliberately not copied into this root.
    return {'stress_records': 220, 'linked_note_files': 24, 'linked_note_sections': 96}


def invoke(binary: Path, root: Path, args: list[str]) -> dict:
    command = [str(binary), '--root', str(root), '--json', *args]
    start = time.perf_counter()
    proc = subprocess.run(command, capture_output=True, text=True, timeout=120)
    elapsed = time.perf_counter() - start
    value = None
    if proc.returncode == 0:
        value = json.loads(proc.stdout)
    return {'command': command, 'exit': proc.returncode, 'seconds': round(elapsed, 4),
            'bytes': len(proc.stdout.encode()), 'stdout_sha256': hashlib.sha256(proc.stdout.encode()).hexdigest(),
            'value': value, 'stderr': proc.stderr}


def ratio(hits: int, total: int) -> dict:
    return {'hits': hits, 'total': total, 'ratio': hits / total if total else None}


def evaluate(binary: Path, root: Path, oracle: dict) -> dict:
    rows = []
    for case in oracle['semantic_cases']:
        result = invoke(binary, root, ['novelty', case['query'], '--frontier-root', 'STMT-C'])
        if result['exit']:
            raise RuntimeError(result)
        value = result['value']
        hits = [h['id'] for h in value['hits'] if h.get('kind') == 'statements'][:5]
        relevant = set(case['relevant_statement_ids'])
        correct = len(set(hits) & relevant)
        result.update({'case': case['id'], 'semantic_recall_at_5': ratio(correct, len(relevant)),
                       'precision_at_5': ratio(correct, len(hits)),
                       'novelty_correct': (value['classification'] == 'already-recorded') == case['identical'],
                       'judgment': case['reason']})
        result['classification'] = value['classification']
        result['statement_candidates_at_5'] = hits
        del result['value']
        rows.append(result)
    graph = invoke(binary, root, ['evidence', SEED, '--limit', '1', '--issues-from', str(root / 'issues.json')])
    if graph['exit']:
        probe = invoke(binary, root, ['evidence', SEED])
        try:
            error = json.loads(probe['stderr'])['error']
        except (json.JSONDecodeError, KeyError):
            raise RuntimeError(probe)
        if error.get('code') != 'usage' or not error.get('message', '').startswith('Usage:') or ' evidence ' in error['message']:
            raise RuntimeError(probe)
        graph['capability_probe'] = {k: v for k, v in probe.items() if k != 'value'}
        graph['capability'] = 'unavailable'  # An old CLI is not a zero-recall graph implementation.
    else:
        graph['capability'] = 'available'
        graph['metrics'] = graph_metrics(graph['value'], oracle)
    del graph['value']
    return {'binary': str(binary), 'sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
            'binary_bytes': binary.stat().st_size, 'semantic_cases': rows, 'graph': graph,
            'summary': {
                'semantic_recall_at_5': ratio(sum(r['semantic_recall_at_5']['hits'] for r in rows),
                                               sum(r['semantic_recall_at_5']['total'] for r in rows)),
                'precision_at_5': ratio(sum(r['precision_at_5']['hits'] for r in rows),
                                        sum(r['precision_at_5']['total'] for r in rows)),
                'novelty_correctness': ratio(sum(r['novelty_correct'] for r in rows), len(rows))}}


def graph_metrics(value: dict, oracle: dict) -> dict:
    # Exact node identities are scored, never token appearance in JSON prose.
    nodes = value['nodes']
    ids = {node['id'] for node in nodes}
    paths = {node.get('path') for node in nodes}
    expected = oracle['graph_record_ids'] + [f'91000000-0000-4000-8000-{i:012d}' for i in range(220)]
    notes = [f'docs/notes/witness-{i:02d}.md' for i in range(24)]
    expected_edges = oracle.get('graph_edges', [])
    matched_edges = sum(any(e['from'] == wanted['from'] and e['to'] == wanted['to']
                            and e.get('provenance', {}).get('field') == wanted['field']
                            and e.get('provenance', {}).get('path') == wanted['path']
                            for e in value['edges']) for wanted in expected_edges)
    return {'edge_provenance_accuracy': ratio(matched_edges, len(expected_edges)),
            'explicit_graph_recall': ratio(sum(s in ids for s in expected), len(expected)),
            'note_file_recall': ratio(sum(s in paths for s in notes), len(notes)),
            'source_coverage': ratio(sum(s in ids for s in oracle['source_ids']), len(oracle['source_ids'])),
            'unique_node_keys': len({(n['kind'], n['id']) for n in nodes}) == len(nodes),
            'issue_pr_recall': ratio(sum(s in ids for s in ['7001', '7002']), 2),
            'node_count': len(nodes), 'edge_count': len(value['edges']),
            'linked_note_section_recall': ratio(sum(f'{p}#witness-{i}' in ids for p in notes for i in range(4)), 96),
            'edge_provenance_complete': all(e.get('provenance', {}).get('path')
                                            and e['provenance'].get('field')
                                            for e in value['edges'])}


def historical_fixture(root: Path) -> None:
    """Same live corpus bytes for both binaries; answer-bearing notes excluded."""
    shutil.copytree(ROOT / 'corpus', root / 'corpus')
    shutil.copytree(ROOT / 'docs/notes', root / 'docs/notes')
    historical = json.loads((ROOT / 'scripts/testdata/retrieval-benchmark.json').read_text())
    for relative in historical['evaluation_excludes']:
        path = root / relative
        if path.is_file():
            path.unlink()


def historical_evaluate(binary: Path, root: Path, oracle: dict) -> list[dict]:
    rows = []
    for case in oracle['historical_cases']:
        result = invoke(binary, root, ['novelty', case['query']])
        if result['exit']:
            raise RuntimeError(result)
        value = result['value']
        hits = value['hits']
        retrieved = {str(h.get('id', '')) for h in hits} | {str(h.get('path', '')) for h in hits}
        refs = case['relevant_references']
        result.update({'case': case['id'], 'judgment': case['reason'],
                       'known_work_recall': ratio(sum(any(ref in hit for hit in retrieved) for ref in refs), len(refs)),
                       'novelty_correct': value['classification'] in case['allowed_classifications']})
        result['classification'] = value['classification']
        result['retrieved_identity_count'] = len(retrieved)
        result['retrieved_identities_sha256'] = hashlib.sha256(json.dumps(sorted(retrieved)).encode()).hexdigest()
        result['retrieved_identity_sample'] = sorted(retrieved)[:20]
        result['matched_reference_identities'] = {ref: sorted(hit for hit in retrieved if ref in hit) for ref in refs}
        del result['value']
        rows.append(result)
    return rows


def source_manifest() -> dict:
    paths = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z', 'truth'],
        cwd=ROOT).decode().split('\0')
    files = [{'path': relative, 'sha256': hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()}
             for relative in sorted(set(paths)) if relative and (ROOT / relative).is_file()]
    encoded = json.dumps(files, sort_keys=True, separators=(',', ':')).encode()
    return {'sha256': hashlib.sha256(encoded).hexdigest(), 'files': files}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--truth', type=Path, required=True)
    parser.add_argument('--baseline', type=Path)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    oracle = json.loads(ORACLE.read_text())
    with tempfile.TemporaryDirectory(prefix='truth-retrieval-oracle-') as temporary:
        root = Path(temporary) / 'synthetic'
        shape = fixture(root)
        historical_root = Path(temporary) / 'historical'
        historical_fixture(historical_root)
        report = {'tier': 'independent-offline-correctness-v1',
                  'checkout_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  'checkout_diff_sha256': hashlib.sha256(subprocess.check_output(['git', 'diff', '--', 'truth'], cwd=ROOT)).hexdigest(),
                  'truth_source_manifest': source_manifest(),
                  'artifact_source_boundary': 'Binary hashes identify measured artifacts; checkout HEAD plus dirty diff identifies local source context, not a clean artifact revision.',
                  'oracle_sha256': hashlib.sha256(ORACLE.read_bytes()).hexdigest(),
                  'environment': {'platform': platform.platform(), 'python': platform.python_version()},
                  'workload': shape}
        for name, binary in [('baseline', args.baseline), ('candidate', args.truth)]:
            if binary:
                report[name] = evaluate(binary.resolve(), root, oracle)
                report[name]['historical_cases'] = historical_evaluate(binary.resolve(), historical_root, oracle)
    if args.json:
        args.json.write_text(json.dumps(report, indent=2) + '\n')
    for name in ['baseline', 'candidate']:
        if name in report:
            print(name, json.dumps(report[name]['summary']), 'graph',
                  json.dumps(report[name]['graph'].get('metrics', report[name]['graph']['capability'])))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
