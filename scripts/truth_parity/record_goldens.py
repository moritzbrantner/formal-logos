#!/usr/bin/env python3
"""Record the golden snapshots of the Python oracle (#954 slice R1).

    python3 scripts/truth_parity/record_goldens.py target/debug/truth

runs every fixture parity test (all but the real-corpus ones: test names
containing `real` and classes marked `real_corpus_only`) with recording on (`golden.record`), then, only if every
test passed, rewrites `truth/tests/golden/` from the Python outputs. The
Rust binary is needed because the recording run is the ordinary parity run:
a case is written only when Rust and Python agree on it today. Replay them
with `cargo test --locked -p truth --test golden`. See `golden.py` for the
format and its normalizations; regenerating twice gives identical files."""
import argparse
import sys
import unittest
from pathlib import Path

# Run from scripts/, as verify_truth_cli.py is: this directory's modules
# (check.py, issues.py, ...) must not shadow top-level imports.
sys.path[0] = str(Path(__file__).resolve().parents[1])

import verify_truth_cli  # noqa: E402  (imports every parity module)
from truth_parity import golden  # noqa: E402
from truth_parity.common import ParityCase  # noqa: E402


def fixture_tests(suite):
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            yield from fixture_tests(item)
        elif "real" not in item._testMethodName and not getattr(item, "real_corpus_only", False):
            yield item


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("binary", type=lambda path: Path(path).resolve())
    parser.add_argument("-k", dest="patterns", action="append", default=[],
                        help="record only tests whose id contains this text (writes nothing; for debugging)")
    options = parser.parse_args()
    ParityCase.binary = options.binary
    golden.RECORDING = True
    loaded = unittest.defaultTestLoader.loadTestsFromModule(verify_truth_cli)
    tests = [test for test in fixture_tests(loaded)
             if not options.patterns or any(pattern in test.id() for pattern in options.patterns)]
    result = unittest.TextTestRunner(verbosity=1).run(unittest.TestSuite(tests))
    if not result.wasSuccessful():
        print("recording failed: no golden file written", file=sys.stderr)
        return 1
    if options.patterns:
        count = sum(len(cases) for cases in golden.CASES.values())
        print(f"recorded {count} cases (not written: -k given)")
        return 0
    groups = golden.write_all()
    count = sum(len(cases) for cases in golden.CASES.values())
    print(f"wrote {count} cases in {len(groups)} files under {golden.GOLDEN.relative_to(golden.REPOSITORY)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
