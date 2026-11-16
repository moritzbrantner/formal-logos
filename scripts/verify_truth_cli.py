#!/usr/bin/env python3
"""Compare the Rust CLI with the Python corpus code that remains until #954
slice R3: the structural view (`status`, `inspect`, `bridges`) against the
Python loaders, `check` (kept for `scripts/merge_queue.py`), `frontier` and
`frontier-diff` (the Python frontier is the base-revision engine of
`truth frontier-diff`, `thickness --base` and `orphans --base` when a
revision's `corpus.py` differs), `configuration-report` (live through a
recorded toolchain), `structure`/`structure-report` (from recorded
PropositionStructure output) and `strength-comparisons`/`strength-report`
(from recorded BindTypes, CheckStrength and PropositionStructure output).

The commands retired from Python in #954 R2 (navigation, gates and research:
`next`, `next-steps`, `thickness`, `related`, `dossier`, `context`, `issues`,
`bind-check`, `unused-premises`, `lean-reuse`, `attribution-check`,
`configurations`, `models`, `territory`, `bridge-experiments`, `senses`,
`index`, `orphans --base`, ...) have no Python oracle any more: their frozen
golden snapshots under `truth/tests/golden/` (`cargo test -p truth --test
golden`) carry it.

The tests live in the `truth_parity` package, one module per command; this
file is the entry point CI runs.

Fixtures are written with readable ids and then converted to uuid identity by
`migrate_uuid.Migration`, exactly as the corpus was; tests look records up by
`corpus_ids.legacy_uuid(kind, legacy id)`."""
import argparse
from pathlib import Path

from truth_parity.common import ParityCase
from truth_parity.structure import TruthParity  # noqa: F401
from truth_parity.frontier import TruthFrontierParity  # noqa: F401
from truth_parity.check import TruthCheckParity  # noqa: F401
from truth_parity.configuration_report import TruthConfigurationReportParity  # noqa: F401
from truth_parity.proposition_structure import TruthStructureParity  # noqa: F401
from truth_parity.strength import TruthStrengthParity  # noqa: F401


if __name__ == "__main__":
    import unittest

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=lambda path: Path(path).resolve())
    known, rest = parser.parse_known_args()
    ParityCase.binary = known.binary
    unittest.main(argv=[__file__, *rest])
