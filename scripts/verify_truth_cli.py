#!/usr/bin/env python3
"""Compare the Rust CLI with the existing Python corpus readers: the
structural view (`status`, `inspect`), `thickness [--queue]`, `check`,
`frontier`, `frontier-diff`, `thickness --base` and `orphans --base`
(against `scripts/orphan_summary.py`), the research navigation commands
`related`, `dossier` and `context`, `next`, `next-steps`, `arguments`,
`results`, `sort-lists`, `configurations --registered`, `models` and
`territory`, `senses` (against `scripts/sense_index.py`),
`bridge-experiments`, `bind-check` (from recorded BindTypes output), `unused-premises`,
`lean-reuse` and `context --proof-use` (from recorded UnusedPremises and
LeanReuse output), `structure`/`structure-report` (from recorded
PropositionStructure output), `strength-comparisons`/`strength-report` (from
recorded BindTypes, CheckStrength and PropositionStructure output), `issues`
with `dossier --issues-from`, and `attribution-check`.

The tests live in the `truth_parity` package, one module per command; this
file is the entry point CI runs.

Fixtures are written with readable ids and then converted to uuid identity by
`migrate_uuid.Migration`, exactly as the corpus was; tests look records up by
`corpus_ids.legacy_uuid(kind, legacy id)`."""
import argparse
from pathlib import Path

from truth_parity.common import ParityCase
from truth_parity.structure import TruthParity  # noqa: F401
from truth_parity.thickness import TruthThicknessParity  # noqa: F401
from truth_parity.frontier import TruthFrontierParity  # noqa: F401
from truth_parity.research import TruthResearchParity  # noqa: F401
from truth_parity.check import TruthCheckParity  # noqa: F401
from truth_parity.issues import TruthIssuesParity  # noqa: F401
from truth_parity.navigation import TruthNavigationParity  # noqa: F401
from truth_parity.configurations import TruthConfigurationParity  # noqa: F401
from truth_parity.bind_check import TruthBindCheckParity  # noqa: F401
from truth_parity.proposition_structure import TruthStructureParity  # noqa: F401
from truth_parity.proof_use import TruthProofUseParity  # noqa: F401
from truth_parity.revisions import TruthRevisionParity  # noqa: F401
from truth_parity.strength import TruthStrengthParity  # noqa: F401
from truth_parity.attribution import TruthAttributionParity  # noqa: F401
from truth_parity.senses import TruthSensesParity  # noqa: F401
from truth_parity.bridge_experiments import TruthBridgeExperimentsParity  # noqa: F401


if __name__ == "__main__":
    import unittest

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=lambda path: Path(path).resolve())
    known, rest = parser.parse_known_args()
    ParityCase.binary = known.binary
    unittest.main(argv=[__file__, *rest])
