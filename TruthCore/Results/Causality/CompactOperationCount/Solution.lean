module

public import TruthCore.Causality.OperationLocalFiniteness

@[expose] public section

namespace TruthCore.Results.Causality.CompactOperationCount

open TruthCore.Causality.OperationLocalFiniteness

/-- Mathlib's locally finite family/compact-intersection theorem counts
operation *indices*, even if distinct operations have the same time. -/
theorem compactOperationCount : CompactOperationCountCertificate := by
  intro Operation time a b hlocal
  exact finite_operations_in_compact_interval time hlocal a b

end TruthCore.Results.Causality.CompactOperationCount
