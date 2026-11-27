module

public import TruthCore.Causality.OriginDeletionIncompatibility

@[expose] public section

namespace TruthCore.Results.Causality.OriginDeletionIncompatibility

open TruthCore.Causality.OriginDeletionIncompatibility

/-- Deletion at `w` applied to the necessary concretum's witness gives an
accessible world lacking it, against its existence at every accessible world. -/
theorem deletionExcludesNecessaryConcrete : DeletionExcludesNecessaryConcrete := by
  intro W B m w hDel ⟨x, hConcrete, hExists, hNec⟩
  obtain ⟨u, hu, hAbsent⟩ := hDel w x hConcrete hExists
  exact hAbsent (hNec u hu)

end TruthCore.Results.Causality.OriginDeletionIncompatibility
