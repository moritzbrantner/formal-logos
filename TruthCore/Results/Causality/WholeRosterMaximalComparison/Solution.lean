module

public import TruthCore.Causality.WholeRosterMaximalComparison
public import TruthCore.Results.Causality.WholeRosterFoundation.Solution
public import TruthCore.Results.Causality.MaximalGroundingAsymmetry.WholeRoster.Solution
public import TruthCore.Causality.DirectEsseRootRoute

@[expose] public section

namespace TruthCore.Results.Causality.WholeRosterMaximalComparison
open TruthCore.Causality.WholeRosterMaximalComparison
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing

theorem comparison : Comparison := by
  intro W B R m w InAct MoreIn CausesIn esse hPop hExisting hEsse hGenus hGrades hEM
  constructor
  · intro hWhole
    obtain ⟨n, hr⟩ :=
      TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists
        m w hPop hWhole hEM
    have hIdentity := TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot
      m w InAct MoreIn CausesIn esse n hr hEM hGenus hExisting hEsse
    intro a b ha _ hb hab _
    have hbIdentity := hIdentity b hb
    subst b
    exact hr.2 a ⟨ha.1, ha.2, hab⟩
  · intro hMaximal
    exact TruthCore.Results.Causality.MaximalGroundingAsymmetry.WholeRoster.wholeRoster
      m w InAct MoreIn CausesIn esse hPop hExisting hEsse
      (restrictGenus InAct MoreIn CausesIn esse hGenus)
      (restrictGrades InAct MoreIn esse hGrades) hEM hMaximal

end TruthCore.Results.Causality.WholeRosterMaximalComparison
