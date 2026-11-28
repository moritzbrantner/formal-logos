module

public import TruthCore.Causality.DependenceOrderSenses
public import TruthCore.Causality.Round2PerfectionPrimacy

@[expose] public section

namespace TruthCore.Results.Causality.ExistentialRegressConnection

open TruthCore.Causality.DependenceOrderSenses
open TruthCore.Causality.Round2PerfectionPrimacy (PerfectionCausingInAnotherIsEfficient)
open TruthCore.Latin.Aquinas.DeEnte

/-- The explicit efficiency bridge maps the same distinct per se actual esse
edge into the present efficient relation at esse. Accessibility then transfers
along that subrelation. The profile and AsCaused are held fixed. -/
theorem actualRegressFromPresentEfficientRegress {B P R : Type} (p : Q3Profile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) (AsCaused : B → B → Prop)
    (hSeries : NoInfinitePerSeEsseEfficientCauseSeries EfficientlyCausesIn p.esse AsCaused)
    (hEfficient : PerfectionCausingInAnotherIsEfficient p.CausesIn EfficientlyCausesIn) :
    NoInfinitePerSeActualEsseCauseRegress p AsCaused := by
  constructor
  intro x
  apply Subrelation.accessible _ (hSeries x)
  intro c y h
  obtain ⟨⟨hne, _, _, hCause⟩, hPerSe⟩ := h
  exact ⟨hEfficient c y p.esse hne hCause, hPerSe⟩

end TruthCore.Results.Causality.ExistentialRegressConnection
