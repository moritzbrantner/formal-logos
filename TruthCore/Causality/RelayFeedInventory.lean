module

public import TruthCore.Causality.RelayCutSensitivity
public import TruthCore.Logic.RegressHeadcount

@[expose] public section

namespace TruthCore.Causality.RelayFeedInventory

open TruthCore.Causality.RelayCutSensitivity (CutResponses RelayActivity)
open TruthCore.Logic.RegressHeadcount (SurvivesEveryFiniteAddition)

/-- A stipulated additive readout: each feed at a position strictly below
the prefix length contributes one separately reported unit. -/
noncomputable def unitFeedCount (feeds : ℕ → Prop) (length : ℕ) : ℕ := by
  classical
  exact Nat.rec 0 (fun i count => count + if feeds i then 1 else 0) length

/-- For arbitrary maintained feeds, the bottom report records whether some
feed is reachable below or at the cut. One feed and the entire tail starting
at that feed yield the same reports, with a strict headcount advantage when
the counted carriers are the maintained feed positions themselves. -/
def FeedInventoryComparison : Prop :=
  (∀ feeds : ℕ → Prop,
    RelayActivity (fun _ => True) feeds (fun _ => True) ∧
      ∃ response, CutResponses feeds response) ∧
  (∀ feeds response, CutResponses feeds response →
    ∀ i, response i 0 ↔ ∃ d ≤ i, feeds d) ∧
  (∀ d,
    (∀ single many, CutResponses (· = d) single → CutResponses (d ≤ ·) many →
      ∀ i, single i 0 ↔ many i 0) ∧
    SurvivesEveryFiniteAddition {n : ℕ // n = d} {n : ℕ // d ≤ n}) ∧
  (∀ feeds i, unitFeedCount feeds (i + 1) = unitFeedCount feeds i + 1 ↔ feeds i) ∧
  ∀ d, unitFeedCount (· = d) (d + 2) = 1 ∧ unitFeedCount (d ≤ ·) (d + 2) = 2

end TruthCore.Causality.RelayFeedInventory
