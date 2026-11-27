import TruthCore.Causality.AxiarchicGuidance
import TruthCore.Results.Causality.AxiarchicFoundation.Solution

namespace TruthCore.Results.Causality.AxiarchicGuidance

open TruthCore.Causality.AxiarchicGuidance
open TruthCore.Causality.GoodFavouring (Profile Tracks Fixed)
open TruthCore.Causality.AxiarchicFoundation (FavouringRealizedOnItems FavouringIrreflexive)

/-! ## Counterfactual guidance is a property of the profile and the value structure -/

/-! ## Self-application -/

/-- Self-application individuates at second order: if a bearer's second-order
favourings are realized on stand-ins and are irreflexive, then when it favours one
of its own favouring determinations over `d`, the stand-in of that determination
differs from the stand-in of `d`. The round-2 trilemma then applies to `d`
exactly as to a first-order candidate (the main theorem of round 2 is stated for
any candidate type, so with determinations as candidates it is the second-order
criterion). -/

/-! ## Control -/

open TruthCore.Causality.AxiarchicGuidance.Control

theorem guidanceTable : GuidanceTable := by
  sorry

end TruthCore.Results.Causality.AxiarchicGuidance
