module

public import TruthCore.Causality.DivineVeracityAssembly1732
public import TruthCore.Results.Causality.DivineVeracityContent1410.Solution

@[expose] public section
namespace TruthCore.Results.Causality.DivineVeracityAssembly1732
open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1
open TruthCore.Causality.DivineVeracity1410
open TruthCore.Causality.DivineVeracityContent1410
open TruthCore.Causality.DivineVeracityAssembly1732
open TruthCore.Logic.ReflectiveCoherence (Semantics)

/-- Route A assembled: sincerity, scoped accuracy and assertion coverage on one
content profile `C`, domain `D`, semantics `S` and world `w`, together with the
one-way representation of the given legacy attitudes `V` by that same `C`,
give the exact legacy target. Composes the checked `contentRouteA` and
`legacyAssertionFromContent`; no premise is restated as a conclusion. -/
theorem assertionTruthRouteA {World Content : Type} (σ : Signature)
    (S : Semantics World Content) (w : World)
    (C : Attitudes σ Content) (D : Content → Prop) (V : Veracity σ)
    (h0 : ContentSincere σ C) (h1 : ScopedAccuracy σ S w C D)
    (h2 : AssertionsInDomain σ C D)
    (h3 : AssertionRepresentation σ S w C V) : GodAssertsOnlyTruth σ V :=
  TruthCore.Results.Causality.DivineVeracityContent1410.legacyAssertionFromContent
    σ S w C V
    (TruthCore.Results.Causality.DivineVeracityContent1410.contentRouteA
      σ S w C D h0 h1 h2) h3

/-- Route B assembled: selected countertruth assent and no contrary assertion on
one content profile `C`, together with the one-way representation of `V` by
that same `C` at the same `S` and `w`, give the exact legacy target. Composes
`contentRouteB` (classical) and `legacyAssertionFromContent`. -/
theorem assertionTruthRouteB {World Content : Type} (σ : Signature)
    (S : Semantics World Content) (w : World)
    (C : Attitudes σ Content) (V : Veracity σ)
    (h0 : CounterComplete σ S w C) (h1 : NoContraryAssertion σ S C)
    (h2 : AssertionRepresentation σ S w C V) : GodAssertsOnlyTruth σ V :=
  TruthCore.Results.Causality.DivineVeracityContent1410.legacyAssertionFromContent
    σ S w C V
    (TruthCore.Results.Causality.DivineVeracityContent1410.contentRouteB
      σ S w C h0 h1) h2

open TruthCore.Causality.DivineVeracityContent1410.Control in
/-- Joint nonvacuity of the assembled chain at one bearer, world and content
profile (see `AssembledJointWitness`). Reuses the checked selective sample and
the erasure-representation theorem. -/
theorem assembledJointWitness : AssembledJointWitness := by
  obtain ⟨hG, hC, hAs, hSin, hAcc, hDom, _, _, hCC, hNC, _⟩ :=
    TruthCore.Results.Causality.DivineVeracityContent1410.controls.1
  have hRep := TruthCore.Results.Causality.DivineVeracityContent1410.erasureRepresented
    σ semantics false selective
  refine ⟨hG, hC, hAs, hSin, hAcc, hDom, hCC, hNC, hRep, ⟨a, hAs, Iff.rfl⟩, ?_⟩
  exact assertionTruthRouteA σ semantics false selective domain _ hSin hAcc hDom hRep

end TruthCore.Results.Causality.DivineVeracityAssembly1732
