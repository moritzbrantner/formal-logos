import Duper
import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Causality.GodMaximalCausal
import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
import TruthCore.Greek.Aristotle.Metaphysics
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaAscent
import TruthCore.Latin.Aquinas.InMetaphysicam.BookII
import TruthCore.Logic.ExcludedMiddle
/-! Identification oracle of the #1832 pilot (docs/discover.md, "Agent-guided
blueprint recipe"; attempts e63628f1 and e8bf6def). A manual check, not built
by `lake build` or CI:

    lake env lean scripts/testdata/discover-blueprint/IdentificationOracle.lean

Each example states a target over one carrier pair and one set of relations,
so the premises' binders are identified explicitly (B := Being, R := Respect,
Entity := Being, Has := InAct, truth := verum, being := esse). These are the
identifications the verified arguments 8542e377, 4d1efe91 and c201b61a
already make by instantiation; no sense tag records them, and they stay OPEN
as tags. Granting them, Duper (or a short hand proof) closes each target in
seconds: rediscovery fails on retrieval plus missing tags, not on proof
search. Checked at 495c8f19f. -/
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.GodMaximalCausal
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Logic

set_option maxHeartbeats 400000

-- 101bdd62 from 5a948c37 (needs Entity:=Being, Has:=InAct, truth:=verum, being:=esse)
example {Being Respect : Type} (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (verum esse : Respect) (h : AsToBeingSoToTruthReading InAct MoreIn verum esse) :
    MostTrueIsMostBeingReading InAct MoreIn verum esse := by
  unfold AsToBeingSoToTruthReading at h; unfold MostTrueIsMostBeingReading IsMaximumIn; duper [*]

-- 4c79298d from known bundle 4d1efe91 (needs B:=Being, R:=Respect)
example {Being Respect : Type} (IsGod : Being → Prop) (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (h1 : GodCausesBeingOfAllOthers IsGod CausesIn esse) (h2 : CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
    (h3 : MoreSuchHasThePerfectionReading InAct MoreIn) (h4 : MoreInIsAsymmetric MoreIn)
    (h5 : SomethingOtherThanGodExists IsGod) :
    GodIsMaximalInBeing IsGod InAct MoreIn esse := by
  unfold GodCausesBeingOfAllOthers at h1; unfold CauseOfBeingIsMoreInBeing at h2
  unfold MoreSuchHasThePerfectionReading at h3; unfold MoreInIsAsymmetric at h4
  unfold SomethingOtherThanGodExists at h5; unfold GodIsMaximalInBeing IsMaximumIn; duper [*]

-- 6c27657f from known bundle c201b61a (needs B:=Being, R:=Respect)
example {Being Respect : Type} (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (CausesIn : Being → Being → Respect → Prop)
    (h1 : MoreSuchHasThePerfectionReading InAct MoreIn) (h2 : DistinctCauseHasWhatItGives CausesIn InAct)
    (h3 : ExceededPerfectionIsCausedReading InAct MoreIn CausesIn)
    (h4 : NoInfiniteRegressOfCausesOfAPerfectionReading CausesIn) :
    GradesByApproachToAMaximumReading InAct MoreIn := by
  intro r ⟨x, y, hxy⟩
  have hx := h1 r x y hxy
  -- well-founded induction on distinct causes of r
  by_contra hno
  have key : ∀ z, InAct z r → False := by
    intro z
    induction z using (h4 r).induction with
    | _ z ih =>
      intro hz
      apply hno
      refine ?_
      by_contra hnm
      apply hnm
      refine ⟨z, hz, fun w hw => ?_⟩
      obtain ⟨c, hcz, hc⟩ := h3 r z w hz hw
      exact ih c ⟨hcz, hc⟩ (h2 c z r hcz hc) |>.elim
  exact key x hx
