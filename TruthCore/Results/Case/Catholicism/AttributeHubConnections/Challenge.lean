import TruthCore.Case.Catholicism.AttributesFromEsse
import TruthCore.Case.Catholicism.StagesOneTwo
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect.Solution

namespace TruthCore.Results.Case.Catholicism.AttributeHubConnections

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.AttributesFromEsse (PerfectInFrame)
open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Uniqueness transports the supplied attribute field from the witness to any
being with the same God predicate, on the unchanged signature. -/
theorem attributesOfUniqueGod (σ : Signature)
    (hUnique : UniqueClassicalGodExists σ) : GodHasClassicalAttributes σ := by
  sorry

/-- Use the independently derived unity, perfection and goodness at each God
candidate. Derive the other six attributes using the existing stage-two proofs
and the potency-free first-being proposition for this frame. -/
theorem attributesFromSeparateProofs (σ : Signature) {W T Respect Principle : Type}
    (F : GradesFrame W σ.Being T Respect)
    (InPotency GoodIn : σ.Being → Respect → Prop)
    (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect F.InAct)
      (IsSupremelyGood F.InAct GoodIn F.CausesIn F.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod F.InAct F.MoreIn F.esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hUniting : CompositeHasAUnitingCauseReading Composite F.CausesIn F.esse)
    (hFirstBeing : MaximumInBeingIsFirstBeing F.InAct F.MoreIn F.esse F.PriorSimply)
    (hNoPotency : FirstBeingIsInNoWayInPotencyReading InPotency F.PriorSimply)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf F.PriorSimply)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hImmaterial : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill)
    (hOne : GodIsOne σ.IsGod)
    (hPerfect : PerfectInFrame F σ.IsGod)
    (hGood : GodIsSupremelyGood σ.IsGod F.InAct GoodIn F.CausesIn F.esse) :
    GodHasClassicalAttributes σ := by
  sorry

end TruthCore.Results.Case.Catholicism.AttributeHubConnections
