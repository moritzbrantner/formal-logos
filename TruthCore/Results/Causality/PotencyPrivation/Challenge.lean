import TruthCore.Causality.Round3CogitoBase
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency

namespace TruthCore.Results.Causality.PotencyPrivation

open TruthCore.Causality.Round3CogitoBase
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem capacityUnderPrivation {Being Respect : Type}
    (InAct InPotency CanBe Deprived : Being → Respect → Prop)
    (hAnalysis : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe)
    (hLack : PrivationIsLackOfActInCapable InAct CanBe Deprived) :
    PotencyIsCapacityUnderPrivation InPotency CanBe Deprived := by
  sorry

theorem lackInCapable {Being Respect : Type}
    (InAct InPotency CanBe Deprived : Being → Respect → Prop)
    (hAnalysis : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe)
    (hPrivation : PotencyIsCapacityUnderPrivation InPotency CanBe Deprived) :
    PrivationIsLackOfActInCapable InAct CanBe Deprived := by
  sorry

theorem adoptedEquivalence {Being Respect : Type}
    (InAct CanBe Deprived : Being → Respect → Prop) :
    PotencyIsCapacityUnderPrivation (AdoptedPotency.InPotency InAct CanBe) CanBe Deprived ↔
      PrivationIsLackOfActInCapable InAct CanBe Deprived := by
  sorry

end TruthCore.Results.Causality.PotencyPrivation
