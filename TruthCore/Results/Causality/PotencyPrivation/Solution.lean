module

public import TruthCore.Causality.Round3CogitoBase
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency

@[expose] public section

namespace TruthCore.Results.Causality.PotencyPrivation

open TruthCore.Causality.Round3CogitoBase
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem capacityUnderPrivation {Being Respect : Type}
    (InAct InPotency CanBe Deprived : Being → Respect → Prop)
    (hAnalysis : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe)
    (hLack : PrivationIsLackOfActInCapable InAct CanBe Deprived) :
    PotencyIsCapacityUnderPrivation InPotency CanBe Deprived := by
  intro x r
  constructor
  · intro hp
    obtain ⟨hc, hn⟩ := (hAnalysis x r).mp hp
    exact ⟨hc, (hLack x r hc).mpr hn⟩
  · rintro ⟨hc, hd⟩
    exact (hAnalysis x r).mpr ⟨hc, (hLack x r hc).mp hd⟩

theorem lackInCapable {Being Respect : Type}
    (InAct InPotency CanBe Deprived : Being → Respect → Prop)
    (hAnalysis : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe)
    (hPrivation : PotencyIsCapacityUnderPrivation InPotency CanBe Deprived) :
    PrivationIsLackOfActInCapable InAct CanBe Deprived := by
  intro x r hc
  constructor
  · intro hd
    exact ((hAnalysis x r).mp ((hPrivation x r).mpr ⟨hc, hd⟩)).2
  · intro hn
    exact ((hPrivation x r).mp ((hAnalysis x r).mpr ⟨hc, hn⟩)).2

theorem adoptedEquivalence {Being Respect : Type}
    (InAct CanBe Deprived : Being → Respect → Prop) :
    PotencyIsCapacityUnderPrivation (AdoptedPotency.InPotency InAct CanBe) CanBe Deprived ↔
      PrivationIsLackOfActInCapable InAct CanBe Deprived := by
  let potency := AdoptedPotency.InPotency InAct CanBe
  have hAnalysis := AdoptedPotency.analysis InAct CanBe
  exact ⟨lackInCapable InAct potency CanBe Deprived hAnalysis,
    capacityUnderPrivation InAct potency CanBe Deprived hAnalysis⟩

end TruthCore.Results.Causality.PotencyPrivation
