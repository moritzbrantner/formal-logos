module

public import TruthCore.Causality.CogitoCapacityInterface
public import TruthCore.Results.Causality.CapacityInterface.Solution
public import TruthCore.Results.Causality.Round4Revisited.Solution

@[expose] public section

namespace TruthCore.Results.Causality.CogitoCapacityInterface

open TruthCore.Causality.CapacityInterface
open TruthCore.Causality.CogitoCapacityInterface
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoEsse
open TruthCore.Logic.CogitoConcrete
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect (OperationAttribution)

/-- Real consumer adoption at a specified intellectual effect. The six original
premise formulas and the exact original conclusion remain unchanged. -/
theorem inhabitedFromSelectedCapacity {W B Episode R : Type} (m : Ontic W B)
    (concrete : B → Prop) (w : W) (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (a : OperationAttribution B Episode) (p : Capacity W B R) (intellectualEffect : R)
    (hO : ThoughtOccurs Occurs)
    (hB : EveryThoughtHasSubject Occurs Bears)
    (hEx : BorneThoughtExercisesIntellect Occurs Bears a)
    (hPow : IntellectualExerciserHasPowerAt a (bearerProfile p intellectualEffect) w)
    (hE : EveryBearerExistsAt m Occurs Bears w)
    (hPowConcrete : PowerRequiresConcreteAt concrete (bearerProfile p intellectualEffect) w) :
    InhabitedConcreteAt m concrete w := by
  exact TruthCore.Results.Causality.Round4Revisited.inhabitedFromPower m concrete w
    Occurs Bears a (bearerProfile p intellectualEffect) hO hB hEx hPow hE hPowConcrete

theorem formula_transport : FormulaTransport := by
  intro W B Episode R a concrete power p intellectualEffect w h
  constructor
  · constructor
    · intro hp b e he
      exact (h b).mp (hp b e he)
    · intro hp b e he
      exact (h b).mpr (hp b e he)
  · constructor
    · intro hc b hb
      exact hc b ((h b).mpr hb)
    · intro hc b hb
      exact hc b ((h b).mp hb)

/-- The generic certificate is reused for the thin embedding's exact round trip;
the consumer above additionally accepts genuinely respect-indexed profiles. -/
theorem thinRecovery (W B : Type) (power : W → B → Prop) :
    bearerProfile (fromBearer power) () = power := by
  exact TruthCore.Results.Causality.CapacityInterface.certificate.2.1.2 W B power

theorem certificate : TruthCore.Causality.CogitoCapacityInterface.Certificate := by
  refine ⟨formula_transport, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩,
        fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
    · intro b h
      cases h
    · intro h
      have bad : true = false := h () () trivial
      cases bad
    · rintro ⟨b, h, _⟩
      exact h
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩,
        fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
    · intro _ _ _
      trivial
    · intro b h
      cases h
    · intro h
      have bad : true = false := (h ()).mp trivial
      cases bad
    · rintro ⟨b, h, _⟩
      exact h

end TruthCore.Results.Causality.CogitoCapacityInterface
