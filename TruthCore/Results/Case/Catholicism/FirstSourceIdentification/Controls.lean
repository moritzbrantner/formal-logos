module

public import TruthCore.Results.Case.Catholicism.FirstSourceIdentification.Solution
public import TruthCore.Case.Catholicism.ClassicalAttributesJointWitness

/-! Finite controls for co-reference under the shared-maximum criterion. -/

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.FirstSourceIdentification.Controls

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.FirstSourceIdentification
open TruthCore.Case.Catholicism.ClassicalAttributesJointWitness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.TermSenseForks

private theorem maximum (x : Being) :
    IsMaximumIn InAct MoreIn esse x ↔ x = false := by
  cases x with
  | false =>
    exact ⟨fun _ => rfl, fun _ => ⟨Or.inl rfl, fun _ h => Bool.noConfusion h.2⟩⟩
  | true =>
    exact ⟨fun h => (h.2 false ⟨rfl, rfl⟩).elim, fun h => Bool.noConfusion h⟩

private theorem atMostOne : AtMostOneMaximeEns InAct MoreIn esse :=
  fun x y hx hy => ((maximum x).mp hx).trans ((maximum y).mp hy).symm

def callsMaximum (_ : Unit) (x : Bool) : Prop := x = false

def callsBoth (_ : Unit) (_ : Bool) : Prop := True

def unnamed : Signature := { σ with IsGod := fun _ => False }

/-- The stage-one extensions have a witness and only include the unique
maximum. Without an inhabited classical extension, both inclusions fail. -/
theorem noClassicalReferent :
    SummaGodIsMaximum (callsMaximum ()) InAct MoreIn esse ∧
    CalledGodIsMaximum callsMaximum () InAct MoreIn esse ∧
    AtMostOneMaximeEns InAct MoreIn esse ∧
    GodIsMaximalInBeing unnamed.IsGod InAct MoreIn esse ∧
    ¬ GodExists unnamed.IsGod ∧
    ¬ SummaGodIsClassicalGod unnamed (callsMaximum ()) ∧
    ¬ CalledGodIsClassicalGod unnamed callsMaximum () :=
  ⟨fun x hx => (maximum x).mpr hx, fun x hx => (maximum x).mpr hx, atMostOne,
    fun _ hx => hx.elim, fun ⟨_, hx⟩ => hx, fun h => h false rfl, fun h => h false rfl⟩

/-- An actual maximum is GOD_4 and satisfies the full nominal description.
Calling both individuals by the same name preserves the forward usage
premise but spoils reference agreement. -/
theorem overinclusiveUsage :
    NominalGod InAct MoreIn CausesIn esse ComponentOf false ∧
    DescribedPrincipleIsCalledGod InAct MoreIn CausesIn esse ComponentOf callsBoth () ∧
    AtMostOneMaximeEns InAct MoreIn esse ∧
    GodExists σ.IsGod ∧ GodIsMaximalInBeing σ.IsGod InAct MoreIn esse ∧
    CalledGod callsBoth () true ∧ ¬ CalledGodIsClassicalGod σ callsBoth () := by
  refine ⟨⟨(maximum false).mpr rfl, ?_, ?_, ?_, fun x => (maximum x).mp⟩,
    fun _ _ _ _ _ _ => trivial, atMostOne, ⟨false, rfl⟩,
    fun x hx => (maximum x).mpr hx, trivial, fun h => Bool.noConfusion (h true trivial)⟩
  · intro x hx _
    cases x
    · exact (hx rfl).elim
    · exact ⟨rfl, rfl⟩
  · intro x r hx _
    cases x
    · exact (hx rfl).elim
    · exact ⟨rfl, rfl⟩
  · intro x hx
    exact Bool.noConfusion hx.1

/-- Co-reference with both name extensions populated, on the same
two-individual roster as the omission tests. -/
theorem commonReferent :
    callsMaximum () false ∧ CalledGod callsMaximum () false ∧ σ.IsGod false ∧
    SummaGodIsClassicalGod σ (callsMaximum ()) ∧ CalledGodIsClassicalGod σ callsMaximum () :=
  ⟨rfl, rfl, rfl,
    summaFromCommonMaximum σ (callsMaximum ()) InAct MoreIn esse
      (fun x hx => (maximum x).mpr hx) (fun x hx => (maximum x).mpr hx) atMostOne ⟨false, rfl⟩,
    usageFromCommonMaximum σ callsMaximum () InAct MoreIn esse
      (fun x hx => (maximum x).mpr hx) (fun x hx => (maximum x).mpr hx) atMostOne ⟨false, rfl⟩⟩

end TruthCore.Results.Case.Catholicism.FirstSourceIdentification.Controls
