module

public import TruthCore.Causality.MutualSupportAsymmetry

@[expose] public section

namespace TruthCore.Results.Causality.MutualSupportAsymmetry

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.GradedSupportFoundation
  (NecessarySupportAscendsInEsse NoInfiniteAscentAmongNecessaryConcreta)
open TruthCore.Causality.MutualSupportAsymmetry
open TruthCore.Causality.NecessarySupportCoverage (NoNecessaryConcretaMutualSupport)

theorem noMutualSupport {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hAscend : NecessarySupportAscendsInEsse m w MoreIn esse)
    (hAsymm : NecessaryGradeAsymmetric m w MoreIn esse) :
    NoNecessaryConcretaMutualSupport m w := by
  rintro ⟨a, b, v, u, ha, hb, hna, hnb, hav, hab, hbu, hba⟩
  exact hAsymm a b ha hb hna hnb (hAscend v a b ha hb hna hnb hav hab)
    (hAscend u b a hb ha hnb hna hbu hba)

theorem asymmetricOfWellFounded {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hWF : NoInfiniteAscentAmongNecessaryConcreta m w MoreIn esse) :
    NecessaryGradeAsymmetric m w MoreIn esse := by
  intro a b ha hb hna hnb hab hba
  exact @WellFounded.asymmetric B _ hWF a b
    ⟨ha, hb, hna, hnb, hab⟩ ⟨hb, ha, hnb, hna, hba⟩

theorem asymmetricGradeWithoutFoundation : AsymmetryWithoutFoundation := by
  let m : Profile Unit Nat := {
    ontic := ⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩
    concrete := fun _ => True
    grounds := fun _ _ _ => False }
  let grade : Unit → Nat → Nat → Prop := fun _ a b => b < a
  refine ⟨m, grade, fun _ _ _ _ _ _ hab => Nat.lt_asymm hab, ?_⟩
  intro hWF
  have impossible (n : Nat) (h : Acc (fun a b =>
      m.concrete a ∧ m.concrete b ∧
      TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic () a ∧
      TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic () b ∧ grade () a b) n) : False := by
    induction h with
    | intro n _ ih =>
      exact ih (n + 1) ⟨trivial, trivial, fun _ _ => trivial,
        fun _ _ => trivial, Nat.lt_succ_self n⟩
  exact impossible 0 (hWF.apply 0)

end TruthCore.Results.Causality.MutualSupportAsymmetry
