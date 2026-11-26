import TruthCore.Causality.SelectedPlgTheory
import TruthCore.Results.Modern.Fine.InfiniteDescent.Solution
import TruthCore.Results.Modern.Fine.StrictGroundAcyclic.Solution

namespace TruthCore.Results.Causality.SelectedPlgTheory

open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.SelectedPlgTheory
open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Results.Modern.Fine.InfiniteDescent
open TruthCore.Results.Modern.Fine.StrictGroundAcyclic
open Relation Sequent

theorem consistentOfNoStrictReturn {Atom : Type} (a : Atom) (S : Set (Sequent Atom))
    (noReturn : NoStrictReturn S) : Consistent S := by
  sorry

theorem consistencyCriterion : ConsistencyCriterion := by
  sorry

theorem strictDerivabilityCriterion : StrictDerivabilityCriterion := by
  sorry

theorem mapOfStrictPaths {B Atom : Type} (D : B → B → Prop) (label : B → Atom)
    (S : Set (Sequent Atom)) (paths : DependenceHasStrictPaths D label S) :
    DependenceMapsToStrictExistenceGround D label S := by
  sorry

open TruthCore.Causality.SelectedPlgTheory.Control

theorem presentationControls : PresentationControls := by
  sorry

end TruthCore.Results.Causality.SelectedPlgTheory
