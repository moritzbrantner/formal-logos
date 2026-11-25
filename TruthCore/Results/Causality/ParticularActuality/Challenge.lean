import TruthCore.Causality.ParticularActuality
import TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution

namespace TruthCore.Results.Causality.ParticularActuality

open TruthCore.Causality.ParticularActuality
open TruthCore.Causality.JointGroups (Groups)
open TruthCore.Causality.DerivativeJointPower (Supply)
open TruthCore.Causality.Round2PerfectionPrimacy (PerfectionsAreModesOfBeing)
open TruthCore.Case.Catholicism

theorem inheritance {B R E G : Type} (h : Groups E G) (I : E → Prop)
    (event : B → R → E) (esse : R) (selected InAct mode : B → R → Prop)
    (hModes : PerfectionsAreModesOfBeing InAct mode)
    (hBearer : ModeUsesBearer h I event esse selected mode) :
    InheritsEsseCuts h I event esse selected InAct := by
  sorry

theorem mediatedInheritance {B R E G : Type} (h : Groups E G) (I : E → Prop)
    (event : B → R → E) (esse : R) (selected InAct mode : B → R → Prop)
    (hModes : PerfectionsAreModesOfBeing InAct mode)
    (hMediated : ModeThroughBearer h I event esse selected mode) :
    InheritsEsseCuts h I event esse selected InAct := by
  sorry

theorem singleDeletion : SingleDeletionTest := by
  sorry

open Control

theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.ParticularActuality
