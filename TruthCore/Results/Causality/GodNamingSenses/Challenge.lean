import TruthCore.Causality.GodNamingSenses
import TruthCore.Results.Modal.RigidDesignation.Solution

namespace TruthCore.Results.Causality.GodNamingSenses

open TruthCore.Causality.GodNamingSenses
open TruthCore.Causality.GodNamingSenses.Control
open TruthCore.Modal.RigidDesignation (Name RigidAt CoRef)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt)
open TruthCore.Isabelle.AFP.GoedelGod (Box)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessarySenseFork (RootFacts NecessaryRootBoxK necessaryAt_iff_boxExistsAt)
open TruthCore.Case.Catholicism (Signature IsTheOneGod)

/-- Rigid-name reading gives the route's box K node. -/
theorem rigidToBoxK {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (h : NecessaryRootRigidName σ m w) (CN : σ.Being → σ.Being → Prop) :
    NecessaryRootBoxK σ m w CN := by
  sorry

/-- Descriptive reading plus the no-other-possible-God bridge gives the box K
node: at each accessible world the existing unique God-satisfier is actually
GOD_4, hence the one GOD_4, the root. -/
theorem descToBoxK {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (GodAt : Description W σ.Being)
    (hDesc : NecessaryRootDescriptiveName σ m w GodAt)
    (hNoOther : NoOtherPossibleGod σ m w GodAt)
    (CN : σ.Being → σ.Being → Prop) :
    NecessaryRootBoxK σ m w CN := by
  sorry

/-- The box K node plus essential Godhood and the no-other-possible-God bridge
gives the descriptive reading. -/
theorem boxKToDesc {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (GodAt : Description W σ.Being) (CN : σ.Being → σ.Being → Prop)
    (hBoxK : NecessaryRootBoxK σ m w CN)
    (hEss : GodhoodEssentialToGod σ m w GodAt)
    (hNoOther : NoOtherPossibleGod σ m w GodAt) :
    NecessaryRootDescriptiveName σ m w GodAt := by
  sorry

theorem checks : Control.Checks := by
  sorry

end TruthCore.Results.Causality.GodNamingSenses
