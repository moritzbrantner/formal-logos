import TruthCore.Causality.NarGrafts
import TruthCore.Causality.NecessaryRootUniqueness

/-! Two grafts onto the NAR/WN route of #1947 (#1926 orphan grafts). (G1) The
optimizing-creator rival to WN (a root that gives by total optimal output with a
unique optimum) is refuted by the premises of #1947's law 2 together with
#1737's `OptimalChoiceCertificate`: a unique optimum makes the root fixed toward
every being it gives, while law 2 makes it two-way toward a contingent one.
(G2) Necessary roots (`d164f730`) from the unique necessary actual root
(`91b085c4`). Analyst reconstructions; attribution deferred. -/

namespace TruthCore.Results.Causality.NarGrafts
open TruthCore.Causality.NarGrafts
open TruthCore.Causality.NarGrafts.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)
open TruthCore.Causality.NecessaryRootUniqueness (UniqueNecessaryActualRootAt)
open TruthCore.Causality.NarDerivation (FixedTowardAt TwoWayTowardAt
  ActualRootsGiveGroundedHere ActualRootsNecessary RationalFixedGivingIsRequired
  ActualRootsEndRequiresNoOther)
open TruthCore.Causality.WillVersusChance (AgencyFrame)
open TruthCore.Modal.ModalGrounding (SomeContingentConcreteAt)
open TruthCore.Modal.PrussPowerPremises (GivesTo GivenExists)
open TruthCore.Modal.PrussPowerPremises.Model (Bg Bg.forall_iff Bg.exists_iff gFrame allC uni)
open TruthCore.Causality.HolderRootIdentification.Model (gGroundsOthers dThereEx)
open TruthCore.Causality.WillVersusChance.Model (onlyG)
open TruthCore.Modal.SelectedEffectBridge (OutputProfile StableActOutput)
open TruthCore.Modal.OptimalCreationChoice (Optimal OptimalOutputs OptimalChoiceCertificate)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)

/-- Argument G1: the optimizing-creator rival is refuted by the premises of
#1947's law 2 (taken from #1947's certificate `b8ee1a50`) and #1737's
certificate. The common GOD_4 root of `0c27f65a` (only
its root and reach clauses are used) is an actual root; by law 2 it is two-way
toward some concrete contingent `c`: it gives `c` being at `w` and not at some
accessible `v` where it exists. A unique optimum with total optimal output makes
it fixed toward `c`, so it gives `c` being at `v`: contradiction.
Constructive. -/
theorem optimalRivalRefuted {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop) (w : W)
    (V : Type) [PartialOrder V] (feasible : Set B) (quality : B → V)
    (hB : ActualRootsGiveGroundedHere F concrete G w) (hGE : GivenExists F)
    (hIG : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (hNec : ActualRootsNecessary F concrete G w) (hSome : SomeContingentConcreteAt F concrete w)
    (hCert : OptimalChoiceCertificate)
    (hNar : TruthCore.Causality.NarDerivation.Model.Controls) :
    NotEveryActualRootGivesUniqueOptimum F concrete G w V feasible quality := by
  sorry

/-- Argument G2: necessary roots (`d164f730`) from the unique necessary actual
root (`91b085c4`): every actual root is that root, which is NECESSARY_2.
Constructive. -/
theorem necessaryRootsFromUniqueNecessaryRoot {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hU : UniqueNecessaryActualRootAt (groundProfile F concrete G) w) :
    ActualRootsNecessary F concrete G w := by
  sorry

/-- Argument G3, the certificate of laws and the tied-optimum model.
Premise-free. -/
theorem narGraftControls : Controls := by
  sorry

end TruthCore.Results.Causality.NarGrafts
