import TruthCore.Causality.NarDerivation

/-! Deriving NAR (#1944's premise `43651417`: every NECESSARY_2 actual concretum
is an actual root) from the root's withholding of each grounded being and an
explicit grounding-to-giving bridge (N1), and that withholding from either a
uniform mode of giving at the root (N2) or the will route of ST I q.19 a.3:
willed giving, a rational power fixed only toward what its end requires, and
a self-sufficient root (N3). Analyst reconstructions; attribution deferred. -/

namespace TruthCore.Results.Causality.NarDerivation
open TruthCore.Causality.NarDerivation
open TruthCore.Causality.NarDerivation.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.HolderRootIdentification (NecessaryActualConcretaAreRoots
  ActualAbsenceHoldersExistAt ActualAbsenceHoldersAreActualRoots)
open TruthCore.Causality.HolderRootIdentification.Model (gdEx gGroundsOthers gdWithholdG dPower)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)
open TruthCore.Causality.WillVersusChance (AgencyFrame OnePower SetupInvariantAt WilledTwoWayAt
  OnePowerIntellectualGivingWilled)
open TruthCore.Causality.WillVersusChance.Model (onlyG nobody simpleRational twoPowerChancer)
open TruthCore.Modal.ModalGrounding (SomeContingentConcreteAt ActualAbsenceInitiatorPresent
  ActualAbsencePowerHoldersConcrete NoActualContingentConcreteIn)
open TruthCore.Modal.PrussPowerPremises (GivesTo TwoWayGiverAt GivenExists
  ActualAbsenceHoldersGiveEach)
open TruthCore.Modal.PrussPowerPremises.Model (Bg Bg.forall_iff Bg.exists_iff gFrame theistG
  allC uni gcEx gcAlways givesCHere)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)

/-- Argument N1: NAR from (a), (b2) and the common root of `0c27f65a` (only its
root and reach clauses are used; `nar_of_commonRoot` is the same argument from
the bare common root). Let `x` be a NECESSARY_2 actual concretum with an actual
concrete ground. The common root `n` is `x` (impossible: `n` is a root) or
grounds `x`. Then (a) gives an accessible world `v` where `n` exists and does
not give `x` being; `x` is necessary, so (b2) makes `n` give it being there.
Constructive. -/
theorem narFromRootWithholding {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop) (w : W)
    (hIG : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (hB : ActualRootsGiveNecessaryGroundedWherever F concrete G w)
    (hA : ActualRootsWithholdEachGrounded F concrete G w) :
    NecessaryActualConcretaAreRoots (groundProfile F concrete G) w := by
  sorry

/-- Argument N2: (a) from uniformity at the root (with the root and reach clauses
of `0c27f65a` as the common root). By law 2 the root is two-way
toward a contingent being; uniformity makes it two-way toward every being it
gives at `w`, and by (b1) it gives each actual concretum it grounds. -/
theorem rootWithholdingFromUniformity {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop) (w : W)
    (hB : ActualRootsGiveGroundedHere F concrete G w) (hGE : GivenExists F)
    (hIG : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (hNec : ActualRootsNecessary F concrete G w) (hSome : SomeContingentConcreteAt F concrete w)
    (hU : ActualRootsGiveUniformly F concrete G w) :
    ActualRootsWithholdEachGrounded F concrete G w := by
  sorry

/-- Argument N3: (a) from the will route. The common GOD_4 root with intellect
(`0c27f65a`) is every actual root; with one power its giving is the exercise of
a rational power (#1941 `5c1aba17`). A root that never withheld a being it
grounds would, by (b1), give it being at `w` and be fixed toward it; WN then
makes that being required by the root's end, against SS. Excluded middle. -/
theorem rootWithholdingFromWill {W B T R S P : Type} (F : CausalityFrame W B T R)
    (A : AgencyFrame W B S P) (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop)
    (EndRequires : B → B → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hIG : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (hWill : OnePowerIntellectualGivingWilled F A HasIntellect)
    (hOne : ActualRootsOnePower F A concrete G w)
    (hB : ActualRootsGiveGroundedHere F concrete G w)
    (hWN : RationalFixedGivingIsRequired F A EndRequires w)
    (hSS : ActualRootsEndRequiresNoOther F concrete G EndRequires w) :
    ActualRootsWithholdEachGrounded F concrete G w := by
  sorry

macro "nd_unfold" : tactic => `(tactic|
  simp only [TruthCore.Logic.ExcludedMiddle, ActualCommonRootAt,
    ActualRootsGiveGroundedHere, ActualRootsGiveNecessaryGroundedWherever,
    ActualRootsWithholdEachGrounded, StrictModalRequirement,
    ActualRootsNecessary, ActualRootsGiveUniformly, ActualRootsOnePower,
    RationalFixedGivingIsRequired, ActualRootsEndRequiresNoOther, UniformGivingModeAt,
    FixedTowardAt, TwoWayTowardAt, NecessaryActualConcretaAreRoots,
    ActualAbsenceHoldersExistAt, ActualAbsenceHoldersAreActualRoots,
    ActualAbsenceInitiatorPresent, TruthCore.Modal.ModalGrounding.InitiatorPresentFor,
    ActualAbsencePowerHoldersConcrete, TruthCore.Modal.ModalGrounding.PowerHoldersConcreteFor,
    ActualAbsenceHoldersGiveEach, SomeContingentConcreteAt, NoActualContingentConcreteIn,
    IntellectualGodCommonRootAt, OnePowerIntellectualGivingWilled, OnePower,
    SetupInvariantAt, TruthCore.Causality.WillVersusChance.SetupSameIn, WilledTwoWayAt,
    TruthCore.Causality.WillVersusChance.GivesBy, AgencyFrame.reclassify,
    ActualRoot, ActualConcrete, ActualConcreteGround, groundProfile, NecessaryAt, ContingentAt,
    GivesTo, GivenExists, simpleRational, twoPowerChancer, rationalGD, naturalGD, onlyG, nobody,
    noRequirement, gRequiresD, mixedGives, mixedG, mutualGD, mutualG, gGivesD, fixedDG,
    gGivesOthers, nonFactiveMixedG, onlyFalseEx, gGivesOthersHere, contingentRootG, noCEx,
    noContingentG, chainGrounds, chainGives, chainG, toTrue, givesCThere, toTrueG,
    gdEx, gGroundsOthers, gdWithholdG, TruthCore.Causality.HolderRootIdentification.Model.dGivesCHere,
    dPower, theistG, gFrame, allC, uni, gcEx, gcAlways, givesCHere])

macro "nd_close" : tactic => `(tactic|
  first
  | exact fun p => Classical.em p
  | (nd_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]))

/-- Argument N4, the certificate of laws and models. Premise-free. -/
theorem narDerivationControls : Controls := by
  sorry

end TruthCore.Results.Causality.NarDerivation
