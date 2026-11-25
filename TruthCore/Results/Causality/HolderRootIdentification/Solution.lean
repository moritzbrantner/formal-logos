module

public import TruthCore.Causality.HolderRootIdentification

/-! Identifying the holder of the power for the actual contingents' joint
absence with the selected root (#1926 phase 3, #1897 gap 2): every holder is an
actual root, given initiator presence, concreteness, existence at the world and
the denial of necessary-through-another; a common root, or at most one root,
then makes every holder that root, carries its intellect and GOD_4 name to the
holder, and gives #1941's willed holder a consumer at GOD_4's will. Analyst
reconstructions; attribution deferred. -/

@[expose] public section

namespace TruthCore.Results.Causality.HolderRootIdentification
open TruthCore.Causality.HolderRootIdentification
open TruthCore.Causality.HolderRootIdentification.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)
open TruthCore.Causality.WillVersusChance (AgencyFrame ActualAbsenceHolderGivesByWill
  GodsHoldActualAbsencePower RationalPowerIsWill ActualAbsenceHoldersHaveIntellect WilledTwoWayAt)
open TruthCore.Causality.WillVersusChance.Model (onlyG nobody simpleRational simpleChancy)
open TruthCore.Latin.Aquinas.DeEnte (AtMostOneActualRootAt)
open TruthCore.Modal.ModalGrounding (NoActualContingentConcreteIn ActualAbsenceInitiatorPresent
  ActualAbsencePowerHoldersConcrete)
open TruthCore.Modal.PrussPowerPremises.Model (Bg Bg.forall_iff Bg.exists_iff gFrame theistG
  allC uni gcEx givesCHere noGiving gPower)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Case.Catholicism (GodHasWill)

/-- No holder is contingent at `w`: P2′ puts it at an accessible world where
every concrete being contingent at `w` is absent, and it is concrete. -/
theorem holder_not_contingent {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hConc : ActualAbsencePowerHoldersConcrete F PowerFor concrete w) (y : B)
    (hy : PowerFor w y (NoActualContingentConcreteIn F concrete w)) :
    ¬ ContingentAt F.history.ontic w y := by
  intro hCont
  obtain ⟨u, _, hq, hyu⟩ := hInit y hy
  exact hq y (hConc y hy) hCont hyu

/-- Every holder is concrete, exists at `w` and is necessary at `w`. -/
theorem holder_necessary {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hConc : ActualAbsencePowerHoldersConcrete F PowerFor concrete w)
    (hExist : ActualAbsenceHoldersExistAt F PowerFor concrete w) :
    ActualAbsenceHoldersNecessaryConcrete F PowerFor concrete w := by
  intro y hy
  refine ⟨hConc y hy, hExist y hy, fun v hv => ?_⟩
  rcases hEM (F.history.ontic.ExistsAt v y) with h | h
  · exact h
  · exact absurd ⟨hExist y hy, v, hv, h⟩
      (holder_not_contingent F PowerFor concrete w hInit hConc y hy)

/-- Argument 1, holders are actual roots. Each holder is concrete (P3′), exists
at `w` (holders at `w`), and exists at every accessible world: at a world where
it is absent it would be contingent at `w`, but P2′ puts it at a world lacking
every actual contingent concretum (excluded middle). NAR then makes the
necessary actual concretum an actual root. -/
theorem holdersAreActualRoots {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hConc : ActualAbsencePowerHoldersConcrete F PowerFor concrete w)
    (hExist : ActualAbsenceHoldersExistAt F PowerFor concrete w)
    (hNAR : NecessaryActualConcretaAreRoots (groundProfile F concrete G) w) :
    ActualAbsenceHoldersAreActualRoots F PowerFor concrete G w := by
  intro y hy
  obtain ⟨hc, he, hn⟩ := holder_necessary F PowerFor concrete w hEM hInit hConc hExist y hy
  exact hNAR y ⟨hc, he⟩ hn

/-- A root of `m` at `w` is the common root `n`: the reach clause gives
`y = n` or an actual concrete ground from `n`, which a root lacks. -/
theorem root_eq_commonRoot {W B : Type} (m : Profile W B) (w : W) (n y : B)
    (hReach : ∀ x, ActualConcrete m w x → x = n ∨ ActualConcreteGround m w n x)
    (hy : ActualRoot m w y) : y = n := by
  rcases hReach y hy.1 with h | h
  · exact h
  · exact absurd h (hy.2 n)

/-- Argument 2, holders have intellect, from the common GOD_4 root with
intellect (`0c27f65a`). A holder is an actual root (argument 1's conclusion);
the common root `n` directly grounds every other actual concretum, so the
holder, having no ground, is `n`, and `n` has intellect. Constructive. -/
theorem holdersHaveIntellectFromCommonRoot {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (G : W → B → B → Prop)
    (IsGod HasIntellect : B → Prop) (w : W)
    (hRoots : ActualAbsenceHoldersAreActualRoots F PowerFor concrete G w)
    (hCommon : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect) :
    ActualAbsenceHoldersHaveIntellect F PowerFor concrete HasIntellect w := by
  intro y hy
  obtain ⟨n, _, hReach, _, hInt⟩ := hCommon
  rw [root_eq_commonRoot _ w n y hReach (hRoots y hy)]
  exact hInt

/-- Argument 3, holders are GOD_4, from the same two premises: the holder is the
common root, which is GOD_4. Constructive. -/
theorem holdersAreGodFromCommonRoot {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (G : W → B → B → Prop)
    (IsGod HasIntellect : B → Prop) (w : W)
    (hRoots : ActualAbsenceHoldersAreActualRoots F PowerFor concrete G w)
    (hCommon : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect) :
    ActualAbsenceHoldersAreGod F PowerFor concrete IsGod w := by
  intro y hy
  obtain ⟨n, _, hReach, hGod, _⟩ := hCommon
  rw [root_eq_commonRoot _ w n y hReach (hRoots y hy)]
  exact hGod

/-- Argument 4, at most one holder, from at most one actual root (`49fdec01`):
two holders are two actual roots of the same relation at the same world.
Constructive. -/
theorem atMostOneHolderFromAtMostOneRoot {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hRoots : ActualAbsenceHoldersAreActualRoots F PowerFor concrete G w)
    (hOne : AtMostOneActualRootAt (groundProfile F concrete G) w) :
    AtMostOneActualAbsenceHolder F PowerFor concrete w :=
  fun y z hy hz => hOne y z (hRoots y hy) (hRoots z hz)

/-- Argument 5, GOD_4 has will, from #1941's willed holder. A GOD_4 `g` holds
the power (`0050b6ed`); the willed holder `y` gives by a rational power, so it
has will (rational power is will, `65e0179f`); there is at most one holder, so
`g = y`. Constructive. -/
theorem godHasWillFromWilledHolder {W B T R S P : Type} (F : CausalityFrame W B T R)
    (A : AgencyFrame W B S P) (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop)
    (IsGod HasWill : B → Prop) (w : W)
    (hWilled : ActualAbsenceHolderGivesByWill F A PowerFor concrete w)
    (hGod : GodsHoldActualAbsencePower F PowerFor concrete IsGod w)
    (hOne : AtMostOneActualAbsenceHolder F PowerFor concrete w)
    (hRat : RationalPowerIsWill A HasWill) :
    GodHasWill IsGod HasWill := by
  intro g hg
  obtain ⟨y, hy, _, p, _, _, hp, hr, _⟩ := hWilled
  rw [hOne g y (hGod g hg).2 hy]
  exact hRat y p hp hr

theorem laws : Laws := by
  refine ⟨?_, ?_, ?_⟩
  · intro W B T R F PowerFor concrete w hInit hConc hExist
    exact ⟨holder_not_contingent F PowerFor concrete w hInit hConc,
      fun hEM => holder_necessary F PowerFor concrete w hEM hInit hConc hExist⟩
  · intro W B T R F PowerFor concrete G w hEM hInit hConc hExist hCommon
    obtain ⟨n, hn, hReach⟩ := hCommon
    refine ⟨n, hn, fun y hy => ?_⟩
    obtain ⟨hc, he, hnec⟩ := holder_necessary F PowerFor concrete w hEM hInit hConc hExist y hy
    rcases hReach y ⟨hc, he⟩ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hnec⟩
  · intro W B T R F PowerFor concrete G w hEM hInit hConc hExist hNAR hCommon
    obtain ⟨n, _, hReach⟩ := hCommon
    exact ⟨n, fun y hy => root_eq_commonRoot _ w n y hReach
      (holdersAreActualRoots F PowerFor concrete G w hEM hInit hConc hExist hNAR y hy)⟩

macro "hr_unfold" : tactic => `(tactic|
  simp only [TruthCore.Logic.ExcludedMiddle, ActualAbsenceInitiatorPresent,
    TruthCore.Modal.ModalGrounding.InitiatorPresentFor, ActualAbsencePowerHoldersConcrete,
    TruthCore.Modal.ModalGrounding.PowerHoldersConcreteFor, ActualAbsenceHoldersExistAt,
    NecessaryActualConcretaAreRoots, ActualAbsenceHoldersAreActualRoots,
    AtMostOneActualAbsenceHolder, ActualAbsenceHoldersAreGod, ActualAbsenceHoldersHaveIntellect,
    IntellectualGodCommonRootAt, AtMostOneActualRootAt, ActualRoot, ActualConcrete,
    ActualConcreteGround, groundProfile, NecessaryAt, ContingentAt, NoActualContingentConcreteIn,
    ActualAbsenceHolderGivesByWill, GodsHoldActualAbsencePower, RationalPowerIsWill, GodHasWill,
    WilledTwoWayAt, TruthCore.Causality.WillVersusChance.SetupSameIn,
    TruthCore.Causality.WillVersusChance.GivesBy, TruthCore.Modal.PrussPowerPremises.GivesTo,
    TruthCore.Modal.PrussPowerPremises.TwoWayGiverAt, TruthCore.Modal.PrussPowerPremises.GivenExists,
    TruthCore.Modal.PrussPowerPremises.ActualAbsenceHoldersGiveEach,
    AgencyFrame.reclassify, simpleRational, simpleChancy, dRational, onlyG, nobody, onlyD, onlyC,
    notD, gdEx, dThereEx, dGivesCHere, gdG, gdWithholdG, dThereG, gGroundsOthers, bothGroundC,
    dPower, cPower, gdPower, theistG, gFrame, allC, uni, gcEx, givesCHere, noGiving, gPower])

macro "hr_close" : tactic => `(tactic|
  first
  | exact fun p => Classical.em p
  | (hr_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]))

theorem theistNonvacuity : TheistNonvacuity := by
  unfold TheistNonvacuity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> hr_close

theorem necessaryThroughAnother : NecessaryThroughAnother := by
  unfold NecessaryThroughAnother
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> hr_close

theorem omissionsHolderRoot : OmissionsHolderRoot := by
  unfold OmissionsHolderRoot
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> hr_close

theorem twoRoots : TwoRoots := by
  unfold TwoRoots
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> hr_close

theorem rootBesideDerivedHolder : RootBesideDerivedHolder := by
  unfold RootBesideDerivedHolder
  refine ⟨?_, ?_, ?_⟩ <;> hr_close

theorem omissionsGodWill : OmissionsGodWill := by
  unfold OmissionsGodWill
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    hr_close

/-- Argument 6, the certificate of laws and models. Premise-free. -/
theorem holderRootIdentificationControls : Controls :=
  ⟨laws, theistNonvacuity, necessaryThroughAnother, omissionsHolderRoot, twoRoots,
    rootBesideDerivedHolder, omissionsGodWill⟩

end TruthCore.Results.Causality.HolderRootIdentification
