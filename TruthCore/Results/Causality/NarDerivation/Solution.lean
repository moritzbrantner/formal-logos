module

public import TruthCore.Causality.NarDerivation

/-! Deriving NAR (#1944's premise `43651417`: every NECESSARY_2 actual concretum
is an actual root) from the root's withholding of each grounded being and an
explicit grounding-to-giving bridge (N1), and that withholding from either a
uniform mode of giving at the root (N2) or the will route of ST I q.19 a.3:
willed giving, a rational power fixed only toward what its end requires, and
a self-sufficient root (N3). Analyst reconstructions; attribution deferred. -/

@[expose] public section

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

/-- Every actual root of `m` is the common root `n` whose reach covers every
other actual concretum. -/
theorem root_eq_common {W B : Type} (m : Profile W B) (w : W) (n r : B)
    (hReach : ∀ x, ActualConcrete m w x → x = n ∨ ActualConcreteGround m w n x)
    (hr : ActualRoot m w r) : r = n := by
  rcases hReach r hr.1 with h | h
  · exact h
  · exact absurd h (hr.2 n)

/-- A root grounds no being identical with itself. -/
theorem ne_of_root_grounds {W B : Type} (m : Profile W B) (w : W) (n x : B)
    (hn : ActualRoot m w n) (hg : ActualConcreteGround m w n x) : x ≠ n := by
  intro h
  subst h
  exact hn.2 x hg

/-- NAR from (a), (b) and a bare common root (the core of argument N1). -/
theorem nar_of_commonRoot {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hCommon : ActualCommonRootAt (groundProfile F concrete G) w)
    (hB : ActualGroundsGiveWhereverGroundedExists F concrete G w)
    (hA : ActualRootsWithholdEachGrounded F concrete G w) :
    NecessaryActualConcretaAreRoots (groundProfile F concrete G) w := by
  intro x hx hnec
  refine ⟨hx, fun z hz => ?_⟩
  obtain ⟨n, hn, hReach⟩ := hCommon
  rcases hReach x hx with h | hgx
  · subst h
    exact hn.2 z hz
  · obtain ⟨v, hv, _, hng⟩ := hA n x hn hx hgx
    exact hng ((hB n x hgx).2 v hv (hnec v hv))

/-- The reach clause of the common GOD_4 root with intellect (`0c27f65a`) is a
common root. -/
theorem commonRoot_of_intellectual {W B : Type} (m : Profile W B) (w : W)
    (IsGod HasIntellect : B → Prop) (hIG : IntellectualGodCommonRootAt m w IsGod HasIntellect) :
    ActualCommonRootAt m w := by
  obtain ⟨n, hn, hReach, _, _⟩ := hIG
  exact ⟨n, hn, hReach⟩

/-- Argument N1: NAR from (a), (b) and the common root of `0c27f65a` (only its
root and reach clauses are used; `nar_of_commonRoot` is the same argument from
the bare common root). Let `x` be a NECESSARY_2 actual concretum with an actual
concrete ground. The common root `n` is `x` (impossible: `n` is a root) or
grounds `x`. Then (a) gives an accessible world `v` where `n` exists and does
not give `x` being; `x` exists at `v` (it is necessary), so (b) makes `n` give it
being there. Constructive. -/
theorem narFromRootWithholding {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop) (w : W)
    (hIG : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (hB : ActualGroundsGiveWhereverGroundedExists F concrete G w)
    (hA : ActualRootsWithholdEachGrounded F concrete G w) :
    NecessaryActualConcretaAreRoots (groundProfile F concrete G) w :=
  nar_of_commonRoot F concrete G w (commonRoot_of_intellectual _ w IsGod HasIntellect hIG) hB hA

/-- Law 2: under (b), factive giving, a common root, necessary roots and some
concrete contingent being, every actual root is two-way toward some concrete
contingent being. -/
theorem root_twoWay_toward_contingent {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hB : ActualGroundsGiveWhereverGroundedExists F concrete G w) (hGE : GivenExists F)
    (hCommon : ActualCommonRootAt (groundProfile F concrete G) w)
    (hNec : ActualRootsNecessary F concrete G w) (hSome : SomeContingentConcreteAt F concrete w)
    (n : B) (hn : ActualRoot (groundProfile F concrete G) w n) :
    ∃ c, concrete c ∧ ContingentAt F.history.ontic w c ∧ TwoWayTowardAt F w n c := by
  obtain ⟨n0, _, hReach⟩ := hCommon
  have hn0 : n = n0 := root_eq_common _ w n0 n hReach hn
  subst hn0
  obtain ⟨c, hcC, hcE, v, hv, hcv⟩ := hSome
  have hnv : F.history.ontic.ExistsAt v n := hNec n hn v hv
  rcases hReach c ⟨hcC, hcE⟩ with h | hgc
  · subst h
    exact absurd hnv hcv
  · exact ⟨c, hcC, ⟨hcE, v, hv, hcv⟩, hn.1.2, (hB n c hgc).1 hcE, v, hv, hnv,
      fun hg => hcv (hGE v n c hg)⟩

/-- Argument N2: (a) from uniformity at the root (with the root and reach clauses
of `0c27f65a` as the common root). By law 2 the root is two-way
toward a contingent being; uniformity makes it two-way toward every being it
gives at `w`, and by (b) it gives each actual concretum it grounds. -/
theorem rootWithholdingFromUniformity {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop) (w : W)
    (hB : ActualGroundsGiveWhereverGroundedExists F concrete G w) (hGE : GivenExists F)
    (hIG : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (hNec : ActualRootsNecessary F concrete G w) (hSome : SomeContingentConcreteAt F concrete w)
    (hU : ActualRootsGiveUniformly F concrete G w) :
    ActualRootsWithholdEachGrounded F concrete G w := by
  intro n x hn hx hgx
  obtain ⟨c, _, _, hc⟩ := root_twoWay_toward_contingent F concrete G w hB hGE
    (commonRoot_of_intellectual _ w IsGod HasIntellect hIG) hNec hSome n hn
  obtain ⟨_, _, hw⟩ := hU n hn ⟨c, hc⟩ x ((hB n x hgx).1 hx.2)
  exact hw

/-- The will step shared by N3 and law 5: if the root gives `x` being at `w`,
and never withholds it at an accessible world where it exists, it is fixed
toward `x`; its giving is a rational exercise, so WN makes `x` required by the
root's end, which SS denies. -/
theorem will_step {W B T R S P : Type} (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop)
    (EndRequires : B → B → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hIG : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (hWill : OnePowerIntellectualGivingWilled F A HasIntellect)
    (hOne : ActualRootsOnePower F A concrete G w)
    (hWN : RationalFixedGivingIsRequired F A EndRequires w)
    (hSS : ActualRootsEndRequiresNoOther F concrete G EndRequires w)
    (n x : B) (hn : ActualRoot (groundProfile F concrete G) w n)
    (hgx : ActualConcreteGround (groundProfile F concrete G) w n x)
    (hgw : GivesTo F w n x) :
    ∃ v, F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v n ∧ ¬ GivesTo F v n x := by
  rcases hEM (∃ v, F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v n ∧
      ¬ GivesTo F v n x) with h | h
  · exact h
  · exfalso
    obtain ⟨n0, _, hReach, _, hInt⟩ := hIG
    have hn0 : n = n0 := root_eq_common _ w n0 n hReach hn
    have hfix : FixedTowardAt F w n x := ⟨hgw, fun v hv hnv => by
      rcases hEM (GivesTo F v n x) with g | g
      · exact g
      · exact absurd ⟨v, hv, hnv, g⟩ h⟩
    obtain ⟨p, hp, hr, hex⟩ := hWill n (hn0 ▸ hInt) (hOne n hn) w x hgw
    exact hSS n x hn (ne_of_root_grounds _ w n x hn hgx) (hWN n p x hp hr hex hfix)

/-- Argument N3: (a) from the will route. The common GOD_4 root with intellect
(`0c27f65a`) is every actual root; with one power its giving is the exercise of
a rational power (#1941 `5c1aba17`). A root that never withheld a being it
grounds would, by (b), give it being at `w` and be fixed toward it; WN then
makes that being required by the root's end, against SS. Excluded middle. -/
theorem rootWithholdingFromWill {W B T R S P : Type} (F : CausalityFrame W B T R)
    (A : AgencyFrame W B S P) (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop)
    (EndRequires : B → B → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hIG : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (hWill : OnePowerIntellectualGivingWilled F A HasIntellect)
    (hOne : ActualRootsOnePower F A concrete G w)
    (hB : ActualGroundsGiveWhereverGroundedExists F concrete G w)
    (hWN : RationalFixedGivingIsRequired F A EndRequires w)
    (hSS : ActualRootsEndRequiresNoOther F concrete G EndRequires w) :
    ActualRootsWithholdEachGrounded F concrete G w := by
  intro n x hn hx hgx
  exact will_step F A concrete IsGod HasIntellect G EndRequires w hEM hIG hWill hOne hWN hSS
    n x hn hgx ((hB n x hgx).1 hx.2)

theorem laws : Laws := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro W B T R F w y
    constructor
    · rintro ⟨hy, x, v, hv, hyv, hg, hng⟩
      exact ⟨x, hy, hg, v, hv, hyv, hng⟩
    · rintro ⟨x, hy, hg, v, hv, hyv, hng⟩
      exact ⟨hy, x, v, hv, hyv, hg, hng⟩
  · intro W B T R F concrete G w hB hGE hCommon hNec hSome n hn
    exact root_twoWay_toward_contingent F concrete G w hB hGE hCommon hNec hSome n hn
  · intro W B T R F concrete G w hEM hB hGE hCommon hNec
    constructor
    · intro hNAR n x hn hx hgx
      have hnr : ¬ ActualRoot (groundProfile F concrete G) w x := fun hr => hr.2 n hgx
      rcases hEM (∃ v, F.history.ontic.frame.access w v ∧ ¬ F.history.ontic.ExistsAt v x)
        with ⟨v, hv, hxv⟩ | h
      · exact ⟨v, hv, hNec n hn v hv, fun hg => hxv (hGE v n x hg)⟩
      · exfalso
        refine hnr (hNAR x hx fun v hv => ?_)
        rcases hEM (F.history.ontic.ExistsAt v x) with e | e
        · exact e
        · exact absurd ⟨v, hv, e⟩ h
    · exact nar_of_commonRoot F concrete G w hCommon hB
  · intro W B T R S P F A w y hInv hExGive hGiveEx x ⟨_, hg, v, hv, hyv, hng⟩
    obtain ⟨p, _, hex⟩ := hGiveEx x hg
    exact hng (hExGive v x p (hInv v x p hv hyv hex))
  · intro W B T R S P F A concrete IsGod HasIntellect G EndRequires w hRefl hEM hIG hWill hOne
      hWN hSS n x hn _ hgx
    rcases hEM (GivesTo F w n x) with hgw | hgw
    · exact will_step F A concrete IsGod HasIntellect G EndRequires w hEM hIG hWill hOne hWN hSS
        n x hn hgx hgw
    · exact ⟨w, hRefl, hn.1.2, hgw⟩

macro "nd_unfold" : tactic => `(tactic|
  simp only [TruthCore.Logic.ExcludedMiddle, ActualCommonRootAt,
    ActualGroundsGiveWhereverGroundedExists, ActualRootsWithholdEachGrounded,
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

theorem theistNonvacuity : TheistNonvacuity := by
  unfold TheistNonvacuity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nd_close

theorem mixedModeRoot : MixedModeRoot := by
  unfold MixedModeRoot
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;> nd_close

theorem omissionsN1 : OmissionsN1 := by
  unfold OmissionsN1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> nd_close

theorem omissionsN2 : OmissionsN2 := by
  unfold OmissionsN2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> nd_close

theorem omissionsN3 : OmissionsN3 := by
  unfold OmissionsN3
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> nd_close

/-- Argument N4, the certificate of laws and models. Premise-free. -/
theorem narDerivationControls : Controls :=
  ⟨laws, theistNonvacuity, mixedModeRoot, omissionsN1, omissionsN2, omissionsN3⟩

end TruthCore.Results.Causality.NarDerivation
