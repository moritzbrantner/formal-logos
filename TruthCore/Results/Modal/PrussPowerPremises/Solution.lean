module

public import TruthCore.Modal.PrussPowerPremises
public import TruthCore.Results.Modal.ModalGroundingActualAbsence.Solution

/-! The power premises of the route with Pruss's own premise (#1887,
continued): the transfer from the collective power to powers over each actual
contingent's esse, the one-way/two-way profile of the holder's giving, and
Pruss's own direction. Analyst reconstructions; attribution deferred. Excluded
middle enters only as the explicit premise `TruthCore.Logic.ExcludedMiddle`. -/

@[expose] public section

namespace TruthCore.Results.Modal.PrussPowerPremises
open TruthCore.Modal.ModalGrounding
open TruthCore.Modal.PrussPowerPremises
open TruthCore.Modal.PrussPowerPremises.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Causality.ContingencyGrounding (PowerOverEsse)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.BruteFoundationBoundary (NecessaryConcreteAt)

/-- Argument 1, the transfer. A concrete `x` is contingent at `w`, so the joint
absence `q` fails at `w`, while P4′ gives an accessible world where it holds;
P1′ gives a being `y` at `w` with a power for `q`; the transfer gives `y`
POWER_OVER_ESSE_1 over each concrete being contingent at `w`. Constructive. -/
theorem transferGivesPowerOverEachActualContingent {W B T R : Type}
    (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (PowerOver : B → B → R → Prop) (concrete : B → Prop) (w : W)
    (hGround : ActualAbsenceGrounded F PowerFor concrete w)
    (hPoss : PossiblyNoActualContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hTransfer : ActualAbsencePowerIsPowerOverEsse F PowerFor PowerOver concrete w) :
    SomeHolderHasPowerOverEachActualContingent F PowerFor PowerOver concrete w := by
  obtain ⟨x, hxc, hx⟩ := hSome
  obtain ⟨y, hyw, hpow⟩ := hGround hPoss (fun h => h x hxc hx hx.1)
  exact ⟨y, hyw, hpow, fun z hzc hz => hTransfer y z hpow hzc hz⟩

/-- P2δ gives P2′: forget the difference in giving. -/
theorem exerciseDiffersGivesInitiator {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (h : ActualAbsenceExerciseDiffers F PowerFor concrete w) :
    ActualAbsenceInitiatorPresent F PowerFor concrete w := by
  intro y hy
  obtain ⟨v, hwv, hq, hyv, _⟩ := h y hy
  exact ⟨v, hwv, hq, hyv⟩

/-- Argument 2, the holder is a necessary varying giver. P2δ gives P2′, so the
route `prussActualAbsenceNecessaryPowerHolder` (#1889) gives a necessary
concrete holder `y` of a power for `q`; P2δ applied to `y` gives an accessible
world where `y` exists and gives being otherwise than at `w`. -/
theorem actualAbsenceHolderIsNecessaryVaryingGiver {W B T R : Type}
    (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop)
    (w : W) (hEM : TruthCore.Logic.ExcludedMiddle)
    (hGround : ActualAbsenceGrounded F PowerFor concrete w)
    (hDiff : ActualAbsenceExerciseDiffers F PowerFor concrete w)
    (hConcrete : ActualAbsencePowerHoldersConcrete F PowerFor concrete w)
    (hPoss : PossiblyNoActualContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w) :
    NecessaryVaryingGiverWithActualAbsencePower F PowerFor concrete w := by
  obtain ⟨y, hyc, hyw, hyn, hpow⟩ :=
    TruthCore.Results.Modal.ModalGroundingActualAbsence.prussActualAbsenceNecessaryPowerHolder
      F PowerFor concrete w hEM hGround (exerciseDiffersGivesInitiator F PowerFor concrete w hDiff)
      hConcrete hPoss hSome
  obtain ⟨v, hwv, _, hyv, hdiff⟩ := hDiff y hpow
  exact ⟨y, hyc, hyw, hyn, hpow, hyw, v, hwv, hyv, hdiff⟩

/-- Argument 3, projection onto the route's conclusion `b90ee2de`: forget the
varying giving. An assembly. -/
theorem varyingGiverGivesNecessaryPowerHolder {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (h : NecessaryVaryingGiverWithActualAbsencePower F PowerFor concrete w) :
    NecessaryConcreteActualAbsencePowerAt F PowerFor concrete w := by
  obtain ⟨y, hc, he, hn, hp, _⟩ := h
  exact ⟨y, hc, he, hn, hp⟩

/-- Argument 4, the joint absence realized by withholding. P1′ gives a holder
`y` at `w`; P2′ an accessible world `v` where `q` holds and `y` exists. By the
creator reading `y` gives each actual contingent concretum being at `w`; at `v`
each is absent, so by factive giving `y` gives none of them being there.
Constructive. -/
theorem actualAbsenceRealizedByWithholding {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hGround : ActualAbsenceGrounded F PowerFor concrete w)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hPoss : PossiblyNoActualContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hGive : ActualAbsenceHoldersGiveEach F PowerFor concrete w)
    (hFactive : GivenExists F) :
    ActualAbsenceByWithholding F PowerFor concrete w := by
  obtain ⟨x, hxc, hx⟩ := hSome
  obtain ⟨y, hyw, hpow⟩ := hGround hPoss (fun h => h x hxc hx hx.1)
  obtain ⟨v, hwv, hq, hyv⟩ := hInit y hpow
  exact ⟨y, hyw, hpow, v, hwv, hq, hyv, fun z hzc hz =>
    ⟨hGive y hpow z hzc hz, fun hg => hq z hzc hz (hFactive v y z hg)⟩⟩

/-- Argument 5, the transfer's conclusion without the transfer: a holder that
gives each actual contingent concretum being at `w` and withholds each at an
accessible world where it exists has, by the withheld-giving bridge,
POWER_OVER_ESSE_1 over each. -/
theorem withholdingGivesPowerOverEachActualContingent {W B T R : Type}
    (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (PowerOver : B → B → R → Prop) (concrete : B → Prop) (w : W)
    (hWith : ActualAbsenceByWithholding F PowerFor concrete w)
    (hBridge : WithheldGivingIsPowerOverEsse F PowerOver w) :
    SomeHolderHasPowerOverEachActualContingent F PowerFor PowerOver concrete w := by
  obtain ⟨y, hyw, hpow, v, hwv, _, hyv, hall⟩ := hWith
  exact ⟨y, hyw, hpow, fun x hxc hx =>
    hBridge y x v (hall x hxc hx).1 hwv hyv (hall x hxc hx).2⟩

/-- Argument 6, Pruss's own direction. P4′ gives an accessible world `v`
lacking every actual contingent concretum; P5's witness shows `v ≠ w`;
symmetric access gives `v`'s access to `w`; grounding at `v` gives a being `y`
at `v` with a power for `w`'s obtaining; initiator presence puts `y` at `w`; `y`
is concrete. Were `y` absent at some world accessible from `w`, it would be an
actual contingent concretum, hence absent at `v`, where it exists. Excluded
middle gives `y`'s existence at every world accessible from `w`. Only the B
part (symmetry) of S5 is used. -/
theorem prussDirectionNecessaryHolder {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hSym : TruthCore.Modal.Symmetric F.history.ontic.frame)
    (hPoss : PossiblyNoActualContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hGround : ActualityGroundedAtAbsenceWorlds F PowerFor concrete w)
    (hInit : ActualityInitiatorPresentAtAbsenceWorlds F PowerFor concrete w)
    (hConcrete : ActualityPowerHoldersConcreteAtAbsenceWorlds F PowerFor concrete w) :
    NecessaryConcreteHolderOfActualityPower F PowerFor concrete w := by
  obtain ⟨x, hxc, hx⟩ := hSome
  obtain ⟨v, hwv, hq⟩ := hPoss
  have hne : ¬ v = w := fun h => hq x hxc hx (h ▸ hx.1)
  obtain ⟨y, hyv, hpow⟩ := hGround v hwv hq ⟨w, hSym w v hwv, rfl⟩ hne
  obtain ⟨u, _, rfl, hyw⟩ := hInit v hwv hq y hpow
  have hyc := hConcrete v hwv hq y hpow
  refine ⟨y, v, hyc, hyw, fun u' hwu => ?_, hwv, hq, hyv, hpow⟩
  rcases hEM (F.history.ontic.ExistsAt u' y) with h | h
  · exact h
  · exact (hq y hyc ⟨hyw, u', hwu, h⟩ hyv).elim

/-- Argument 7, projection of Pruss's direction onto the stage-one node:
forget the power and the absence world. An assembly. -/
theorem prussDirectionNecessaryConcrete {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W) (h : NecessaryConcreteHolderOfActualityPower F PowerFor concrete w) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  obtain ⟨y, _, hc, he, hn, _⟩ := h
  exact ⟨y, hc, he, hn⟩

/-- Argument 9, the transfer's conclusion at the foundational case. A concrete
foundational being `f` at `w` (statement `c5da5e62`) is under no being's
POWER_OVER_ESSE_1; were it absent at a world accessible from `w`, it would be a
concrete being contingent at `w`, over whose esse the holder has power. So,
with excluded middle, `f` exists at every accessible world and witnesses the
stage-one node. PGP's verdict at the foundational case, reproduced through the
distributive powers, without PGP and without a Euclidean premise. -/
theorem powerOverEachGivesNecessaryConcrete {W B T R P : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (PowerOver : B → B → R → Prop)
    (concrete : B → Prop) (grounds : W → B → B → Prop) (w : W) (essenceOf esseOf : B → P)
    (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hEach : SomeHolderHasPowerOverEachActualContingent F PowerFor PowerOver concrete w)
    (hFound : SomeConcreteFoundationalAt F w essenceOf esseOf Received ComposedOfMatterAndForm
      CanFailToBe PowerOver concrete) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  obtain ⟨f, hfc, hf⟩ := hFound
  obtain ⟨y, _, _, hover⟩ := hEach
  refine ⟨f, hfc, hf.1, fun u hwu => ?_⟩
  rcases hEM (F.history.ontic.ExistsAt u f) with h | h
  · exact h
  · exact (hf.2.2.2.2.2.2.2 y (hover f hfc ⟨hf.1, u, hwu, h⟩)).elim

/-! ## Laws and models -/

theorem laws : Laws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B T R F PowerFor concrete w y hDiff hpow hyw hfix
    obtain ⟨v, _, _, hyv, hdiff⟩ := hDiff y hpow
    exact hdiff (hfix w v hyw hyv)
  · intro W B T R F PowerFor concrete w hGround hDiff hPoss hSome hall
    obtain ⟨x, hxc, hx⟩ := hSome
    obtain ⟨y, hyw, hpow⟩ := hGround hPoss (fun h => h x hxc hx hx.1)
    obtain ⟨v, _, _, hyv, hdiff⟩ := hDiff y hpow
    exact hdiff (hall y hyw w v hyw hyv)
  · intro W B T R F w y hFactive hyw hyn hfix x hx v hwv
    exact hFactive v y x ((hfix w v hyw (hyn v hwv) x).1 hx)
  · intro W B T R F concrete w hFactive hall ⟨x, hxc, hx⟩
    obtain ⟨y, hyw, hyn, hfix, hgx⟩ := hall x hxc hx
    obtain ⟨_, v, hwv, hxv⟩ := hx
    exact hxv (hFactive v y x ((hfix w v hyw (hyn v hwv) x).1 hgx))
  · intro W B T R F PowerFor concrete w hGive hFactive hInit ⟨x, hxc, hx⟩ y hpow
    obtain ⟨v, hwv, hq, hyv⟩ := hInit y hpow
    exact ⟨v, hwv, hq, hyv, fun hsame =>
      hq x hxc hx (hFactive v y x ((hsame x).1 (hGive y hpow x hxc hx)))⟩
  · intro W B T R F PowerFor concrete w hWith ⟨x, hxc, hx⟩
    obtain ⟨y, hyw, _, v, hwv, _, hyv, hall⟩ := hWith
    have hxy := hall x hxc hx
    refine ⟨y, ⟨hyw, x, v, hwv, hyv, hxy.1, hxy.2⟩,
      ⟨hyw, v, hwv, hyv, fun hs => hxy.2 ((hs x).1 hxy.1)⟩, fun hfix => ?_⟩
    exact hxy.2 ((hfix w v hyw hyv x).1 hxy.1)
  · intro W B T R F concrete w v y x hFactive hwv hq hyw hyv hxc hx hgx
    exact ⟨hyw, x, v, hwv, hyv, hgx, fun hg => hq x hxc hx (hFactive v y x hg)⟩
  · intro W B T R F concrete w y hEM hyc hyw hall u hwu
    rcases hEM (F.history.ontic.ExistsAt u y) with h | h
    · exact h
    · obtain ⟨v, _, hnv, hyv⟩ := hall y hyc ⟨hyw, u, hwu, h⟩
      exact (hnv hyv).elim
  · intro W B T R P F PowerFor PowerOver concrete w essenceOf esseOf Received MF CanFailToBe
      hEM ⟨y, _, _, hover⟩ f hfc hf u hwu
    rcases hEM (F.history.ontic.ExistsAt u f) with h | h
    · exact h
    · exact (hf.2.2.2.2.2.2.2 y (hover f hfc ⟨hf.1, u, hwu, h⟩)).elim

macro "pp_unfold" : tactic => `(tactic|
  simp only [ActualAbsenceGrounded, ActualAbsenceInitiatorPresent, ActualAbsencePowerHoldersConcrete,
    PossiblyNoActualContingentConcrete, SomeContingentConcreteAt, NoActualContingentConcreteIn,
    AristotelianGroundingFor, InitiatorPresentFor, PowerHoldersConcreteFor,
    ActualAbsenceExerciseDiffers, ActualAbsenceHoldersGiveEach, GivenExists,
    ActualAbsencePowerIsPowerOverEsse, WithheldGivingIsPowerOverEsse,
    ActualityGroundedAtAbsenceWorlds, ActualityInitiatorPresentAtAbsenceWorlds,
    ActualityPowerHoldersConcreteAtAbsenceWorlds, SomeHolderHasPowerOverEachActualContingent,
    NecessaryVaryingGiverWithActualAbsencePower, ActualAbsenceByWithholding,
    NecessaryConcreteHolderOfActualityPower, EachActualAbsenceGrounded,
    EachActualAbsenceInitiatorPresent, TwoWayGiverAt, GivingVariesAt, FixedGiver, GivingSameIn,
    GivesTo, PowerOverEsse, NecessaryAt, ContingentAt, TruthCore.Modal.Symmetric,
    theistG, nonFactiveG, replacementG, inertG, necessitarianG, forwardG, absentHolderG, mutualG,
    vanCleveG, gFrame, allC, onlyCD, uni, forwardOnly, gcEx, gcAlways, replEx, gOnlyThereEx,
    givesCHere, givesCAlways, givesDThere, noGiving, gPower, gPowerThere, noPower,
    positivePower, gOverC, gOverCD, noOver, pairEx, annihilatorPower, vcEx, vcGives])

theorem theistNonvacuity : TheistNonvacuity := by
  unfold TheistNonvacuity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  pp_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff]

theorem collectiveWithoutDistributive : CollectiveWithoutDistributive := by
  unfold CollectiveWithoutDistributive
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  pp_unfold <;> simp [Bool.exists_bool, Bg.forall_iff]

theorem distributiveWithoutCollective : DistributiveWithoutCollective := by
  unfold DistributiveWithoutCollective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  pp_unfold <;> simp [V3.exists_iff, Bg.forall_iff]

theorem mutualAnnihilators : MutualAnnihilators := by
  unfold MutualAnnihilators
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  pp_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Prod.forall, Prod.exists,
    Bg.forall_iff]

theorem omissions : Omissions := by
  unfold Omissions
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  pp_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, V3.exists_iff,
    Bg.forall_iff, Bg.exists_iff]

theorem rivals : Rivals := by
  unfold Rivals
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  pp_unfold <;> simp [Bool.exists_bool]

/-- Argument 8, the certificate of laws and models. Premise-free. -/
theorem prussPowerControls : Controls :=
  ⟨laws, theistNonvacuity, collectiveWithoutDistributive, distributiveWithoutCollective,
    mutualAnnihilators, omissions, rivals⟩

end TruthCore.Results.Modal.PrussPowerPremises
