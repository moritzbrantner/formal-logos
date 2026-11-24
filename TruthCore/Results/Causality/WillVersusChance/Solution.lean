module

public import TruthCore.Causality.WillVersusChance
public import TruthCore.Results.Modal.PrussPowerPremises.Solution

/-! Choice versus chance at a necessary, patientless source (stage two,
`66aecdd7`): intellect and one power make every giving willed, and so make the
withholding holder a willed two-way giver; the Θ.5 principle restricted to
sources with an invariant set-up turns an invariant two-way giver into a being
with will, and with the GOD_4 bridge and #1897's creator premises gives GOD_4
will; the strong Θ.5 principle implies the restricted one. Analyst
reconstructions; attribution deferred. -/

@[expose] public section

namespace TruthCore.Results.Causality.WillVersusChance
open TruthCore.Causality.WillVersusChance
open TruthCore.Causality.WillVersusChance.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Modal.PrussPowerPremises (GivesTo GivingSameIn TwoWayGiverAt GivenExists
  ActualAbsenceHoldersGiveEach ActualAbsenceByWithholding)
open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 Bg.forall_iff Bg.exists_iff V3.forall_iff
  V3.exists_iff theistG inertG nonFactiveG
  necessitarianG gFrame allC onlyCD uni gcEx gcAlways givesCHere givesCAlways noGiving gPower noPower)
open TruthCore.Modal.ModalGrounding (SomeContingentConcreteAt NoActualContingentConcreteIn
  ActualAbsenceInitiatorPresent)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (WillFollowsIntellectReading)
open TruthCore.Case.Catholicism (GodHasWill)

/-- Argument A, the intellect route to willed giving. An intellectual `y` has
will (will follows intellect, `090be689`), hence a rational power `q`; each
giving of `y` exercises some power `p` of `y`; with one power, `p = q`, so the
giving exercises a rational power. Constructive. -/
theorem oneIntellectualPowerGivesWilledGiving {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (HasIntellect HasWill : B → Prop)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill)
    (hRat : WillIsRationalPower A HasWill)
    (hEx : GivingExercisesOwnPower F A) :
    OnePowerIntellectualGivingWilled F A HasIntellect := by
  intro y hI hOne v x hg
  obtain ⟨q, hq, hr⟩ := hRat y (hWill y hI)
  obtain ⟨p, hp, he⟩ := hEx v y x hg
  exact ⟨p, hp, hOne q p hq hp ▸ hr, he⟩

/-- Argument B, the withholding holder gives by will. Withholding gives a holder
`y` at `w` that gives each actual contingent concretum being at `w` and none of
them at an accessible world `v` where it exists; P5 supplies one, `x`. The
holder has intellect and one power, so by argument A's conclusion its giving of
`x` at `w` exercises a rational power; its invariant set-up makes `v` a world
with the same set-up. Constructive. -/
theorem actualAbsenceHolderGivesByWill {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (HasIntellect : B → Prop) (w : W)
    (hWith : ActualAbsenceByWithholding F PowerFor concrete w)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hInv : ActualAbsenceHoldersSetupInvariant F A PowerFor concrete w)
    (hInt : ActualAbsenceHoldersHaveIntellect F PowerFor concrete HasIntellect w)
    (hOne : ActualAbsenceHoldersOnePower F A PowerFor concrete w)
    (hWilled : OnePowerIntellectualGivingWilled F A HasIntellect) :
    ActualAbsenceHolderGivesByWill F A PowerFor concrete w := by
  obtain ⟨x, hxc, hx⟩ := hSome
  obtain ⟨y, hyw, hpow, v, hwv, _, hyv, hall⟩ := hWith
  obtain ⟨hg, hng⟩ := hall x hxc hx
  obtain ⟨p, hp, hr, he⟩ := hWilled y (hInt y hpow) (hOne y hpow) w x hg
  exact ⟨y, hpow, hyw, p, x, v, hp, hr, hwv, hyv, hInv y hpow v hwv hyv, ⟨hg, he⟩, hng⟩

/-- Argument C, the Θ.5 bridge, restricted. A two-way giver `y` with an invariant
set-up gives `x` being at `w` by some power `p`, and does not give it at an
accessible `v` where it exists; DNP_inv makes `p` rational, and a being with a
rational power has will. Constructive. -/
theorem thetaFiveBridgeGivesWill {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (HasWill : B → Prop) (w : W)
    (hD : InvariantSetupVariationIsRational F A w)
    (hEx : GivingExercisesOwnPower F A)
    (hRW : RationalPowerIsWill A HasWill) :
    InvariantSetupTwoWayGiversWill F A HasWill w := by
  intro y hInv ⟨hyw, x, v, hwv, hyv, hg, hng⟩
  obtain ⟨p, hp, he⟩ := hEx w y x hg
  exact hRW y p hp (hD y p x v hInv hyw hwv hyv hp ⟨hg, he⟩ hng)

/-- Argument D, GOD_4 has will by the restricted Θ.5 bridge. Each GOD_4 `g`
exists at `w` and holds the power for the joint absence of the actual
contingent concreta (bridge); P2′ puts `g` at an accessible world `v` where they
are all absent; P5 gives one, `x`; by the creator reading `g` gives `x` being at
`w`, and by factive giving not at `v`. So `g` is a two-way giver at `w`; its
set-up is invariant (holder premise); argument C's conclusion gives it will.
Constructive. -/
theorem godHasWillByThetaFive {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (IsGod HasWill : B → Prop)
    (w : W)
    (hGod : GodsHoldActualAbsencePower F PowerFor concrete IsGod w)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hGive : ActualAbsenceHoldersGiveEach F PowerFor concrete w)
    (hFact : GivenExists F)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hInv : ActualAbsenceHoldersSetupInvariant F A PowerFor concrete w)
    (hWill : InvariantSetupTwoWayGiversWill F A HasWill w) :
    GodHasWill IsGod HasWill := by
  intro g hg
  obtain ⟨hgw, hpow⟩ := hGod g hg
  obtain ⟨v, hwv, hq, hgv⟩ := hInit g hpow
  obtain ⟨x, hxc, hx⟩ := hSome
  have hgx : GivesTo F w g x := hGive g hpow x hxc hx
  refine hWill g (hInv g hpow) ⟨hgw, x, v, hwv, hgv, hgx, fun hgxv => hq x hxc hx ?_⟩
  exact hFact v g x hgxv

/-- Argument E, the strength order: DNP′ implies DNP_inv (an invariant set-up
gives the same set-up at the withholding world). Constructive. -/
theorem sameSetupVariationIsRationalWeakens {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W)
    (hD : SameSetupVariationIsRational F A w) :
    InvariantSetupVariationIsRational F A w := by
  intro y p x v hInv hyw hwv hyv hp hgb hng
  exact hD y p x v hyw hwv hyv hp (hInv v hwv hyv) hgb hng

/-! ## Laws and models -/

theorem laws : Laws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B T R S P F A w y hInv
    refine ⟨?_, ?_⟩
    · rintro ⟨_, v, hwv, hyv, _, z, _, hz⟩
      exact hz ((hInv v hwv hyv).2 z)
    · rintro ⟨_, v, hwv, hyv, _, hs⟩
      exact hs (hInv v hwv hyv)
  · intro W B T R S P F A w hVG
    refine ⟨?_, fun y hInv => ⟨?_, ?_⟩⟩
    · intro y hInv ⟨hyw, x, v, hwv, hyv, hg, hng⟩
      exact hVG y v hwv hyw hyv (fun hs => hng ((hs x).1 hg)) (hInv v hwv hyv)
    · rintro ⟨hyw, p, x, v, _, _, hwv, hyv, hsame, ⟨hg, _⟩, hng⟩
      exact hVG y v hwv hyw hyv (fun hs => hng ((hs x).1 hg)) hsame
    · rintro ⟨hyw, p, x, v, _, _, hwv, hyv, hsame, ⟨hg, _⟩, hng⟩
      exact hVG y v hwv hyw hyv (fun hs => hng ((hs x).1 hg)) hsame
  · intro W B T R S P F A w hVG y p x v hyw hwv hyv _ hsame hgb hng
    exact (hVG y v hwv hyw hyv (fun hs => hng ((hs x).1 hgb.1)) hsame).elim
  · intro W B T R S P F A w hD y ⟨hyw, p, x, v, hpow, hnr, hwv, hyv, hsame, hgb, hng⟩
    exact hnr (hD y p x v hyw hwv hyv hpow hsame hgb hng)
  · intro W B T R S P F A w y
    refine ⟨?_, ?_, fun _ _ _ => Iff.rfl⟩
    · rintro ⟨hyw, p, x, v, hpow, _, hwv, hyv, hsame, hgb, hng⟩
      exact ⟨hyw, p, x, v, hpow, fun h => h, hwv, hyv, hsame, hgb, hng⟩
    · rintro ⟨hyw, p, x, v, hpow, _, hwv, hyv, hsame, hgb, hng⟩
      exact ⟨hyw, p, x, v, hpow, trivial, hwv, hyv, hsame, hgb, hng⟩
  · intro W B T R S P F A HasWill w y hWR hW hOne ⟨_, p, _, _, hpow, hnr, _⟩
    obtain ⟨q, hq, hr⟩ := hWR y hW
    exact hnr (hOne q p hq hpow ▸ hr)
  · intro W B T R S P F A w y
    refine ⟨?_, ?_⟩
    · rintro ⟨hyw, p, x, v, _, _, hwv, hyv, _, ⟨hg, _⟩, hng⟩
      exact ⟨hyw, x, v, hwv, hyv, hg, hng⟩
    · rintro ⟨hyw, p, x, v, _, _, hwv, hyv, _, ⟨hg, _⟩, hng⟩
      exact ⟨hyw, x, v, hwv, hyv, hg, hng⟩
  · intro W B T R S P F A w y hFact hNec hInv hNst x hg v hwv
    have hyv := hNec v hwv
    exact hFact v y x ((hNst v hwv hyv (hInv v hwv hyv) x).1 hg)
  · intro W B T R S P F A w hEM
    constructor
    · intro hVG y hyw v hwv hyv hsame
      rcases hEM (GivingSameIn F y w v) with h | h
      · exact h
      · exact (hVG y v hwv hyw hyv h hsame).elim
    · intro hN y v hwv hyw hyv hng hsame
      exact hng (hN y hyw v hwv hyv hsame)
  · intro W B T R S P F A PowerFor concrete w hWith hSome hInv
    obtain ⟨x, hxc, hx⟩ := hSome
    obtain ⟨y, hyw, hpow, v, hwv, _, hyv, hall⟩ := hWith
    obtain ⟨hg, hng⟩ := hall x hxc hx
    refine ⟨y, hyw, hpow, ⟨hyw, x, v, hwv, hyv, hg, hng⟩, fun hN => ?_⟩
    exact hng ((hN v hwv hyv (hInv y hpow v hwv hyv) x).1 hg)
  · intro W B T R S P F A w hEM
    refine ⟨⟨fun hD y => ?_, fun hN y p x v hyw hwv hyv hp hsame hgb hng => ?_⟩,
      ⟨fun hD y hInv => ?_, fun hN y p x v hInv hyw hwv hyv hp hgb hng => ?_⟩⟩
    · rintro ⟨hyw, p, x, v, hpow, hnr, hwv, hyv, hsame, hgb, hng⟩
      exact hnr (hD y p x v hyw hwv hyv hpow hsame hgb hng)
    · rcases hEM (A.Rational p) with h | h
      · exact h
      · exact (hN y ⟨hyw, p, x, v, hp, h, hwv, hyv, hsame, hgb, hng⟩).elim
    · rintro ⟨hyw, p, x, v, hpow, hnr, hwv, hyv, _, hgb, hng⟩
      exact hnr (hD y p x v hInv hyw hwv hyv hpow hgb hng)
    · rcases hEM (A.Rational p) with h | h
      · exact h
      · exact (hN y hInv ⟨hyw, p, x, v, hp, h, hwv, hyv, hInv v hwv hyv, hgb, hng⟩).elim
  · intro W B T R S P F A w y
    refine ⟨fun hEM hEx hInv ⟨hyw, x, v, hwv, hyv, hg, hng⟩ => ?_, ?_⟩
    · obtain ⟨p, hp, he⟩ := hEx w y x hg
      rcases hEM (A.Rational p) with h | h
      · exact Or.inl ⟨hyw, p, x, v, hp, h, hwv, hyv, hInv v hwv hyv, ⟨hg, he⟩, hng⟩
      · exact Or.inr ⟨hyw, p, x, v, hp, h, hwv, hyv, hInv v hwv hyv, ⟨hg, he⟩, hng⟩
    · rintro hOne ⟨⟨_, p, _, _, hp, hr, _⟩, ⟨_, q, _, _, hq, hnr, _⟩⟩
      exact hnr (hOne p q hp hq ▸ hr)
  · intro W B T R S P F A HasIntellect HasWill w y hOne ⟨_, p, _, _, hpow, hnr, _⟩ hI hWF hWR
    obtain ⟨q, hq, hr⟩ := hWR y (hWF y hI)
    exact hnr (hOne q p hq hpow ▸ hr)

macro "wc_unfold" : tactic => `(tactic|
  simp only [WillFollowsIntellectReading, WillIsRationalPower, GivingExercisesOwnPower,
    OnePowerIntellectualGivingWilled, SameSetupVariationIsRational, RationalPowerIsWill,
    InvariantSetupVariationIsRational, InvariantSetupTwoWayGiversWill,
    ActualAbsenceHoldersSetupInvariant, ActualAbsenceHoldersHaveIntellect,
    ActualAbsenceHoldersOnePower, ActualAbsenceHolderGivesByWill, GodsHoldActualAbsencePower,
    GodHasWill, SetupInvariantAt, SetupNecessitatedAt, OnePower, WilledTwoWayAt,
    PropensityChanceAt, VariationNeedsVaryingSetup, NoTwoWayGiverWithInvariantSetup,
    SetupVariationAt, IncidentalVariationAt, SetupSameIn, GivesBy,
    ActualAbsenceByWithholding, SomeContingentConcreteAt, NoActualContingentConcreteIn,
    ActualAbsenceInitiatorPresent, TruthCore.Modal.ModalGrounding.InitiatorPresentFor,
    ActualAbsenceHoldersGiveEach, GivenExists,
    TwoWayGiverAt, GivingSameIn, GivesTo, TruthCore.German.Kant.CosmologicalInference.ContingentAt,
    AgencyFrame.reclassify, simpleRational, simpleChancy, twoPowerChancer, idleRational,
    powerless, varyingState, varyingRational, concurrence, onlyG, nobody, onlyCD,
    gcHereOnlyEx, holderHereOnlyG, threeWorldG, threeWorldChancy, zFlag,
    theistG, inertG, nonFactiveG, necessitarianG, gFrame, allC, uni, gcEx, gcAlways, givesCHere,
    givesCAlways, noGiving, gPower, noPower])

theorem theistNonvacuity : TheistNonvacuity := by
  unfold TheistNonvacuity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]

theorem chanceRival : ChanceRival := by
  unfold ChanceRival
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]

theorem intellectualChancer : IntellectualChancer := by
  unfold IntellectualChancer
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]

theorem chanceCoreDeletions : ChanceCoreDeletions := by
  unfold ChanceCoreDeletions
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]

theorem omissionsIntellectRoute : OmissionsIntellectRoute := by
  unfold OmissionsIntellectRoute
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]

theorem omissionsHolderWill : OmissionsHolderWill := by
  unfold OmissionsHolderWill
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]

theorem omissionsThetaFive : OmissionsThetaFive := by
  unfold OmissionsThetaFive
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]

theorem omissionsGodWill : OmissionsGodWill := by
  unfold OmissionsGodWill
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_⟩⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]

theorem dnpStrictness : DNPStrictness := by
  unfold DNPStrictness
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff,
    V3.forall_iff, V3.exists_iff]

theorem senseModels : SenseModels := by
  unfold SenseModels
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩ <;>
  wc_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Bg.forall_iff, Bg.exists_iff]

/-- Argument F, the certificate of laws and models. Premise-free. -/
theorem willVersusChanceControls : Controls :=
  ⟨laws, theistNonvacuity, chanceRival, intellectualChancer, chanceCoreDeletions,
    omissionsIntellectRoute, omissionsHolderWill, omissionsThetaFive, omissionsGodWill,
    dnpStrictness, senseModels⟩

end TruthCore.Results.Causality.WillVersusChance
