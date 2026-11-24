module

public import TruthCore.Causality.WillVersusChance
public import TruthCore.Causality.FirstMoverNecessity
public import TruthCore.Causality.RootPositiveIntellectWill
public import TruthCore.Latin.Aquinas.DeEnte.EsseSource

/-!
# Identifying the holder of the joint-absence power with the root (#1926 phase 3)

Analyst formulations, attribution deferred (logic first). #1897
(`TruthCore.Modal.PrussPowerPremises`) and #1941
(`TruthCore.Causality.WillVersusChance`) work with the *holder*: whatever has,
at `w`, a power (`PowerFor`, DEF `bf7eddca`) for the joint absence of the
concrete beings contingent at `w` (`q = NoActualContingentConcreteIn F concrete w`).
The existing intellect routes conclude HAS_INTELLECT_1 of the *selected root*
of an actual grounding relation (`IntellectualGodCommonRootAt`, `0c27f65a`) or
of GOD_4. The missing step (#1897 note gap 2; #1941 note gap 2) is that every
holder is that root. This module types the step in two parts and keeps both
explicit:

1. **The holder is an actual root.** Initiator presence (P2′) puts every holder
   at an accessible world lacking every actual contingent concretum; with
   concreteness (P3′) the holder is therefore not contingent at `w`, and with
   existence at `w` and excluded middle it is de re necessary at `w` (law 1:
   #1897's necessity, now for *every* holder). Necessity does not by itself
   make a being underived: a necessary being can have a necessary ground
   (Avicenna's "necessary through another"). The bridge
   `NecessaryActualConcretaAreRoots` (NAR) says that it cannot.
2. **One root.** The common-root reach of `0c27f65a` (the root directly
   grounds every other actual concretum) makes every actual root that root.
   The at-most-one-root interface `49fdec01` (De ente's no-multiplication of
   beings whose esse is their essence) gives only that any two actual roots
   are the same, so it yields at most one holder, not an identification with
   a named root.

**Frames.** The holder lives in the shared `CausalityFrame`; the root in a
`Profile`. They are joined only through `FirstMoverNecessity.groundProfile F
concrete G`: the profile *on the frame's own world-relative existence*, with
the holder premises' `concrete` predicate and a selected grounding relation
`G` that is a parameter. `G` is not identified with the frame's `GivesAt`,
`CausesIn`, `DependsForBeing` or `PriorSimply` (rigor contract 5 of #1926;
#1626): no premise of this batch relates them. On the composed routes the
reused root nodes relate `G` one way to esse-causation (`cb1cdea9`) and to
simple priority (the `0c27f65a` route's priority bridge); these are explicit
open bridges there. Using one existence predicate for both
is a choice of interpretation, recorded in the note; it identifies no two
relations.

Every model is a finite structural surrogate on #1897's frames; it witnesses
only its formal interpretation, never metaphysical possibility. See
`docs/notes/holder-root-identification.md`.
-/

@[expose] public section

namespace TruthCore.Causality.HolderRootIdentification

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.ModalGrounding (NoActualContingentConcreteIn)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)

variable {W B T R : Type}

/-! ## Premises (OPEN) -/

/-- OPEN (holders exist at `w`): whatever has at `w` a power for the joint
absence of the concrete beings contingent at `w` exists at `w`. The actualist
reading of powers (serious actualism: a being has properties, powers among
them, only at worlds where it exists; Pruss's powers of actual substances,
navigation only). Restricted to this one power, the weakest form the
identification uses. -/
def ActualAbsenceHoldersExistAt (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) → F.history.ontic.ExistsAt w y

/-- OPEN (NAR, necessary actual concreta are underived): every actual concretum
at `w` that exists at every world accessible from `w` has no actual concrete
ground at `w` in the selected relation, i.e. is an actual root. The denial of
"necessary through another" for modal necessity (`NecessaryAt`, NECESSARY in the
accessible-world sense, not the tertia via's per se necessity). Its rival is a
necessary actual concretum with an actual concrete `G`-ground (note §4). The
historical Avicennian version is causal (necessitated emanation): it bears on
NAR only through the esse-cause bridge `cb1cdea9`, and its fixed giving would
need a further causing-to-giving bridge that no premise states. Constructively
equivalent to "whatever actual concretum (concrete, existing at `w`) has an
actual concrete ground at `w` is not necessary at `w`"; with excluded middle,
such a concretum is contingent at `w`. The unrestricted form (over all `x`,
not only actual concreta) is strictly stronger. -/
def NecessaryActualConcretaAreRoots (m : Profile W B) (w : W) : Prop :=
  ∀ x, ActualConcrete m w x → NecessaryAt m.ontic w x → ActualRoot m w x

/-! ## Conclusions -/

/-- Every holder at `w` of a power for the joint absence of the concrete beings
contingent at `w` is an actual root of the selected grounding relation `G`, in
the profile on the frame's existence (`groundProfile F concrete G`): concrete,
existing at `w`, with no actual concrete `G`-ground at `w`. Universal over
holders; no existence of a holder and no uniqueness. -/
def ActualAbsenceHoldersAreActualRoots (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop)
    (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) →
    ActualRoot (groundProfile F concrete G) w y

/-- At most one being has at `w` a power for the joint absence of the concrete
beings contingent at `w`: any two holders are the same. No existence. -/
def AtMostOneActualAbsenceHolder (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ y z, PowerFor w y (NoActualContingentConcreteIn F concrete w) →
    PowerFor w z (NoActualContingentConcreteIn F concrete w) → y = z

/-- Every holder at `w` of a power for the joint absence of the concrete beings
contingent at `w` is GOD_4. The converse direction of `0050b6ed` (which says
that every GOD_4 is such a holder). No existence. -/
def ActualAbsenceHoldersAreGod (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (IsGod : B → Prop)
    (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) → IsGod y

/-- Used by law 1: every holder is concrete, exists at `w` and exists at every
world accessible from `w`. -/
def ActualAbsenceHoldersNecessaryConcrete (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) →
    concrete y ∧ F.history.ontic.ExistsAt w y ∧ NecessaryAt F.history.ontic w y

/-! ## Laws and models -/

namespace Model

open TruthCore.Modal.PrussPowerPremises.Model (Bg Bg.forall_iff Bg.exists_iff gFrame theistG
  allC uni gcEx givesCHere noGiving gPower)
open TruthCore.Modal.PrussPowerPremises (GivesTo TwoWayGiverAt GivenExists
  ActualAbsenceHoldersGiveEach)
open TruthCore.Causality.WillVersusChance (AgencyFrame ActualAbsenceHolderGivesByWill
  GodsHoldActualAbsencePower RationalPowerIsWill ActualAbsenceHoldersHaveIntellect)
open TruthCore.Causality.WillVersusChance.Model (onlyG nobody simpleRational simpleChancy)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)
open TruthCore.Latin.Aquinas.DeEnte (AtMostOneActualRootAt)
open TruthCore.Modal.ModalGrounding (ActualAbsenceInitiatorPresent
  ActualAbsencePowerHoldersConcrete)
open TruthCore.Case.Catholicism (GodHasWill)

/-- General laws.

1. **Every holder is necessary.** With P2′, P3′ and holders existing at `w`, no
   holder is contingent at `w` (constructive); with excluded middle every
   holder is concrete, exists at `w` and is necessary at `w`.
2. **The dichotomy without NAR.** Add a common root of the selected relation
   (`ActualCommonRootAt`, the reach clause of `0c27f65a`): every holder is that
   root, or a necessary actual concretum directly grounded by it ("necessary
   through another"). NAR excludes exactly the second horn.
3. **NAR and the common root identify.** With NAR, P2′, P3′, holders at `w`
   and excluded middle, a common root is the only holder candidate: every
   holder equals it. -/
def Laws : Prop :=
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
      (concrete : B → Prop) (w : W),
    ActualAbsenceInitiatorPresent F PowerFor concrete w →
    ActualAbsencePowerHoldersConcrete F PowerFor concrete w →
    ActualAbsenceHoldersExistAt F PowerFor concrete w →
    (∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) →
        ¬ ContingentAt F.history.ontic w y) ∧
      (TruthCore.Logic.ExcludedMiddle →
        ActualAbsenceHoldersNecessaryConcrete F PowerFor concrete w)) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
      (concrete : B → Prop) (G : W → B → B → Prop) (w : W),
    TruthCore.Logic.ExcludedMiddle →
    ActualAbsenceInitiatorPresent F PowerFor concrete w →
    ActualAbsencePowerHoldersConcrete F PowerFor concrete w →
    ActualAbsenceHoldersExistAt F PowerFor concrete w →
    ActualCommonRootAt (groundProfile F concrete G) w →
    ∃ n, ActualRoot (groundProfile F concrete G) w n ∧
      ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) →
        y = n ∨ (ActualConcreteGround (groundProfile F concrete G) w n y ∧
          NecessaryAt F.history.ontic w y)) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
      (concrete : B → Prop) (G : W → B → B → Prop) (w : W),
    TruthCore.Logic.ExcludedMiddle →
    ActualAbsenceInitiatorPresent F PowerFor concrete w →
    ActualAbsencePowerHoldersConcrete F PowerFor concrete w →
    ActualAbsenceHoldersExistAt F PowerFor concrete w →
    NecessaryActualConcretaAreRoots (groundProfile F concrete G) w →
    ActualCommonRootAt (groundProfile F concrete G) w →
    ∃ n, ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) → y = n)

/-! ### Frames on #1897's three candidates (`Bg`: `g`, `c`, `d`; actual world `false`) -/

/-- `g` and `d` at both worlds; `c` only at the actual world `false`. -/
def gdEx (v : Bool) (x : Bg) : Prop := x = .g ∨ x = .d ∨ (x = .c ∧ v = false)

/-- `g` at both worlds; `c` only at `false`; `d` only at `true`. -/
def dThereEx (v : Bool) (x : Bg) : Prop := x = .g ∨ (x = .c ∧ v = false) ∨ (x = .d ∧ v = true)

/-- `d` gives `c` being at `false` only. -/
def dGivesCHere (v : Bool) (y x : Bg) : Prop := y = .d ∧ x = .c ∧ v = false

/-- Necessary `g` and `d`, contingent `c`; nothing gives anything. -/
def gdG : CausalityFrame Bool Bg Unit Bool := gFrame uni gdEx noGiving

/-- Necessary `g` and `d`, contingent `c`; `d` gives `c` being at `false` and
withholds it at `true`. -/
def gdWithholdG : CausalityFrame Bool Bg Unit Bool := gFrame uni gdEx dGivesCHere

/-- `g` necessary, `c` actual and contingent, `d` only at the non-actual world. -/
def dThereG : CausalityFrame Bool Bg Unit Bool := gFrame uni dThereEx noGiving

/-- `g` grounds every other being, at every world. -/
def gGroundsOthers (_ : Bool) (y x : Bg) : Prop := y = .g ∧ x ≠ .g

/-- `g` and `d` each ground `c`, at every world; nothing grounds `g` or `d`. -/
def bothGroundC (_ : Bool) (y x : Bg) : Prop := y ≠ .c ∧ x = .c

/-- `d` holds every power. -/
def dPower (_ : Bool) (y : Bg) (_ : Bool → Prop) : Prop := y = .d

/-- `c` holds every power. -/
def cPower (_ : Bool) (y : Bg) (_ : Bool → Prop) : Prop := y = .c

/-- `g` and `d` hold every power. -/
def gdPower (_ : Bool) (y : Bg) (_ : Bool → Prop) : Prop := y ≠ .c

/-- Everything but `d` is concrete. -/
def notD (x : Bg) : Prop := x ≠ .d

/-- Only `d` (the will slot of the two-holder model). -/
def onlyD (x : Bg) : Prop := x = .d

/-- Only `c` (a GOD_4 slot that holds no power). -/
def onlyC (x : Bg) : Prop := x = .c

/-- `d` alone has one constant state and one rational power, exercised in all of
`d`'s giving; no external conditions. -/
def dRational : AgencyFrame Bool Bg Unit Unit where
  StateAt := fun _ y _ => y = .d
  ConditionOf := fun _ _ _ => False
  PowerOf := fun y _ => y = .d
  Rational := fun _ => True
  Exercises := fun _ y _ _ => y = .d

/-- **Theist nonvacuity** (`theistG`, `gPower`, `g` grounds every other being,
`g` is GOD_4 with intellect and will; actual world `false`): every premise and
conclusion of arguments 1–5 holds. -/
def TheistNonvacuity : Prop :=
  TruthCore.Logic.ExcludedMiddle ∧
  ActualAbsenceInitiatorPresent theistG gPower allC false ∧
  ActualAbsencePowerHoldersConcrete theistG gPower allC false ∧
  ActualAbsenceHoldersExistAt theistG gPower allC false ∧
  NecessaryActualConcretaAreRoots (groundProfile theistG allC gGroundsOthers) false ∧
  ActualAbsenceHoldersAreActualRoots theistG gPower allC gGroundsOthers false ∧
  IntellectualGodCommonRootAt (groundProfile theistG allC gGroundsOthers) false onlyG onlyG ∧
  AtMostOneActualRootAt (groundProfile theistG allC gGroundsOthers) false ∧
  ActualAbsenceHoldersHaveIntellect theistG gPower allC onlyG false ∧
  ActualAbsenceHoldersAreGod theistG gPower allC onlyG false ∧
  AtMostOneActualAbsenceHolder theistG gPower allC false ∧
  ActualAbsenceHolderGivesByWill theistG simpleRational gPower allC false ∧
  GodsHoldActualAbsencePower theistG gPower allC onlyG false ∧
  RationalPowerIsWill simpleRational onlyG ∧
  GodHasWill onlyG onlyG

/-- **The necessary-through-another holder** (`gdWithholdG`, `dPower`, `g`
grounds every other being, GOD_4 and intellect at `g` only): the omission model
of NAR. `d` is the only holder; it is necessary and grounded by `g`, gives `c`
being at `false` and withholds it at `true` (a two-way giver, satisfying #1897's
creator reading and factive giving). Excluded middle, P2′, P3′, holders at `w`,
the common GOD_4 root with intellect (`0c27f65a`) and at most one actual root
(`49fdec01`) all hold; NAR fails, and every holder conclusion fails: `d` is not
an actual root, has no intellect, is not GOD_4. So in this interpretation the
two uniqueness premises do not yield the identification without the holder
being a root. Encoding: `G` is the same at both worlds, the `Ontic` causal
field is empty, and `d` holds every power; the model shows a non-entailment,
not that an emanation scheme is coherent or true. -/
def NecessaryThroughAnother : Prop :=
  TruthCore.Logic.ExcludedMiddle ∧
  ActualAbsenceInitiatorPresent gdWithholdG dPower allC false ∧
  ActualAbsencePowerHoldersConcrete gdWithholdG dPower allC false ∧
  ActualAbsenceHoldersExistAt gdWithholdG dPower allC false ∧
  ActualAbsenceHoldersGiveEach gdWithholdG dPower allC false ∧ GivenExists gdWithholdG ∧
  TwoWayGiverAt gdWithholdG false .d ∧
  IntellectualGodCommonRootAt (groundProfile gdWithholdG allC gGroundsOthers) false onlyG onlyG ∧
  AtMostOneActualRootAt (groundProfile gdWithholdG allC gGroundsOthers) false ∧
  ¬ NecessaryActualConcretaAreRoots (groundProfile gdWithholdG allC gGroundsOthers) false ∧
  ¬ ActualAbsenceHoldersAreActualRoots gdWithholdG dPower allC gGroundsOthers false ∧
  ¬ ActualAbsenceHoldersHaveIntellect gdWithholdG dPower allC onlyG false ∧
  ¬ ActualAbsenceHoldersAreGod gdWithholdG dPower allC onlyG false

/-- **Omission models of argument 1** (holders are actual roots; `g` grounds
every other being, actual world `false`):

1. without holders at `w` (`dThereG`, `dPower`): the holder `d` exists only at
   the non-actual world, where `c` is absent;
2. without P2′ (`theistG`, `cPower`): the holder is the contingent `c`;
3. without P3′ (`gdG`, `dPower`, `d` not concrete): a necessary non-concrete
   holder;
4. without NAR: `NecessaryThroughAnother`. -/
def OmissionsHolderRoot : Prop :=
  (ActualAbsenceInitiatorPresent dThereG dPower allC false ∧
    ActualAbsencePowerHoldersConcrete dThereG dPower allC false ∧
    NecessaryActualConcretaAreRoots (groundProfile dThereG allC gGroundsOthers) false ∧
    ¬ ActualAbsenceHoldersExistAt dThereG dPower allC false ∧
    ¬ ActualAbsenceHoldersAreActualRoots dThereG dPower allC gGroundsOthers false) ∧
  (ActualAbsencePowerHoldersConcrete theistG cPower allC false ∧
    ActualAbsenceHoldersExistAt theistG cPower allC false ∧
    NecessaryActualConcretaAreRoots (groundProfile theistG allC gGroundsOthers) false ∧
    ¬ ActualAbsenceInitiatorPresent theistG cPower allC false ∧
    ¬ ActualAbsenceHoldersAreActualRoots theistG cPower allC gGroundsOthers false) ∧
  (ActualAbsenceInitiatorPresent gdG dPower notD false ∧
    ActualAbsenceHoldersExistAt gdG dPower notD false ∧
    NecessaryActualConcretaAreRoots (groundProfile gdG notD gGroundsOthers) false ∧
    ¬ ActualAbsencePowerHoldersConcrete gdG dPower notD false ∧
    ¬ ActualAbsenceHoldersAreActualRoots gdG dPower notD gGroundsOthers false)

/-- **Two roots** (`gdG`, `gdPower`, `g` and `d` each ground `c`; GOD_4 and
intellect at `g` only): both holders are actual roots, so argument 1's
conclusion holds; at most one root (`49fdec01`) and the common GOD_4 root
(`0c27f65a`) fail, and so do at most one holder, every holder having intellect
and every holder being GOD_4. The omission model of the uniqueness premise of
arguments 2–4. A structural surrogate of two necessary underived sources
(primitive thisness, note §5). -/
def TwoRoots : Prop :=
  ActualAbsenceHoldersAreActualRoots gdG gdPower allC bothGroundC false ∧
  ¬ AtMostOneActualRootAt (groundProfile gdG allC bothGroundC) false ∧
  ¬ IntellectualGodCommonRootAt (groundProfile gdG allC bothGroundC) false onlyG onlyG ∧
  ¬ AtMostOneActualAbsenceHolder gdG gdPower allC false ∧
  ¬ ActualAbsenceHoldersHaveIntellect gdG gdPower allC onlyG false ∧
  ¬ ActualAbsenceHoldersAreGod gdG gdPower allC onlyG false

/-- **A root holder beside a derived holder** (`gdG`, `gdPower`, `g` grounds
every other being): `g` and `d` both hold the power; `g` is the only actual
root, so at most one root (`49fdec01`) holds, while argument 1's conclusion
fails at `d` and so does at most one holder. The omission model of argument 1's
conclusion in argument 4. -/
def RootBesideDerivedHolder : Prop :=
  AtMostOneActualRootAt (groundProfile gdG allC gGroundsOthers) false ∧
  ¬ ActualAbsenceHoldersAreActualRoots gdG gdPower allC gGroundsOthers false ∧
  ¬ AtMostOneActualAbsenceHolder gdG gdPower allC false

/-- **Omission models of argument 5** (GOD_4 has will from the willed holder;
actual world `false`):

1. without at most one holder (`gdWithholdG`, `dRational`, `gdPower`): `d` is a
   willed holder with will, `g` is a GOD_4 holder without will;
2. without the rational-power bridge (`theistG`, `simpleRational`, will for
   nobody);
3. without the GOD_4 bridge `0050b6ed` (`theistG`, `simpleRational`, GOD_4 at
   `c`, which holds no power, will at `g`);
4. without the willed holder `fdd2b1cf`: the chance rival of #1941 (`theistG`,
   `simpleChancy`, will for nobody). -/
def OmissionsGodWill : Prop :=
  (ActualAbsenceHolderGivesByWill gdWithholdG dRational gdPower allC false ∧
    GodsHoldActualAbsencePower gdWithholdG gdPower allC onlyG false ∧
    RationalPowerIsWill dRational onlyD ∧
    ¬ AtMostOneActualAbsenceHolder gdWithholdG gdPower allC false ∧
    ¬ GodHasWill onlyG onlyD) ∧
  (ActualAbsenceHolderGivesByWill theistG simpleRational gPower allC false ∧
    GodsHoldActualAbsencePower theistG gPower allC onlyG false ∧
    AtMostOneActualAbsenceHolder theistG gPower allC false ∧
    ¬ RationalPowerIsWill simpleRational nobody ∧ ¬ GodHasWill onlyG nobody) ∧
  (ActualAbsenceHolderGivesByWill theistG simpleRational gPower allC false ∧
    AtMostOneActualAbsenceHolder theistG gPower allC false ∧
    RationalPowerIsWill simpleRational onlyG ∧
    ¬ GodsHoldActualAbsencePower theistG gPower allC onlyC false ∧ ¬ GodHasWill onlyC onlyG) ∧
  (GodsHoldActualAbsencePower theistG gPower allC onlyG false ∧
    AtMostOneActualAbsenceHolder theistG gPower allC false ∧
    RationalPowerIsWill simpleChancy nobody ∧
    ¬ ActualAbsenceHolderGivesByWill theistG simpleChancy gPower allC false ∧
    ¬ GodHasWill onlyG nobody)

/-- The certificate: laws and models. -/
def Controls : Prop :=
  Laws ∧ TheistNonvacuity ∧ NecessaryThroughAnother ∧ OmissionsHolderRoot ∧ TwoRoots ∧
    RootBesideDerivedHolder ∧ OmissionsGodWill

end Model

end TruthCore.Causality.HolderRootIdentification
