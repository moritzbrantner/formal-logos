module

public import TruthCore.Modal.ModalGrounding
public import TruthCore.Modal.Kripke

/-!
# The power premises of the route with Pruss's own premise (#1887, continued)

Analyst formulations, attribution deferred (logic first). This module studies
the grounding premise P1′ (`ModalGrounding.ActualAbsenceGrounded`, statement
`95bf8780`) of the route `prussActualAbsenceNecessaryPowerHolder` (`42da6b2d`):
some being at `w` has a power (`PowerFor`, DEF `bf7eddca`) for the joint
absence of the concrete beings contingent at `w`. Three questions:

1. **Transfer.** Does that collective power give a power over each such
   being's esse (POWER_OVER_ESSE_1, `PowerOverEsse`)? The collective/distributive
   split is the one of disambiguation `197f0097` (C1, #1882), transposed from a
   cause of a totality to a power for a totality's absence; the transfer is the
   analogue of C1's premise B (whole to members).
2. **Powers to abstain.** Is a power whose outcome obtains by the holder's not
   giving being an Aristotelian power, and of which kind? One-way and two-way
   exercise are typed *extensionally* on the frame's world-relative giving
   field `GivesAt` (DEF `158301bc`), not as intensional potencies.
3. **Pruss's own direction**: a power, held in a world lacking the actual
   contingents, for the actual world's obtaining.

Sources read for this slice (2026-11-23), navigation for the analyst
formulations below, no claim record: ST I q.104 a.3 co. and ad 1, ad 3 (New
Advent, https://www.newadvent.org/summa/1104.htm); Aristotle, *Metaphysics* Θ.2
(1046b) and Θ.5 (1048a), Ross translation (http://classics.mit.edu/Aristotle/metaphysics.9.ix.html);
A. Pruss, "The Actual and the Possible", sections "An Aristotelian alternative"
and "A combined account" (http://alexanderpruss.com/papers/ActualAndPossible.html).

**Relation to existing work.** `FixedGiver` is the frame/`GivesAt` analogue of
#555's `BeingCarriesAct` reading (one act wherever the bearer exists); the
collapse law here corresponds to #555 `Core` and #462's `fixedEffects`.
#435/#462 already show a necessary source with varying causal activity is
consistent (on `Ontic.Causes`, a different relation).

Every new relation is defined from frame fields and the existing primitives
`PowerFor` and `PowerOver`; no new primitive is introduced. Models in the
Solution are finite structural surrogates, never certificates of metaphysical
possibility.
-/

@[expose] public section

namespace TruthCore.Modal.PrussPowerPremises

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Causality.ContingencyGrounding (PowerOverEsse)
open TruthCore.Modal.ModalGrounding

variable {W B T R : Type}

/-! ## Giving being, and one-way and two-way exercise -/

/-- `GivesTo F v y x`: in world `v`, `y` exercises causation of `x`'s being at
some moment (`∃ t, F.GivesAt v y x t`, the frame's primitive of DEF `158301bc`).
Weaker than both CAUSE_OF_BEING senses of disambiguation `88a8fba7`
(originating, sustaining), each of which implies it for a thing with a moment of
presence. It is an *exercise*, world by world; the frame's `CausesIn` is
tenseless and world-independent. -/
def GivesTo (F : CausalityFrame W B T R) (v : W) (y x : B) : Prop :=
  ∃ t, F.GivesAt v y x t

/-- `y` gives being to exactly the same beings in worlds `u` and `v`. -/
def GivingSameIn (F : CausalityFrame W B T R) (y : B) (u v : W) : Prop :=
  ∀ x, GivesTo F u y x ↔ GivesTo F v y x

/-- ONE-WAY exercise profile (extensional): wherever `y` exists, it gives being
to the same beings. Intended reading: Met. Θ.5's rule for a non-rational power
("when the agent and the patient meet ... the one must act"), for a holder
whose exercise needs no patient, so that its conditions are present wherever it
is; Θ.2: "the hot is capable only of heating". Examples: a necessary emanative
source that produces the same effects in every world where it is; an inert
being (it gives nothing anywhere). Non-examples: a craftsman who builds in one
world and not in another; a source whose output varies by chance. Being a fixed
giver is a property of the exercise pattern, not of an intensional potency: a
one-way power whose exercise depends on a varying external patient is *not* a
fixed giver, which is why the patientless condition is part of the reading. -/
def FixedGiver (F : CausalityFrame W B T R) (y : B) : Prop :=
  ∀ u v, F.history.ontic.ExistsAt u y → F.history.ontic.ExistsAt v y → GivingSameIn F y u v

/-- `y` exists at `w` and, at some world accessible from `w` where it also
exists, gives being to different beings than at `w` (by giving more, less or
otherwise). The extensional signature of an exercise not fixed by the holder's
existence. A fixed giver never has it. -/
def GivingVariesAt (F : CausalityFrame W B T R) (w : W) (y : B) : Prop :=
  F.history.ontic.ExistsAt w y ∧ ∃ v, F.history.ontic.frame.access w v ∧
    F.history.ontic.ExistsAt v y ∧ ¬ GivingSameIn F y w v

/-- TWO-WAY giving profile, withholding form (extensional): `y` exists at `w`,
gives being to some `x` at `w`, and at a world accessible from `w` where `y`
also exists, does not give being to `x`. Θ.2's "capable of contrary effects"
(giving `x` being and not giving it), read on world-relative exercise. Example:
on the Thomist account, God giving a creature being and being "free not to
continue their existence" (q.104 a.3 co., navigation). Non-examples: a fixed
giver; a being that gives `x` being only in worlds where it alone exists (no
world with the holder and without the giving). It does not say what decides
the difference (choice, chance or an external condition). -/
def TwoWayGiverAt (F : CausalityFrame W B T R) (w : W) (y : B) : Prop :=
  F.history.ontic.ExistsAt w y ∧ ∃ x v, F.history.ontic.frame.access w v ∧
    F.history.ontic.ExistsAt v y ∧ GivesTo F w y x ∧ ¬ GivesTo F v y x

/-- OPEN bridge between two frame fields (factivity of giving): whatever is
given being in a world exists in that world. The frame relates no fields, so it
is stated. -/
def GivenExists (F : CausalityFrame W B T R) : Prop :=
  ∀ v y x, GivesTo F v y x → F.history.ontic.ExistsAt v x

/-! ## Premises about the power for the actual contingents' joint absence

Throughout, `q` is `NoActualContingentConcreteIn F concrete w`: every concrete
being contingent at `w` is absent. -/

/-- OPEN (P2δ, initiator presence with a difference in giving): whatever has at
`w` a power for `q` can exercise it so that `q` obtains at an accessible world
where the holder exists *and gives being otherwise than at `w`*. It strengthens
P2′ (`906f5c39`): the exercise of a power for an outcome about existence shows
in what the holder gives. It does not say whether the difference is a giving of
something new (replacement) or a withholding. -/
def ActualAbsenceExerciseDiffers (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) →
    ∃ v, F.history.ontic.frame.access w v ∧ NoActualContingentConcreteIn F concrete w v ∧
      F.history.ontic.ExistsAt v y ∧ ¬ GivingSameIn F y w v

/-- OPEN (the holder gives being to each actual contingent concretum): whatever
has at `w` a power for `q` gives being, at `w`, to every concrete being
contingent at `w`. The creator/conserver reading of the holder (q.104 a.3 co.:
God preserves things "by continually pouring out existence into them",
navigation). Not sole giving, not immediacy. -/
def ActualAbsenceHoldersGiveEach (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) →
    ∀ x, concrete x → ContingentAt F.history.ontic w x → GivesTo F w y x

/-- OPEN transfer bridge for Pruss's own premise (collective to distributive):
whatever has at `w` a power for `q` has POWER_OVER_ESSE_1 over each concrete
being contingent at `w`. The analogue of the global variant's
`GlobalAbsencePowerIsPowerOverEsse` and of C1's premise B (disambiguation
`197f0097`: what accounts for a totality accounts for each member). -/
def ActualAbsencePowerIsPowerOverEsse (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (PowerOver : B → B → R → Prop)
    (concrete : B → Prop) (w : W) : Prop :=
  ∀ y x, PowerFor w y (NoActualContingentConcreteIn F concrete w) → concrete x →
    ContingentAt F.history.ontic w x → PowerOverEsse F PowerOver y x

/-- OPEN (withholdable giving is power over esse): a being that gives `x` being
at `w` and, existing at an accessible world, does not give it there has
POWER_OVER_ESSE_1 over `x` (it can unmake `x`'s being by withholding). The
q.104 a.3 co. structure ("just as ... God was free not to give them existence
..., so after they are made, He is free not to continue their existence";
navigation), stated without freedom. A necessitated giver is not covered: the
antecedent requires an actual withholding world. -/
def WithheldGivingIsPowerOverEsse (F : CausalityFrame W B T R)
    (PowerOver : B → B → R → Prop) (w : W) : Prop :=
  ∀ y x v, GivesTo F w y x → F.history.ontic.frame.access w v → F.history.ontic.ExistsAt v y →
    ¬ GivesTo F v y x → PowerOverEsse F PowerOver y x

/-! ## Conclusions -/

/-- Some being at `w` has a power for `q` and POWER_OVER_ESSE_1 over each
concrete being contingent at `w` (the distributive powers, one holder). -/
def SomeHolderHasPowerOverEachActualContingent (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (PowerOver : B → B → R → Prop)
    (concrete : B → Prop) (w : W) : Prop :=
  ∃ y, F.history.ontic.ExistsAt w y ∧ PowerFor w y (NoActualContingentConcreteIn F concrete w) ∧
    ∀ x, concrete x → ContingentAt F.history.ontic w x → PowerOverEsse F PowerOver y x

/-- Some concrete being exists at `w`, exists at every world accessible from
`w`, has at `w` a power for `q`, and gives being otherwise at some accessible
world where it exists than at `w` (`GivingVariesAt`). Nothing is said about
what decides the variation. -/
def NecessaryVaryingGiverWithActualAbsencePower (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∃ y, concrete y ∧ F.history.ontic.ExistsAt w y ∧ NecessaryAt F.history.ontic w y ∧
    PowerFor w y (NoActualContingentConcreteIn F concrete w) ∧ GivingVariesAt F w y

/-- The joint absence realized by withholding: some being at `w` with a power
for `q` exists at an accessible world where `q` holds, and gives being at `w`
to every concrete being contingent at `w` while giving none of them being
there. -/
def ActualAbsenceByWithholding (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∃ y, F.history.ontic.ExistsAt w y ∧ PowerFor w y (NoActualContingentConcreteIn F concrete w) ∧
    ∃ v, F.history.ontic.frame.access w v ∧ NoActualContingentConcreteIn F concrete w v ∧
      F.history.ontic.ExistsAt v y ∧
      ∀ x, concrete x → ContingentAt F.history.ontic w x → GivesTo F w y x ∧ ¬ GivesTo F v y x

/-! ## Pruss's own direction

Pruss ("A combined account"): with `w1` a world in which no member of the set
`S` of actual contingent beings exists, "it is then true at w1 (technically, by
the axiom S5 of modal logic) that it might have been that w0 was actual. Then,
by the Aristotelian account, there is a substance x in w1 which could have
initiated a causal chain that could lead to w0 being actual." The proposition
"`w` obtains" is `fun u => u = w`. -/

/-- OPEN (grounding at the absence worlds): at every world accessible from `w`
that lacks every actual contingent concretum, Aristotelian grounding holds for
the proposition that `w` obtains. The grounding principle applied at a
non-actual world. -/
def ActualityGroundedAtAbsenceWorlds (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ v, F.history.ontic.frame.access w v → NoActualContingentConcreteIn F concrete w v →
    AristotelianGroundingFor F PowerFor v (fun u => u = w)

/-- OPEN (initiator presence at the absence worlds): a power, held at such a
world, for `w`'s obtaining issues in an accessible world where it obtains and
the holder exists (Pruss: "x cannot start any chain of causes that can lead to
actuality's not including x"). -/
def ActualityInitiatorPresentAtAbsenceWorlds (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ v, F.history.ontic.frame.access w v → NoActualContingentConcreteIn F concrete w v →
    InitiatorPresentFor F PowerFor v (fun u => u = w)

/-- OPEN: holders, at such a world, of a power for `w`'s obtaining are
concrete. -/
def ActualityPowerHoldersConcreteAtAbsenceWorlds (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ v, F.history.ontic.frame.access w v → NoActualContingentConcreteIn F concrete w v →
    PowerHoldersConcreteFor PowerFor concrete v (fun u => u = w)

/-- Conclusion of Pruss's direction: some concrete being exists at `w`, exists
at every world accessible from `w`, and exists at an accessible world lacking
every actual contingent concretum, where it has a power for `w`'s obtaining. -/
def NecessaryConcreteHolderOfActualityPower (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∃ y v, concrete y ∧ F.history.ontic.ExistsAt w y ∧ NecessaryAt F.history.ontic w y ∧
    F.history.ontic.frame.access w v ∧ NoActualContingentConcreteIn F concrete w v ∧
    F.history.ontic.ExistsAt v y ∧ PowerFor v y (fun u => u = w)

/-! ## The distributive reading of P1′ (controls only) -/

/-- Distributive grounding with varying holders: the possible absence of each
concrete being contingent at `w` is grounded in some being at `w` with a power
for that one being's absence. -/
def EachActualAbsenceGrounded (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ x, concrete x → ContingentAt F.history.ontic w x →
    ∃ y, F.history.ontic.ExistsAt w y ∧ PowerFor w y (fun u => ¬ F.history.ontic.ExistsAt u x)

/-- Initiator presence for each such power. -/
def EachActualAbsenceInitiatorPresent (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ x y, concrete x → ContingentAt F.history.ontic w x →
    PowerFor w y (fun u => ¬ F.history.ontic.ExistsAt u x) →
    ∃ v, F.history.ontic.frame.access w v ∧ ¬ F.history.ontic.ExistsAt v x ∧
      F.history.ontic.ExistsAt v y

/-! ## Finite surrogate frames -/

namespace Model

/-- Three rigid candidates: a holder `g` and two others `c`, `d`. -/
inductive Bg
  | g
  | c
  | d
  deriving DecidableEq

theorem Bg.forall_iff (p : Bg → Prop) : (∀ x, p x) ↔ p .g ∧ p .c ∧ p .d :=
  ⟨fun h => ⟨h _, h _, h _⟩, fun ⟨hg, hc, hd⟩ x => by cases x <;> assumption⟩

theorem Bg.exists_iff (p : Bg → Prop) : (∃ x, p x) ↔ p .g ∨ p .c ∨ p .d :=
  ⟨fun ⟨x, h⟩ => by cases x <;> simp_all, fun h => by
    rcases h with h | h | h <;> exact ⟨_, h⟩⟩

/-- A frame with stated accessibility, existence and world-relative giving; every
other field is empty. -/
def gFrame {W : Type} (acc : W → W → Prop) (ex : W → Bg → Prop) (gives : W → Bg → Bg → Prop) :
    CausalityFrame W Bg Unit Bool where
  history := ⟨⟨⟨acc⟩, ex, fun _ _ _ => False⟩, fun _ _ _ => False, ()⟩
  GivesAt := fun v y x _ => gives v y x
  CausesIn := fun _ _ _ => False
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := true

/-- Every candidate is concrete. -/
def allC (_ : Bg) : Prop := True

/-- Only `c` and `d` are concrete (`g` a non-concrete holder). -/
def onlyCD (x : Bg) : Prop := x ≠ .g

/-- Universal access on `Bool`. -/
def uni (_ _ : Bool) : Prop := True

/-- Access only from `false` to `true` and from each world to itself. -/
def forwardOnly (u v : Bool) : Prop := u = v ∨ (u = false ∧ v = true)

/-- `g` everywhere; `c` only at the actual world `false`. -/
def gcEx (v : Bool) (x : Bg) : Prop := x = .g ∨ (x = .c ∧ v = false)

/-- `g` and `c` everywhere. -/
def gcAlways (_ : Bool) (x : Bg) : Prop := x = .g ∨ x = .c

/-- `g` everywhere; `c` only at `false`; `d` only at `true` (replacement). -/
def replEx (v : Bool) (x : Bg) : Prop :=
  x = .g ∨ (x = .c ∧ v = false) ∨ (x = .d ∧ v = true)

/-- `g` only at `true`; `c` only at `false`. -/
def gOnlyThereEx (v : Bool) (x : Bg) : Prop := (x = .g ∧ v = true) ∨ (x = .c ∧ v = false)

/-- `g` gives `c` being at `false` only. -/
def givesCHere (v : Bool) (y x : Bg) : Prop := y = .g ∧ x = .c ∧ v = false

/-- `g` gives `c` being at both worlds (giving not factive at `true` in `gcEx`). -/
def givesCAlways (_ : Bool) (y x : Bg) : Prop := y = .g ∧ x = .c

/-- `g` gives `d` being at `true` only. -/
def givesDThere (v : Bool) (y x : Bg) : Prop := y = .g ∧ x = .d ∧ v = true

/-- Nobody gives anything. -/
def noGiving {W : Type} (_ : W) (_ _ : Bg) : Prop := False

/-- `g` holds every power. -/
def gPower {W : Type} (_ : W) (y : Bg) (_ : W → Prop) : Prop := y = .g

/-- `g` holds every power at `true` only. -/
def gPowerThere (u : Bool) (y : Bg) (_ : Bool → Prop) : Prop := y = .g ∧ u = true

/-- No powers. -/
def noPower {W : Type} (_ : W) (_ : Bg) (_ : W → Prop) : Prop := False

/-- Positive-outcome-only powers: `g` has a power for `p` at `u` only if every
world where `p` holds is one where `g` gives something. -/
def positivePower {W : Type} (gives : W → Bg → Bg → Prop) (_ : W) (y : Bg) (p : W → Prop) :
    Prop :=
  y = .g ∧ ∀ v, p v → ∃ x, gives v .g x

/-- `g` has power over the esse of `c`. -/
def gOverC (y x : Bg) (_ : Bool) : Prop := y = .g ∧ x = .c

/-- `g` has power over the esse of `c` and of `d`. -/
def gOverCD (y x : Bg) (_ : Bool) : Prop := y = .g ∧ x ≠ .g

/-- No power over anything. -/
def noOver (_ _ : Bg) (_ : Bool) : Prop := False

/-- The classical-theist surrogate: a necessary `g` gives `c` being at the
actual world `false` and withholds it at `true`; universal access. -/
def theistG : CausalityFrame Bool Bg Unit Bool := gFrame uni gcEx givesCHere

/-- Giving not factive: `g` gives `c` at `true` too, where `c` is absent. -/
def nonFactiveG : CausalityFrame Bool Bg Unit Bool := gFrame uni gcEx givesCAlways

/-- Replacement: `c` brute at `false`, `g` gives `d` being at `true`. -/
def replacementG : CausalityFrame Bool Bg Unit Bool := gFrame uni replEx givesDThere

/-- An inert necessary `g` and a contingent `c`; nothing gives anything. -/
def inertG : CausalityFrame Bool Bg Unit Bool := gFrame uni gcEx noGiving

/-- A necessitated source: `g` gives `c` being at both worlds; both everywhere. -/
def necessitarianG : CausalityFrame Bool Bg Unit Bool := gFrame uni gcAlways givesCAlways

/-- The theist profile with access only forward: `true` does not access `false`. -/
def forwardG : CausalityFrame Bool Bg Unit Bool := gFrame forwardOnly gcEx givesCHere

/-- `g` only at the absence world `true`. -/
def absentHolderG : CausalityFrame Bool Bg Unit Bool := gFrame uni gOnlyThereEx noGiving

/-- Worlds for two beings: `(c exists, d exists)`. -/
def pairEx (v : Bool × Bool) (x : Bg) : Prop := (x = .c ∧ v.1 = true) ∨ (x = .d ∧ v.2 = true)

/-- Mutual annihilators: `c` and `d`, each possibly absent, also jointly; no `g`. -/
def mutualG : CausalityFrame (Bool × Bool) Bg Unit Bool :=
  gFrame (fun _ _ => True) pairEx noGiving

/-- `c` has a power for the absence of `d` and `d` one for the absence of `c`:
a power for exactly the absence of a distinct one of the two. -/
def annihilatorPower (_ : Bool × Bool) (y : Bg) (p : Bool × Bool → Prop) : Prop :=
  (y = .c ∧ ∀ v, p v ↔ ¬ pairEx v .d) ∨ (y = .d ∧ ∀ v, p v ↔ ¬ pairEx v .c)

/-- Three worlds for Van Cleve's point with a holder: `g` everywhere; at `a`
both `c` and `d`, at `b` only `c`, at `z` only `d`. -/
inductive V3
  | a
  | b
  | z
  deriving DecidableEq

theorem V3.forall_iff (p : V3 → Prop) : (∀ v, p v) ↔ p .a ∧ p .b ∧ p .z :=
  ⟨fun h => ⟨h _, h _, h _⟩, fun ⟨ha, hb, hz⟩ v => by cases v <;> assumption⟩

theorem V3.exists_iff (p : V3 → Prop) : (∃ v, p v) ↔ p .a ∨ p .b ∨ p .z :=
  ⟨fun ⟨v, h⟩ => by cases v <;> simp_all, fun h => by
    rcases h with h | h | h <;> exact ⟨_, h⟩⟩

/-- Existence for the Van Cleve frame with a holder. -/
def vcEx (v : V3) (x : Bg) : Prop :=
  x = .g ∨ (x = .c ∧ v ≠ .z) ∨ (x = .d ∧ v ≠ .b)

/-- `g` gives each of `c` and `d` being wherever it exists. -/
def vcGives (v : V3) (y x : Bg) : Prop := y = .g ∧ vcEx v x ∧ x ≠ .g

/-- Van Cleve's frame with a giving holder. -/
def vanCleveG : CausalityFrame V3 Bg Unit Bool := gFrame (fun _ _ => True) vcEx vcGives

/-- General laws.
1. One-way exclusion: a fixed giver existing at `w` has no power for `q`
   satisfying P2δ.
2. With P1′, P2δ, P4′ and P5, not every being at `w` is a fixed giver.
3. Collapse: a fixed giver existing at `w` and necessary at `w`, with factive
   giving, gives being at `w` only to beings necessary at `w`.
4. Necessary non-rational sources: if every concrete being contingent at `w` is
   given being at `w` by some fixed giver necessary at `w` (one or an
   aggregate), with factive giving, no concrete being is contingent at `w`.
5. Under the creator reading, P2′ gives P2δ: holders that give each actual
   contingent concretum being, factive giving, P2′ and P5 give P2δ.
6. Withholding is two-way giving: `ActualAbsenceByWithholding` with P5 gives a
   being with `TwoWayGiverAt`; two-way giving implies varying giving, which no
   fixed giver has.
7. Pruss's direction relocates the abstention: a being existing at `w` and at
   an accessible world lacking the actual contingent concreta, that gives one of
   them being at `w`, is (with factive giving) a two-way giver at `w`.
8. The joint one (C1's lesson): a concrete being existing at `w` that, for each
   concrete being contingent at `w`, exists at an accessible world lacking it, is
   (with excluded middle) necessary at `w`. No joint-absence premise is used.
9. The transfer's conclusion reproduces PGP's verdict: with excluded middle,
   `SomeHolderHasPowerOverEachActualContingent` makes every concrete
   foundational being at `w` necessary at `w`. No Euclidean premise. -/
def Laws : Prop :=
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (concrete : B → Prop) (w : W) (y : B),
    ActualAbsenceExerciseDiffers F PowerFor concrete w →
    PowerFor w y (NoActualContingentConcreteIn F concrete w) →
    F.history.ontic.ExistsAt w y → ¬ FixedGiver F y) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (concrete : B → Prop) (w : W),
    ActualAbsenceGrounded F PowerFor concrete w →
    ActualAbsenceExerciseDiffers F PowerFor concrete w →
    PossiblyNoActualContingentConcrete F concrete w →
    SomeContingentConcreteAt F concrete w →
    ¬ ∀ y, F.history.ontic.ExistsAt w y → FixedGiver F y) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (y : B),
    GivenExists F → F.history.ontic.ExistsAt w y → NecessaryAt F.history.ontic w y →
    FixedGiver F y → ∀ x, GivesTo F w y x → NecessaryAt F.history.ontic w x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (concrete : B → Prop) (w : W),
    GivenExists F →
    (∀ x, concrete x → ContingentAt F.history.ontic w x → ∃ y,
      F.history.ontic.ExistsAt w y ∧ NecessaryAt F.history.ontic w y ∧ FixedGiver F y ∧
        GivesTo F w y x) →
    ¬ SomeContingentConcreteAt F concrete w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (concrete : B → Prop) (w : W),
    ActualAbsenceHoldersGiveEach F PowerFor concrete w → GivenExists F →
    ActualAbsenceInitiatorPresent F PowerFor concrete w → SomeContingentConcreteAt F concrete w →
    ActualAbsenceExerciseDiffers F PowerFor concrete w) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (concrete : B → Prop) (w : W),
    ActualAbsenceByWithholding F PowerFor concrete w → SomeContingentConcreteAt F concrete w →
    ∃ y, TwoWayGiverAt F w y ∧ GivingVariesAt F w y ∧ ¬ FixedGiver F y) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (concrete : B → Prop) (w v : W) (y x : B),
    GivenExists F → F.history.ontic.frame.access w v →
    NoActualContingentConcreteIn F concrete w v → F.history.ontic.ExistsAt w y →
    F.history.ontic.ExistsAt v y → concrete x → ContingentAt F.history.ontic w x →
    GivesTo F w y x → TwoWayGiverAt F w y) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (concrete : B → Prop) (w : W) (y : B),
    TruthCore.Logic.ExcludedMiddle → concrete y → F.history.ontic.ExistsAt w y →
    (∀ x, concrete x → ContingentAt F.history.ontic w x →
      ∃ v, F.history.ontic.frame.access w v ∧ ¬ F.history.ontic.ExistsAt v x ∧
        F.history.ontic.ExistsAt v y) →
    NecessaryAt F.history.ontic w y) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (PowerOver : B → B → R → Prop) (concrete : B → Prop) (w : W) (essenceOf esseOf : B → P)
    (Received : B → P → Prop) (MF : B → Prop) (CanFailToBe : B → R → Prop),
    TruthCore.Logic.ExcludedMiddle →
    SomeHolderHasPowerOverEachActualContingent F PowerFor PowerOver concrete w →
    ∀ f, concrete f → FoundationalAt F w essenceOf esseOf Received MF CanFailToBe PowerOver f →
      NecessaryAt F.history.ontic w f)

/-- Nonvacuity on `theistG` (all at the actual world `false`): P1′, P2′, P2δ,
P3′, P4′, P5, the holders-give-each premise, factive giving, the transfer, the
withheld-giving bridge, symmetric access, the three premises of Pruss's
direction; and every new conclusion (`g` necessary, a two-way giver, not a fixed
giver). -/
def TheistNonvacuity : Prop :=
  ActualAbsenceGrounded theistG gPower allC false ∧
  ActualAbsenceInitiatorPresent theistG gPower allC false ∧
  ActualAbsenceExerciseDiffers theistG gPower allC false ∧
  ActualAbsencePowerHoldersConcrete theistG gPower allC false ∧
  PossiblyNoActualContingentConcrete theistG allC false ∧
  SomeContingentConcreteAt theistG allC false ∧
  ActualAbsenceHoldersGiveEach theistG gPower allC false ∧
  GivenExists theistG ∧
  ActualAbsencePowerIsPowerOverEsse theistG gPower gOverC allC false ∧
  WithheldGivingIsPowerOverEsse theistG gOverC false ∧
  TruthCore.Modal.Symmetric theistG.history.ontic.frame ∧
  ActualityGroundedAtAbsenceWorlds theistG gPower allC false ∧
  ActualityInitiatorPresentAtAbsenceWorlds theistG gPower allC false ∧
  ActualityPowerHoldersConcreteAtAbsenceWorlds theistG gPower allC false ∧
  SomeHolderHasPowerOverEachActualContingent theistG gPower gOverC allC false ∧
  NecessaryVaryingGiverWithActualAbsencePower theistG gPower allC false ∧
  ActualAbsenceByWithholding theistG gPower allC false ∧
  NecessaryConcreteHolderOfActualityPower theistG gPower allC false ∧
  TwoWayGiverAt theistG false .g ∧ ¬ FixedGiver theistG .g

/-- Q1, collective without distributive (`replacementG`, actual world
`false`): P1′, P2′, P2δ, P3′, P4′, P5 and factive giving hold; `g` is
necessary with varying giving (it gives a replacement `d` at `true`); the
holders-give-each premise, the transfer and its conclusion fail, and `g` is
not a two-way giver in the withholding form. Also the omission model of the
holders-give-each premise (argument 4) and of the transfer (argument 1). -/
def CollectiveWithoutDistributive : Prop :=
  ActualAbsenceGrounded replacementG gPower allC false ∧
  ActualAbsenceInitiatorPresent replacementG gPower allC false ∧
  ActualAbsenceExerciseDiffers replacementG gPower allC false ∧
  ActualAbsencePowerHoldersConcrete replacementG gPower allC false ∧
  PossiblyNoActualContingentConcrete replacementG allC false ∧
  SomeContingentConcreteAt replacementG allC false ∧
  GivenExists replacementG ∧
  NecessaryVaryingGiverWithActualAbsencePower replacementG gPower allC false ∧
  ¬ ActualAbsenceHoldersGiveEach replacementG gPower allC false ∧
  ¬ ActualAbsencePowerIsPowerOverEsse replacementG gPower noOver allC false ∧
  ¬ SomeHolderHasPowerOverEachActualContingent replacementG gPower noOver allC false ∧
  ¬ ActualAbsenceByWithholding replacementG gPower allC false ∧
  ¬ TwoWayGiverAt replacementG false .g

/-- Q1, distributive without collective (`vanCleveG` at `a`): `g` exists
everywhere, gives `c` and `d` being wherever they exist and has POWER_OVER_ESSE_1
over each; each is contingent at `a`; but no accessible world lacks both (P4′
fails), so even a holder of every power (`gPower`) fails initiator presence
P2′ for the joint absence. Power over each member's esse does not give the
joint possibility (Van Cleve's point, now with a common holder). -/
def DistributiveWithoutCollective : Prop :=
  GivenExists vanCleveG ∧ NecessaryAt vanCleveG.history.ontic .a .g ∧
  (∀ x, onlyCD x → ContingentAt vanCleveG.history.ontic .a x) ∧
  (∀ x, onlyCD x → PowerOverEsse vanCleveG gOverCD .g x) ∧
  ¬ PossiblyNoActualContingentConcrete vanCleveG onlyCD .a ∧
  ¬ ActualAbsenceInitiatorPresent vanCleveG gPower onlyCD .a

/-- Q1, distributive grounding with varying holders (`mutualG` at
`(true, true)`): the possible absence of each actual contingent concretum is
grounded in a power of the other, with initiator presence; holders are concrete;
P4′ and P5 hold; yet no being is necessary at the actual world, and the
collective P1′ fails. -/
def MutualAnnihilators : Prop :=
  EachActualAbsenceGrounded mutualG annihilatorPower allC (true, true) ∧
  EachActualAbsenceInitiatorPresent mutualG annihilatorPower allC (true, true) ∧
  PossiblyNoActualContingentConcrete mutualG allC (true, true) ∧
  SomeContingentConcreteAt mutualG allC (true, true) ∧
  (∀ y, ¬ (mutualG.history.ontic.ExistsAt (true, true) y ∧
    NecessaryAt mutualG.history.ontic (true, true) y)) ∧
  ¬ ActualAbsenceGrounded mutualG annihilatorPower allC (true, true)

/-- Omission models for the new arguments (actual world `false` unless noted).
1. P2δ omitted (argument 2): `inertG` with `gPower`: P1′, P2′, P3′, P4′, P5
   hold, P2δ fails, and no necessary concrete holder has varying giving.
2. Factive giving omitted (argument 4): `nonFactiveG`: P1′, P2′, P4′, P5 and
   the holders-give-each premise hold; giving is not factive; the joint absence
   is not realized by withholding.
3. Withheld-giving bridge omitted (argument 5): `theistG` with no power over
   esse: `ActualAbsenceByWithholding` holds, the bridge and the conclusion fail.
4. Symmetric access omitted (argument 6): `forwardG` with no powers: P4′, P5
   and the three absence-world premises hold (vacuously: `true` accesses only
   itself), access is not symmetric, and the conclusion fails.
5. Grounding at the absence worlds omitted (argument 6): `theistG` with no
   powers: symmetric access, P4′, P5, initiator presence and concreteness
   (vacuous) hold, the grounding and the conclusion fail.
6. Initiator presence at the absence worlds omitted (argument 6):
   `absentHolderG` with `gPowerThere`: `g` exists only at `true`, where it has
   the power; grounding, concreteness, symmetric access, P4′ and P5 hold;
   initiator presence and the conclusion fail.
7. Concreteness at the absence worlds omitted (argument 6): `theistG` with
   only `c` and `d` concrete: everything else holds, the conclusion fails.
8. P4′ omitted (argument 6): `vanCleveG` at `a` with only `c`, `d` concrete
   and `gPower`: symmetric access, P5 and the absence-world premises
   (vacuously) hold; P4′ and the conclusion fail. -/
def Omissions : Prop :=
  (ActualAbsenceGrounded inertG gPower allC false ∧
    ActualAbsenceInitiatorPresent inertG gPower allC false ∧
    ActualAbsencePowerHoldersConcrete inertG gPower allC false ∧
    PossiblyNoActualContingentConcrete inertG allC false ∧
    SomeContingentConcreteAt inertG allC false ∧
    ¬ ActualAbsenceExerciseDiffers inertG gPower allC false ∧
    ¬ NecessaryVaryingGiverWithActualAbsencePower inertG gPower allC false) ∧
  (ActualAbsenceGrounded nonFactiveG gPower allC false ∧
    ActualAbsenceInitiatorPresent nonFactiveG gPower allC false ∧
    PossiblyNoActualContingentConcrete nonFactiveG allC false ∧
    SomeContingentConcreteAt nonFactiveG allC false ∧
    ActualAbsenceHoldersGiveEach nonFactiveG gPower allC false ∧
    ¬ GivenExists nonFactiveG ∧
    ¬ ActualAbsenceByWithholding nonFactiveG gPower allC false) ∧
  (ActualAbsenceByWithholding theistG gPower allC false ∧
    ¬ WithheldGivingIsPowerOverEsse theistG noOver false ∧
    ¬ SomeHolderHasPowerOverEachActualContingent theistG gPower noOver allC false) ∧
  (PossiblyNoActualContingentConcrete forwardG allC false ∧
    SomeContingentConcreteAt forwardG allC false ∧
    ActualityGroundedAtAbsenceWorlds forwardG noPower allC false ∧
    ActualityInitiatorPresentAtAbsenceWorlds forwardG noPower allC false ∧
    ActualityPowerHoldersConcreteAtAbsenceWorlds forwardG noPower allC false ∧
    ¬ TruthCore.Modal.Symmetric forwardG.history.ontic.frame ∧
    ¬ NecessaryConcreteHolderOfActualityPower forwardG noPower allC false) ∧
  (TruthCore.Modal.Symmetric theistG.history.ontic.frame ∧
    PossiblyNoActualContingentConcrete theistG allC false ∧
    SomeContingentConcreteAt theistG allC false ∧
    ActualityInitiatorPresentAtAbsenceWorlds theistG noPower allC false ∧
    ActualityPowerHoldersConcreteAtAbsenceWorlds theistG noPower allC false ∧
    ¬ ActualityGroundedAtAbsenceWorlds theistG noPower allC false ∧
    ¬ NecessaryConcreteHolderOfActualityPower theistG noPower allC false) ∧
  (TruthCore.Modal.Symmetric absentHolderG.history.ontic.frame ∧
    PossiblyNoActualContingentConcrete absentHolderG allC false ∧
    SomeContingentConcreteAt absentHolderG allC false ∧
    ActualityGroundedAtAbsenceWorlds absentHolderG gPowerThere allC false ∧
    ActualityPowerHoldersConcreteAtAbsenceWorlds absentHolderG gPowerThere allC false ∧
    ¬ ActualityInitiatorPresentAtAbsenceWorlds absentHolderG gPowerThere allC false ∧
    ¬ NecessaryConcreteHolderOfActualityPower absentHolderG gPowerThere allC false) ∧
  (TruthCore.Modal.Symmetric theistG.history.ontic.frame ∧
    PossiblyNoActualContingentConcrete theistG onlyCD false ∧
    SomeContingentConcreteAt theistG onlyCD false ∧
    ActualityGroundedAtAbsenceWorlds theistG gPower onlyCD false ∧
    ActualityInitiatorPresentAtAbsenceWorlds theistG gPower onlyCD false ∧
    ¬ ActualityPowerHoldersConcreteAtAbsenceWorlds theistG gPower onlyCD false ∧
    ¬ NecessaryConcreteHolderOfActualityPower theistG gPower onlyCD false) ∧
  (TruthCore.Modal.Symmetric vanCleveG.history.ontic.frame ∧
    SomeContingentConcreteAt vanCleveG onlyCD .a ∧
    ActualityGroundedAtAbsenceWorlds vanCleveG gPower onlyCD .a ∧
    ActualityInitiatorPresentAtAbsenceWorlds vanCleveG gPower onlyCD .a ∧
    ActualityPowerHoldersConcreteAtAbsenceWorlds vanCleveG gPower onlyCD .a ∧
    ¬ PossiblyNoActualContingentConcrete vanCleveG onlyCD .a ∧
    ¬ NecessaryConcreteHolderOfActualityPower vanCleveG gPower onlyCD .a)

/-- Rivals at matching scope (actual world `false`).
1. Inert necessary being (`inertG`, no powers): `g` exists at every world and
   is a fixed giver; P4′ and P5 hold; P1′ fails.
2. Necessary non-rational source (`necessitarianG`): `g` necessary, a fixed
   giver, factive giving, giving `c` being at every world; P5 fails (`c` is
   necessary too) while P4′ holds vacuously.
3. Positive-outcome powers only (`theistG` with `positivePower`): `g` is a
   necessary two-way giver; P4′, P5 and symmetric access hold; P1′ fails (no
   power for the joint absence, which no giving produces); every premise of
   Pruss's direction holds and so does its conclusion. -/
def Rivals : Prop :=
  (NecessaryAt inertG.history.ontic false .g ∧ FixedGiver inertG .g ∧
    PossiblyNoActualContingentConcrete inertG allC false ∧
    SomeContingentConcreteAt inertG allC false ∧
    ¬ ActualAbsenceGrounded inertG noPower allC false) ∧
  (NecessaryAt necessitarianG.history.ontic false .g ∧ FixedGiver necessitarianG .g ∧
    GivenExists necessitarianG ∧ GivesTo necessitarianG false .g .c ∧
    PossiblyNoActualContingentConcrete necessitarianG allC false ∧
    ¬ SomeContingentConcreteAt necessitarianG allC false) ∧
  (NecessaryAt theistG.history.ontic false .g ∧ TwoWayGiverAt theistG false .g ∧
    PossiblyNoActualContingentConcrete theistG allC false ∧
    SomeContingentConcreteAt theistG allC false ∧
    TruthCore.Modal.Symmetric theistG.history.ontic.frame ∧
    ¬ ActualAbsenceGrounded theistG (positivePower givesCHere) allC false ∧
    ActualityGroundedAtAbsenceWorlds theistG (positivePower givesCHere) allC false ∧
    ActualityInitiatorPresentAtAbsenceWorlds theistG (positivePower givesCHere) allC false ∧
    ActualityPowerHoldersConcreteAtAbsenceWorlds theistG (positivePower givesCHere) allC false ∧
    NecessaryConcreteHolderOfActualityPower theistG (positivePower givesCHere) allC false)

/-- The certificate: laws, nonvacuity, the three Q1 separations, the omission
models and the rival models. -/
def Controls : Prop :=
  Laws ∧ TheistNonvacuity ∧ CollectiveWithoutDistributive ∧ DistributiveWithoutCollective ∧
    MutualAnnihilators ∧ Omissions ∧ Rivals

end Model

end TruthCore.Modal.PrussPowerPremises
