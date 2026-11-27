module

public import TruthCore.Causality.AxiarchicFoundation

/-! # Counterfactual guidance and self-application: two tests between apprehension and imitability exemplars (#2145, premise lane C, round 3)

Analyst formulations, attribution deferred (logic first). See
`docs/notes/causal-perfection-transfer.md`, section "Counterfactual guidance and
self-application against imitability exemplars".

Round 2 left the containment-recognition bridge at parity with the strongest
rival A4: a source that contains individuating, value-ranked modes of
imitability which guide its favouring, without apprehending them. The owner
approved two tests of the remaining gap, to be applied identically to the
personal source.

**Counterfactual guidance.** Is the source sensitive to reasons it does not act
on? Value is graded respect by respect: `w s r x` is the weight of candidate `x`
in respect `r` at scenario `s`. A reason for `y` over `x` in respect `r` is
*outweighed* at `s` when `r` weighs `y` above `x`, yet overall `x` is better and
the favouring favours `x` (`Outweighed`). The favouring is *guided* by that
reason when the reason itself makes a difference: in some scenario that agrees
on the control, raises `y`'s weight in `r` alone and holds every other respect
and every other candidate fixed (`RaisesOnly`), the favouring favours `y` over
`x` (`GuidedByOutweighed`). A profile blind to `r` is never guided by an
outweighed `r`-reason (`respectBlindNotGuided`, results module).

**Self-application.** Does the source take its own favouring as an object? A
second-order favouring has determinations as its candidates. In its weak form
it favours one of the bearer's own favouring determinations over some
determination (`SelfApplies`). In its strong form it is responsive to the
standard of its own favouring: it favours a favouring that tracks the value
order over one that does not (`SecondOrderStandard`, read as a second-order
value ranking).

Every model in `Control` is a finite structural surrogate; it witnesses only the
stated formal interpretation, never a metaphysical possibility. Which account a
profile represents is an interpretive assignment. A4 is defined as a structural
duplicate of the personal source (round 2, control rows 1 and 2: the same
profile, stand-ins and loci), so parity on every test stated on these carriers
follows from that definition and is not further evidence. -/

@[expose] public section

namespace TruthCore.Causality.AxiarchicGuidance

open TruthCore.Causality.GoodFavouring (Profile Tracks Fixed)

variable {S X R Z B D : Type}

/-- An OUTWEIGHED REASON at `s`: respect `r` weighs `y` above `x`, yet overall
`x` is better than `y` and the profile favours `x` over `y`. -/
def Outweighed (w : S → R → X → Nat) (good : S → X → X → Prop) (φ : Profile S X)
    (s : S) (r : R) (x y : X) : Prop :=
  w s r x < w s r y ∧ good s x y ∧ φ s x y

/-- `t` RAISES `y` IN RESPECT `r` ALONE over `s`: every other respect weighs every
candidate as at `s`, respect `r` weighs every candidate other than `y` as at `s`,
and it weighs `y` more. -/
def RaisesOnly (w : S → R → X → Nat) (s t : S) (r : R) (y : X) : Prop :=
  (∀ r' z, r' ≠ r → w t r' z = w s r' z) ∧ (∀ z, z ≠ y → w t r z = w s r z) ∧
    w s r y < w t r y

/-- COUNTERFACTUAL GUIDANCE by an outweighed reason: the reason for `y` in
respect `r` is outweighed at `s`, and in some scenario `t` that agrees with `s`
on the control and raises `y` in respect `r` alone, the profile favours `y` over
`x`. The reason itself, not the removal of what outweighs it, makes the
difference. -/
def GuidedByOutweighed (w : S → R → X → Nat) (good : S → X → X → Prop) (ctrl : S → Z)
    (φ : Profile S X) (s : S) (r : R) (x y : X) : Prop :=
  Outweighed w good φ s r x y ∧ ∃ t, ctrl t = ctrl s ∧ RaisesOnly w s t r y ∧ φ t y x

/-- A profile is BLIND TO RESPECT `r`: it is the same in any two scenarios that
weigh every candidate alike in every other respect. -/
def BlindTo (w : S → R → X → Nat) (φ : Profile S X) (r : R) : Prop :=
  ∀ s t, (∀ r' z, r' ≠ r → w t r' z = w s r' z) → ∀ x y, φ s x y ↔ φ t x y

/-- WEAK SELF-APPLICATION: some second-order favouring determination of `b`,
whose candidates are determinations, favours at some scenario one of `b`'s own
favouring determinations over some determination `d`. It does not require that
`b` lacks `d`. -/
def SelfApplies (Has : B → D → Prop) (favours : Profile S X → D)
    (favours2 : Profile S D → D) (b : B) : Prop :=
  ∃ ψ φ s d, Has b (favours2 ψ) ∧ Has b (favours φ) ∧ ψ s (favours φ) d

/-- The SECOND-ORDER STANDARD: a favouring determination that tracks the value
order `good` ranks above one that does not. Read as a second-order value ranking
of favourings. It is the same in every scenario, since `Tracks` quantifies over
all of them. -/
def SecondOrderStandard (good : S → X → X → Prop) (favours : Profile S X → D) :
    S → D → D → Prop :=
  fun _ d d' => ∃ φ φ', d = favours φ ∧ d' = favours φ' ∧ Tracks φ good ∧ ¬ Tracks φ' good

/-- The SCENARIO-RELATIVE SECOND-ORDER STANDARD: at `s`, a favouring determination
whose profile agrees with the value order at `s` ranks above one whose profile
does not. Unlike `SecondOrderStandard` it can vary across scenarios. -/
def SecondOrderStandardAt (good : S → X → X → Prop) (favours : Profile S X → D) :
    S → D → D → Prop :=
  fun s d d' => ∃ φ φ', d = favours φ ∧ d' = favours φ' ∧
    GoodFavouring.AlignedAt φ good s ∧ ¬ GoodFavouring.AlignedAt φ' good s

/-- STRONG SELF-APPLICATION: some second-order favouring of `b` favours, at some
scenario, one of `b`'s own favouring determinations over another favouring
determination, and the second-order standard ranks them that way. -/
def SelfAppliesToStandard (Has : B → D → Prop) (good : S → X → X → Prop)
    (favours : Profile S X → D) (favours2 : Profile S D → D) (b : B) : Prop :=
  ∃ ψ φ φ' s, Has b (favours2 ψ) ∧ Has b (favours φ) ∧ ψ s (favours φ) (favours φ') ∧
    SecondOrderStandard good favours s (favours φ) (favours φ')

/-! ## Finite control

Two candidates `c`, `d`; two respects, `fit` (realization of the recipient good)
and `extra` (further content fit does not record); two scenarios. In `base`, `d`
weighs more in fit and `c` in the extra respect, and `c` is better overall: the
fit reason for `d` is outweighed. In `raised`, `d`'s fit weight alone is raised,
and `d` is better overall. Overall betterness is the larger sum of weights, given
as a table. -/
namespace Control

/-- Candidates. -/
inductive Cand
  | c
  | d
  deriving DecidableEq

/-- Respects. -/
inductive Respect
  | fit
  | extra
  deriving DecidableEq

/-- Scenarios: `base` and `raised` (`d`'s fit weight alone raised). -/
inductive Scen
  | base
  | raised
  deriving DecidableEq

/-- Respect weights. -/
def w : Scen → Respect → Cand → Nat
  | _, .fit, .c => 1
  | .base, .fit, .d => 2
  | .raised, .fit, .d => 6
  | _, .extra, .c => 3
  | _, .extra, .d => 0

/-- Overall betterness: the larger sum of weights (base: `c` 4 against `d` 2;
raised: `d` 6 against `c` 4), given as a table. -/
def good : Scen → Cand → Cand → Prop
  | .base, .c, .d => True
  | .raised, .d, .c => True
  | _, _, _ => False

/-- The good-tracking profile, shared by the personal source and A4. -/
def goodTracking : Profile Scen Cand := good

/-- A fit-blind profile that follows the extra respect alone. -/
def extraOnly : Profile Scen Cand := fun s x y => w s .extra y < w s .extra x

/-- A fixed favouring of `c` over `d`. -/
def fixedC : Profile Scen Cand := fun _ x y => x = .c ∧ y = .d

/-- A nature that follows fit alone (the D-nature's form on this carrier). -/
def fitNature : Profile Scen Cand := fun s x y => w s .fit y < w s .fit x

/-- No control beyond the scenario space. -/
def noCtrl (_ : Scen) : Unit := ()

/-- Counterfactual guidance at `base` by the outweighed fit reason for `d` over
`c`, with `raised` raising `d`'s fit weight alone:

1. `raised` raises `d` in fit alone over `base`;
2. the good-tracking profile (personal source and A4 alike) is guided;
3. the fit-blind profile meets the outweighed condition and is not guided;
4. the fixed favouring meets the outweighed condition and is not guided;
5. the fit nature does not favour `c` over `d` at `base`, so for it the reason
   is not outweighed;
6. strong self-application: with favourings as their own determinations, the
   second-order standard ranks the good-tracking profile over the fit-blind one,
   in every scenario alike. -/
def GuidanceTable : Prop :=
  RaisesOnly w .base .raised .fit .d ∧
  GuidedByOutweighed w good noCtrl goodTracking .base .fit .c .d ∧
  (Outweighed w good extraOnly .base .fit .c .d ∧
    ¬ GuidedByOutweighed w good noCtrl extraOnly .base .fit .c .d) ∧
  (Outweighed w good fixedC .base .fit .c .d ∧
    ¬ GuidedByOutweighed w good noCtrl fixedC .base .fit .c .d) ∧
  ¬ Outweighed w good fitNature .base .fit .c .d ∧
  (∀ s, SecondOrderStandard good id s goodTracking extraOnly)

end Control

end TruthCore.Causality.AxiarchicGuidance
