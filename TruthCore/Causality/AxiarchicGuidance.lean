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
on? Betterness is given respect by respect (`rk r s x y`: in respect `r`, `x` is
better than `y` at `s`) and overall (`good`). A reason for `y` over `x` in respect
`r` is *outweighed* at `s` when overall `x` is better and the favouring favours
`x` (`Outweighed`). The favouring is *guided* by that outweighed reason when, in
some scenario that agrees on the control and keeps the respect's ranking, the
favouring follows it (`GuidedByOutweighed`). Whether the outweighed reason is
also *registered* in the source's actual state is a question about the stand-ins
of round 2: a stand-in that carries only an overall degree registers no respect
in which two overall-tied candidates differ (`degreeOnlyRegistersNoRespectBetweenTies`
in the results module).

**Self-application.** Does the source take its own favouring as an object? A
second-order favouring `favours2 ψ` has the bearer's own determinations as its
candidates; the bearer *self-applies* when such a favouring favours one of its
own favouring determinations over some determination (`SelfApplies`).

Every model in `Control` is a finite structural surrogate; it witnesses only the
stated formal interpretation, never a metaphysical possibility. Which account a
profile represents is an interpretive assignment: the personal source and A4
share their profile, stand-ins and loci (round 2, control rows 1 and 2), so every
test stated on these carries gives them the same verdict. -/

@[expose] public section

namespace TruthCore.Causality.AxiarchicGuidance

open TruthCore.Causality.GoodFavouring (Profile Tracks Fixed)

variable {S X R Z B D : Type}

/-- An OUTWEIGHED REASON at `s`: in respect `r` the candidate `y` is better than
`x`, yet overall `x` is better than `y` and the profile favours `x` over `y`. -/
def Outweighed (rk : R → S → X → X → Prop) (good : S → X → X → Prop) (φ : Profile S X)
    (s : S) (r : R) (x y : X) : Prop :=
  rk r s y x ∧ good s x y ∧ φ s x y

/-- COUNTERFACTUAL GUIDANCE by an outweighed reason: the reason for `y` in respect
`r` is outweighed at `s`, and in some scenario `t` that agrees with `s` on the
control `ctrl` and keeps respect `r`'s ranking of `y` over `x`, the profile
favours `y` over `x`. The reason the source does not act on at `s` would make a
difference to its favouring where it is not outweighed. -/
def GuidedByOutweighed (rk : R → S → X → X → Prop) (good : S → X → X → Prop) (ctrl : S → Z)
    (φ : Profile S X) (s : S) (r : R) (x y : X) : Prop :=
  Outweighed rk good φ s r x y ∧ ∃ t, ctrl t = ctrl s ∧ rk r t y x ∧ φ t y x

/-- SELF-APPLICATION: some second-order favouring determination of `b`, whose
candidates are determinations, favours at some scenario one of `b`'s own
(first-order) favouring determinations over some determination `d`. -/
def SelfApplies (Has : B → D → Prop) (favours : Profile S X → D)
    (favours2 : Profile S D → D) (b : B) : Prop :=
  ∃ ψ φ s d, Has b (favours2 ψ) ∧ Has b (favours φ) ∧ ψ s (favours φ) d

/-! ## Finite control for counterfactual guidance

Two candidates `c`, `d`; two respects, `fit` (realization of the recipient good)
and `extra` (further content that fit does not record); two scenarios. In `base`,
`d` is better in fit, `c` is better in the extra respect, and overall `c` is
better: the reason for `d` is outweighed. In `alt` the extra respect ties them
and overall `d` is better. -/
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

/-- Scenarios: `base` (the reason for `d` is outweighed) and `alt` (it is not). -/
inductive Scen
  | base
  | alt
  deriving DecidableEq

/-- Respect-wise betterness. -/
def rk : Respect → Scen → Cand → Cand → Prop
  | .fit, _, .d, .c => True
  | .extra, .base, .c, .d => True
  | _, _, _, _ => False

/-- Overall betterness. -/
def good : Scen → Cand → Cand → Prop
  | .base, .c, .d => True
  | .alt, .d, .c => True
  | _, _, _ => False

/-- The good-tracking profile, shared by the personal source and A4 (round 2,
control rows 1 and 2). -/
def goodTracking : Profile Scen Cand := good

/-- A fixed favouring of `c` over `d` (determined to one content). -/
def fixedC : Profile Scen Cand := fun _ x y => x = .c ∧ y = .d

/-- A nature directed to fit alone. -/
def fitNature : Profile Scen Cand := rk .fit

/-- No control beyond the scenario space. -/
def noCtrl (_ : Scen) : Unit := ()

/-- Counterfactual guidance at `base` by the outweighed fit reason for `d` over
`c`:

1. the good-tracking profile (personal and A4 alike) is guided by it;
2. the fixed favouring of `c` meets the outweighed condition but is not guided;
3. the fit nature does not favour `c` over `d` at `base`, so for it the reason
   is not outweighed.

Registration of the outweighed reason in the source's actual state is not a
property of the profile; it is posed separately on stand-ins
(`degreeOnlyRegistersNoRespectBetweenTies`). -/
def GuidanceTable : Prop :=
  GuidedByOutweighed rk good noCtrl goodTracking .base .fit .c .d ∧
  (Outweighed rk good fixedC .base .fit .c .d ∧
    ¬ GuidedByOutweighed rk good noCtrl fixedC .base .fit .c .d) ∧
  ¬ Outweighed rk good fitNature .base .fit .c .d

end Control

end TruthCore.Causality.AxiarchicGuidance
