module

public import TruthCore.Epistemology.UltimateExplanation
public import TruthCore.Logic.SelfApplication

/-!
An internal rather than universal critique of an unrestricted-future stance.

The #737 `Cell (openFuture n) on n` includes two populated continuations with
the same evidence through n and opposite next outcomes. No metaphysical claim
about all future laws is built into that binary surrogate. In particular,
failure of ultimate explanation alone does NOT imply that this is the right
evidence cell; that applicability bridge remains OPEN.

A stance here has (i) the continuations it admits and (ii) which particular
scientific forecasts or practical policies it presents as *entitled*. Its own
strict standard demands perfect cross-continuation prediction or payoff at
least two, respectively. Neither standard is true epistemic justification by
definition; the strong standard is attributed only to a rival that endorses it.
The weaker practice standard requires only the robust payoff floor one.

The intended conclusion is conditional: a stance that admits both successors,
endorses the strict norm, and nevertheless claims a particular prediction or
high-payoff policy entitled defeats that claim by its OWN stated standard.
Merely acting, using a safe fallback, expressing a fallible forecast, or
withholding strict entitlement is not inconsistent on this interpretation.
-/

@[expose] public section

namespace TruthCore.Epistemology.NoFoundationPractice

open TruthCore.Epistemology.UltimateExplanation
open TruthCore.Modern.Hume.Induction
open TruthCore.Logic.SelfApplication

/-- Deterministic scientific forecast based on the complete observed trace and
the end of its observed prefix. No computability bound or epistemic oracle. -/
abbrev Forecast := Trace → Nat → Bool

/-- A policy uses the same record but selects one of #737's three task actions.
This menu includes a robust safe fallback; it is not the space of all real acts. -/
abbrev Policy := Trace → Nat → Action

/-- The claimed subject matter is particular, not an undifferentiated label
"science". Each entitlement attaches to a method or policy and a horizon. -/
inductive Claim where
  | scientific (method : Forecast) (horizon : Nat)
  | practical (policy : Policy) (horizon : Nat)

/-- What a position admits and what it presents as entitled. `entitled` is an
attributed stance predicate, not a fact about genuine normative warrant. -/
structure Stance where
  admits : Nat → Trace → Prop
  entitled : Claim → Prop

/-- The stance permits each of the two concrete, observationally identical
histories at every finite horizon: uninterrupted truth and a failure at n+1.
Both are real trace functions in the selected mathematical domain. -/
def BothSuccessors (s : Stance) : Prop :=
  ∀ n, s.admits n on ∧ s.admits n (delayedFailure (n+1))

/-- Strong normative reading that the assessed stance explicitly chooses:
every *entitled* forecast must be exactly correct in every admitted future,
and every *entitled* practical policy must earn at least two in every future.
This is intentionally stronger than ordinary fallible justification or
satisficing action. Scope includes both claim constructors. -/
def strictNorm (s : Stance) : Norm Claim where
  scope := fun _ => True
  standard := fun
    | .scientific method n => ∀ f, s.admits n f → method on n = f (n+1)
    | .practical policy n => ∀ f, s.admits n f →
        2 ≤ payoff (policy on n) (f (n+1))

/-- A rival's more modest practice norm is silent about exact scientific
forecasts and asks only that an endorsed action meet the payoff floor one.
Whether this is an adequate practical norm is not asserted. -/
def modestNorm (s : Stance) : Norm Claim where
  scope := fun
    | .scientific _ _ => False
    | .practical _ _ => True
  standard := fun
    | .scientific _ _ => True
    | .practical policy n => ∀ f, s.admits n f →
        1 ≤ payoff (policy on n) (f (n+1))

/-- The robust fallback from #737, now offered as a method for every finite
record. This is a choice, not a proof of any moral or epistemic duty. -/
def safePolicy : Policy := fun _ _ => .safe

/-- An open-future stance that endorses only policies selecting the robust
fallback at the observed record. It need not endorse exact scientific claims. -/
def prudentOpen : Stance where
  admits := fun n f => Cell (openFuture n) on n f
  entitled := fun
    | .scientific _ _ => False
    | .practical policy n => policy on n = .safe

/-- The same nonempty open future, but no asserted strict entitlements; it is a
consistency control for accepting a universal strict norm while withholding. -/
def abstainingOpen : Stance where
  admits := fun n f => Cell (openFuture n) on n f
  entitled := fun _ => False

/-- A genuinely narrower stable-law profile endorses forecasts returning true
and policies betting true on the record. It is a control for the difference
made by the empirically consequential restriction, not evidence for it. -/
def confidentStable : Stance where
  admits := fun n f => Cell stable on n f
  entitled := fun
    | .scientific method n => method on n = true
    | .practical policy n => policy on n = .betTrue

/-- Both admitted continuations defeat EVERY deterministic binary forecast
and every policy seeking payoff two on all continuations. Explicitly gives a
countercontinuation for each method/policy; no probabilities are invoked. -/
def UniformBarrier : Prop :=
  ∀ s : Stance, BothSuccessors s →
    (∀ (method : Forecast) n, ∃ f, s.admits n f ∧
      method on n ≠ f (n+1)) ∧
    (∀ (policy : Policy) n, ∃ f, s.admits n f ∧
      payoff (policy on n) (f (n+1)) < 2)

/-- A stance that applies its own strict cross-continuation standard to its
own entitled claims must withdraw every such entitlement in the two-successor
cell. Any positive entitlement while affirming that norm is an internal
conflict; non-entitlement or failure to endorse the norm remains coherent. -/
def InternalDiscipline : Prop :=
  ∀ s : Stance, BothSuccessors s →
    ((strictNorm s).Holds s.entitled → ∀ c, ¬ s.entitled c) ∧
    ((∃ c, s.entitled c) → ¬ (strictNorm s).Holds s.entitled)

/-- Real populated open futures: the strict norm can be held with no strict
entitlement, while a weaker robust-action norm accepts a genuinely offered
safe policy. The strong norm fails for that same positive safe claim. This
separates internal inconsistency from an alleged impossibility of acting. -/
def OpenControls : Prop :=
  BothSuccessors prudentOpen ∧
  BothSuccessors abstainingOpen ∧
  (strictNorm abstainingOpen).Holds abstainingOpen.entitled ∧
  (modestNorm prudentOpen).Holds prudentOpen.entitled ∧
  prudentOpen.entitled (.practical safePolicy 0) ∧
  ¬ (strictNorm prudentOpen).Holds prudentOpen.entitled ∧
  (∀ n f, prudentOpen.admits n f →
    1 ≤ payoff (safePolicy on n) (f (n+1)))

/-- Under the stronger stable profile, both positive strict entitlements and
the strict norm CAN coexist; the altered future admissibility is load-bearing.
The delayed-failure trace is excluded by stable, for a nonempty observed cell. -/
def StableControl : Prop :=
  (strictNorm confidentStable).Holds confidentStable.entitled ∧
  confidentStable.entitled (.scientific (fun _ _ => true) 0) ∧
  confidentStable.entitled (.practical (fun _ _ => .betTrue) 0) ∧
  Cell stable on 0 on ∧
  ¬ BothSuccessors confidentStable

end TruthCore.Epistemology.NoFoundationPractice
