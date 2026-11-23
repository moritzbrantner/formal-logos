module

public import TruthCore.Results.Explanation.NoFoundationLawChaos.Solution
public import TruthCore.Results.Epistemology.NoFoundationPractice.Solution

/-! Formal adapters from the selector-relative `WholeSuffixRich` of
`RecombinationFork` (#1867) to the two existing downstream consumers:

* #1809, `NoFoundationLawChaos.certificate`, stated over a Profile cell
  through `SuffixComplete p n` and `UniversalProjection p q n`;
* #1808, `NoFoundationPractice.internalDiscipline`, stated over a `Stance`
  through `BothSuccessors s`.

They are Lean-only lemmas, not registered corpus results. They show only
that the *formal* hand-off from S to those certificates exists; they do not
show that any real law space satisfies `WholeSuffixRich`. That applicability
bridge (from no ultimate explanation, U, to R and C) remains OPEN.

The file also proves that the satisfiers of one fixed local `Profile` form a
prefix-closed selector (`follows_prefixClosed`), the structural rationale the
note gives for C when every admissibility exclusion is finitely witnessed. -/

@[expose] public section

namespace TruthCore.Results.Explanation.NoFoundationLawChaos.Adapters

open TruthCore.Explanation.NoFoundationLawChaos
open TruthCore.Explanation.LawActuality
open TruthCore.Epistemology.UltimateExplanation
open TruthCore.Epistemology.NoFoundationPractice
open TruthCore.Modern.Hume.Induction

/-- With whole-suffix richness, the selector admits exactly the #737 open
cell: the selector restriction is idle at that cutoff. -/
theorem wholeSuffix_admitted_iff (allowed : Trace → Prop) (n : Nat)
    (hwhole : WholeSuffixRich allowed n) (f : Trace) :
    Admitted allowed n f ↔ Cell (openFuture n) on n f := by
  constructor
  · exact fun h => h.1
  · intro hf
    have hsplice : splice n f = f := by
      funext t
      show (if t < n+1 then true else f t) = f t
      by_cases ht : t < n+1
      · simp only [ht, ↓reduceIte]
        exact (hf.2 t ht).symm
      · simp only [ht, ↓reduceIte]
    rw [← hsplice]
    exact hwhole f

/-- #1809 adapter: a Profile that holds on every selector-admitted history is
itself suffix-complete and universally projected on its own cell, so the
existing Profile-cell certificate applies to it. -/
theorem wholeSuffix_profile (allowed : Trace → Prop) (n : Nat) (q : Profile)
    (hwhole : WholeSuffixRich allowed n)
    (hproj : ∀ f, Admitted allowed n f → Follows q f) :
    SuffixComplete q n ∧ UniversalProjection q q n :=
  ⟨fun tail => ⟨hproj _ (hwhole tail), (hwhole tail).1.2⟩, fun _ hf => hf.1⟩

/-- Composed with #1809's `certificate` (sixth conjunct): a Profile holding on
every selector-admitted history permits every later state pair. -/
theorem wholeSuffix_future_total (allowed : Trace → Prop) (n : Nat)
    (q : Profile) (hwhole : WholeSuffixRich allowed n)
    (hproj : ∀ f, Admitted allowed n f → Follows q f) :
    ∀ t a b, n+1 ≤ t → q.step t a b := by
  obtain ⟨hc, hu⟩ := wholeSuffix_profile allowed n q hwhole hproj
  exact TruthCore.Results.Explanation.NoFoundationLawChaos.certificate.2.2.2.2.2.1
    n q q hc hu

/-- Composed with #1809's `certificate` (eighth conjunct): no deterministic
Profile holds on every selector-admitted history. -/
theorem wholeSuffix_no_deterministic (allowed : Trace → Prop) (n : Nat)
    (q : Profile) (hwhole : WholeSuffixRich allowed n)
    (hdet : Deterministic q) :
    ¬ ∀ f, Admitted allowed n f → Follows q f := by
  intro hproj
  obtain ⟨hc, hu⟩ := wholeSuffix_profile allowed n q hwhole hproj
  exact TruthCore.Results.Explanation.NoFoundationLawChaos.certificate.2.2.2.2.2.2.2.1
    n q q hc hdet hu

/-- Composed with #1809's `certificate` (fifth conjunct): no record-only
estimator is exactly correct at a later index on every selector-admitted
history. -/
theorem wholeSuffix_no_forecast (allowed : Trace → Prop) (n k : Nat)
    (predict : Trace → Bool) (hk : n+1 ≤ k)
    (hwhole : WholeSuffixRich allowed n) (hrecord : UsesRecord n predict) :
    ¬ ∀ f, Admitted allowed n f → predict f = f k := by
  intro hall
  have hcert := TruthCore.Results.Explanation.NoFoundationLawChaos.certificate
  exact hcert.2.2.2.2.1 n k (openFuture n) predict hk (hcert.2.1 n) hrecord
    (fun f hf => hall f ((wholeSuffix_admitted_iff allowed n hwhole f).2 hf))

theorem splice_on (n : Nat) : splice n (fun _ => true) = on := by
  funext t
  show (if t < n+1 then true else true) = true
  by_cases ht : t < n+1
  · simp only [ht, ↓reduceIte]
  · simp only [ht, ↓reduceIte]

theorem splice_delayedFailure (n : Nat) :
    splice n (delayedFailure (n+1)) = delayedFailure (n+1) := by
  funext t
  show (if t < n+1 then true else delayedFailure (n+1) t) = delayedFailure (n+1) t
  by_cases ht : t < n+1
  · simp only [ht, ↓reduceIte]
    show true = (if t < n+1 then true else false)
    simp only [ht, ↓reduceIte]
  · simp only [ht, ↓reduceIte]

/-- The stance whose admitted continuations at each cutoff are exactly the
selector-admitted histories. Its entitlement predicate is supplied freely. -/
def selectorStance (allowed : Trace → Prop) (entitled : Claim → Prop) :
    Stance where
  admits := fun n f => Admitted allowed n f
  entitled := entitled

/-- #1808 adapter: whole-suffix richness of one fixed selector at every
cutoff gives #1808's `BothSuccessors` for the selector's stance. -/
theorem selector_bothSuccessors (allowed : Trace → Prop)
    (entitled : Claim → Prop) (hwhole : ∀ n, WholeSuffixRich allowed n) :
    BothSuccessors (selectorStance allowed entitled) := by
  intro n
  refine ⟨?_, ?_⟩
  · have h := hwhole n (fun _ => true)
    rw [splice_on n] at h
    exact h
  · have h := hwhole n (delayedFailure (n+1))
    rw [splice_delayedFailure n] at h
    exact h

/-- Composed with #1808's `internalDiscipline`: such a stance that endorses
its own strict norm cannot hold any positive strict entitlement. -/
theorem selector_internalDiscipline (allowed : Trace → Prop)
    (entitled : Claim → Prop) (hwhole : ∀ n, WholeSuffixRich allowed n) :
    ((strictNorm (selectorStance allowed entitled)).Holds
        (selectorStance allowed entitled).entitled →
      ∀ c, ¬ (selectorStance allowed entitled).entitled c) ∧
    ((∃ c, (selectorStance allowed entitled).entitled c) →
      ¬ (strictNorm (selectorStance allowed entitled)).Holds
        (selectorStance allowed entitled).entitled) :=
  TruthCore.Results.Epistemology.NoFoundationPractice.internalDiscipline _
    (selector_bothSuccessors allowed entitled hwhole)

/-- The satisfiers of one fixed local Profile form a prefix-closed selector:
any failure of `Follows q` occurs at time zero or at one finite successor
pair, so it is witnessed by a finite prefix. -/
theorem follows_prefixClosed (q : Profile) (n : Nat) :
    PrefixClosed (Follows q) n := by
  intro f _ hmatch
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg, hagree⟩ := hmatch 0
    exact (hagree 0 (Nat.le_refl _)).symm.trans hg.2.1
  · intro t
    obtain ⟨g, hg, hagree⟩ := hmatch (t+1)
    have hstep := hg.2.2 t
    rw [hagree t (by omega), hagree (t+1) (Nat.le_refl _)] at hstep
    exact hstep

end TruthCore.Results.Explanation.NoFoundationLawChaos.Adapters
