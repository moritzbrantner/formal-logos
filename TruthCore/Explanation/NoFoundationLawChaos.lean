module

public import TruthCore.Explanation.LawActuality

/-! Unrestricted future transition alternatives and global law projection.

This is an ontic *conditional* on a supplied set of admissible complete paths,
not a derivation of that set from the absence of ultimate explanation. The
observed prefix, the law profile and the represented presence history reuse
#737/#743. No modal admissibility, physical actuality or grounding relation is
defined by the Boolean traces. See `docs/notes/no-foundation-law-chaos.md`.
-/

@[expose] public section

namespace TruthCore.Explanation.NoFoundationLawChaos
open TruthCore.Modern.Hume.Induction
open TruthCore.Modern.Hume.Regularity
open TruthCore.Epistemology.UltimateExplanation
open TruthCore.Explanation.LawActuality
open TruthCore.Modal.TemporalHistory
open TruthCore.Modal.HistoryContrastive

/-- Preserve the entire recorded `true` prefix, while assigning an *arbitrary*
complete suffix. This permits late flips, repetitions and irregular patterns;
it is not a probabilistic or causal process. -/
def splice (n : Nat) (tail : Trace) : Trace :=
  fun t => if t < n+1 then true else tail t

/-- Every complete Boolean suffix is admitted after the fixed actual record.
It is the decisive EXTRA ontic-admissibility assumption, not a consequence of
`¬ GroundedTotality`. An admitted path need not be the actual path. -/
def SuffixComplete (p : Profile) (n : Nat) : Prop :=
  ∀ tail : Trace, Cell p on n (splice n tail)

/-- This *one* law profile holds on EVERY admitted whole path, not just the
actual path or the record. It is an all-alternatives universal projection,
stronger than a true scientific law interpreted as applying only to actuality. -/
def UniversalProjection (p q : Profile) (n : Nat) : Prop :=
  ∀ f, Cell p on n f → Follows q f

/-- Exact, all-admitted-path correctness at a specified future time. #743's
`UsesRecord` is the independent constraint that an estimator sees no more
than the common finite observed prefix. No chance or fallible warrant appears. -/
def UniformForecast (p : Profile) (n k : Nat) (predict : Trace → Bool) : Prop :=
  ∀ f, Cell p on n f → predict f = f k

/-- A candidate law forbids even one transition at a fully unobserved time.
Initial-state and past constraints are deliberately not counted. -/
def FutureExclusion (q : Profile) (n : Nat) : Prop :=
  ∃ t a b, n+1 ≤ t ∧ ¬ q.step t a b

/-- The very weak law retaining only the observed initial condition: all
future transitions remain allowed. A nontrivial non-deterministic control. -/
def unconstrained : Profile := ⟨true, fun _ _ _ => True⟩

/-- Mathematical presence for EVERY complete trace-world: at each time exactly
one Boolean state is present; `ExistsAt` agrees at now=0. This represents
states, NOT a persistent concrete bearer or efficient causes. -/
def realized : History Trace Bool Nat where
  ontic := { frame := ⟨fun _ _ => True⟩
             ExistsAt := fun f b => b = f 0
             Causes := fun _ _ _ => False }
  IsAt := fun f b t => b = f t
  now := 0

/-- A *law schedule* chooses the copy transition when false and the toggle
transition when true. Each fixed complete schedule is an ordinary deterministic
time-dependent profile; what fixes the schedule is a separate question. -/
def scheduled (switches : Nat → Bool) : Profile :=
  ⟨true, fun t a b => b = if switches t then !a else a⟩

/-- The unique trace generated from the initial true state by this schedule. -/
def generated (switches : Nat → Bool) : Trace :=
  fun t => Nat.rec true (fun i prior => if switches i then !prior else prior) t

def copySchedule : Nat → Bool := fun _ => false
def toggleFrom (k : Nat) (t : Nat) : Bool := decide (k ≤ t)

/-- Ex-post transition-code extraction: it is deliberately a function of the
FULL path, not a grounded law or an observation-based justification. -/
def scheduleOf (f : Trace) (t : Nat) : Bool := f (t+1) != f t

/-- General law-stability boundary. The iff is an exact characterization:
unrestricted futures force EVERY later state-pair to be permitted by any
universal candidate law, independently of its time dependence. An unrestricted
future cannot retain an all-history deterministic transition rule. -/
def Certificate : Prop :=
  (∀ n f, Cell (openFuture n) on n f ↔
    ∀ i, i < n+1 → f i = true) ∧
  (∀ n, SuffixComplete (openFuture n) n) ∧
  (CoherentAtNow realized ∧ ∀ f t, ∃! b, realized.IsAt f b t) ∧
  (∀ n k, n+1 ≤ k → ∃ f g : Trace,
    Cell (openFuture n) on n f ∧ Cell (openFuture n) on n g ∧
    (∀ i, i < n+1 → f i = g i) ∧ f k ≠ g k ∧
    ¬ SameHistory realized f g) ∧
  (∀ n k p (predict : Trace → Bool), n+1 ≤ k →
    SuffixComplete p n → UsesRecord n predict →
    ¬ UniformForecast p n k predict) ∧
  (∀ n p q, SuffixComplete p n → UniversalProjection p q n →
    ∀ t a b, n+1 ≤ t → q.step t a b) ∧
  (∀ n p q, SuffixComplete p n → FutureExclusion q n →
    ¬ UniversalProjection p q n) ∧
  (∀ n p q, SuffixComplete p n → Deterministic q →
    ¬ UniversalProjection p q n) ∧
  (∀ n q, UniversalProjection (openFuture n) q n ↔
    q.initial = true ∧
    (∀ t, t < n → q.step t true true) ∧
    (∀ b, q.step n true b) ∧
    (∀ t a b, n+1 ≤ t → q.step t a b))

/-- Fully deterministic laws themselves can change at any arbitrarily late
date while sharing the earlier observation record. Every whole path with the
given initial state has an ex-post deterministic copy/toggle schedule, but
this coding does not confer causal or explanatory primacy on that schedule. -/
def LawSwitch : Prop :=
  (∀ switches, Deterministic (scheduled switches) ∧
    Follows (scheduled switches) (generated switches) ∧
    ∀ f, Follows (scheduled switches) f → f = generated switches) ∧
  (∀ f, f 0 = true → Follows (scheduled (scheduleOf f)) f) ∧
  (∀ n k, n ≤ k →
    Cell (openFuture n) on n (generated (toggleFrom k)) ∧
    Cell (openFuture n) on n (generated copySchedule) ∧
    (∀ t, t < k → ∀ a b,
      (scheduled copySchedule).step t a b ↔
      (scheduled (toggleFrom k)).step t a b) ∧
    (scheduled copySchedule).step k true true ∧
    ¬ (scheduled (toggleFrom k)).step k true true ∧
    generated (toggleFrom k) (k+1) = false ∧
    generated copySchedule (k+1) = true)

/-- A SINGLE unchanged rival's admissible whole paths: it permits exactly
those with initial true, equivalently the union of individually deterministic
copy/toggle-schedule solutions. The arbitrary path itself determines a schedule
EX POST; nothing establishes that this schedule explains its own actuality.
This fixes the modal quantifier across every possible observation cutoff. -/
def OneRival : Prop :=
  (∀ f, (f 0 = true ↔ ∃ switches, Follows (scheduled switches) f)) ∧
  (∀ n, SuffixComplete unconstrained n) ∧
  (∀ n f, Cell unconstrained on n f ↔
    (∃ switches, Follows (scheduled switches) f) ∧
    ∀ i, i < n+1 → f i = true) ∧
  (∀ n q, Deterministic q → ¬ UniversalProjection unconstrained q n)

/-- Nonvacuous/stable and omitted-premise controls: a law can hold on a
populated stable set; complete suffix freedom does not eliminate the actual
stable continuation. The empty-cell impostor would make *any* law vacuously
universal. `brute` has no totality ground yet admits the stable law; `grounded`
has a totality ground yet may be paired with the open future. Thus missing
ultimate ground alone does NOT imply suffix freedom in this product model. -/
def impossible : Profile := ⟨false, stable.step⟩

def Omissions : Prop :=
  (∀ n, Cell stable on n on ∧ UniversalProjection stable stable n ∧
    ¬ SuffixComplete stable n) ∧
  (∀ n, Cell (openFuture n) on n on ∧ Follows stable on ∧
    UniversalProjection (openFuture n) unconstrained n ∧
    ¬ Deterministic unconstrained) ∧
  (∀ n, (¬ ∃ f, Cell impossible on n f) ∧
    ∀ q, UniversalProjection impossible q n) ∧
  (∀ n, ¬ GroundedTotality brute ∧ GroundedTotality grounded ∧
    ¬ SuffixComplete stable n ∧ SuffixComplete (openFuture n) n)


/-! ## Finite recombination versus completed infinite futures

An admitted *complete-history selector* is separate from the local Profile:
being compatible with a transition rule does not settle which infinite paths
are metaphysically available. The same observed all-true prefix and Trace
domain are used in the existing chaos certificate. -/

/-- A fixed global selector further restricts #737's populated record cell.
It is not a grounding predicate or a metaphysical possibility operator. -/
def Admitted (allowed : Trace → Prop) (n : Nat) (f : Trace) : Prop :=
  Cell (openFuture n) on n f ∧ allowed f

/-- Any admitted complete history can be copied through m and extended by
either chosen next bit, while keeping the same globally admitted class.
The case m<n is already fixed by the observed record and is excluded. -/
def OneStepRich (allowed : Trace → Prop) (n : Nat) : Prop :=
  ∀ m f b, n ≤ m → Admitted allowed n f →
    ∃ g, Admitted allowed n g ∧
      (∀ t, t ≤ m → g t = f t) ∧ g (m+1) = b

/-- Every prescribed *finite* initial segment of any suffix has an admitted
complete extension. The extension may depend on the finite cutoff. -/
def FiniteRich (allowed : Trace → Prop) (n : Nat) : Prop :=
  ∀ tail m, ∃ g, Admitted allowed n g ∧
    ∀ t, t ≤ m → g t = splice n tail t

/-- A genuine closure commitment on the admitted complete-history set:
every prefix of a candidate is realized by some allowed complete history,
so the candidate itself is allowed. Closure and finite richness are independent:
neither implies the other; their conjunction yields whole-suffix richness. -/
def PrefixClosed (allowed : Trace → Prop) (n : Nat) : Prop :=
  ∀ f, Cell (openFuture n) on n f →
    (∀ m, ∃ g, Admitted allowed n g ∧
      ∀ t, t ≤ m → g t = f t) →
    allowed f

/-- Every prescribed complete infinite suffix is admitted, now relative to
the fixed selector, not inferred from absence of ultimate explanation. -/
def WholeSuffixRich (allowed : Trace → Prop) (n : Nat) : Prop :=
  ∀ tail, Admitted allowed n (splice n tail)

/-- Finite-switching histories: after some finite stage all values agree.
The bound and final value vary between admitted complete histories. -/
def EventuallyConstant (f : Trace) : Prop :=
  ∃ k b, ∀ t, k ≤ t → f t = b

def finiteSwitchClass : Trace → Prop := EventuallyConstant
def stableOnlyClass : Trace → Prop := fun f => f = on
def allHistoryClass : Trace → Prop := fun _ => True
def emptyHistoryClass : Trace → Prop := fun _ => False

/-- Exact upstream entailment and omission controls.
Populated one-step recombination gives all finite patterns; prefix closure
additionally gives all *infinite* suffixes. The eventually-constant class has
the former without the latter. The stable class is closed but not rich.
The unrestricted class has both. The empty class exposes the independent
nonemptiness condition. Nothing here states that foundationlessness entails
any one selector, epistemic norm, or actual physical law freedom. -/
def RecombinationFork : Prop :=
  (∀ (allowed : Trace → Prop) n, (∃ f, Admitted allowed n f) →
    OneStepRich allowed n → FiniteRich allowed n) ∧
  (∀ (allowed : Trace → Prop) n, FiniteRich allowed n →
    PrefixClosed allowed n → WholeSuffixRich allowed n) ∧
  (∀ n, (∃ f, Admitted finiteSwitchClass n f) ∧
    OneStepRich finiteSwitchClass n ∧
    FiniteRich finiteSwitchClass n ∧
    ¬ PrefixClosed finiteSwitchClass n ∧
    ¬ WholeSuffixRich finiteSwitchClass n) ∧
  (∀ n, (∃ f, Admitted stableOnlyClass n f) ∧
    PrefixClosed stableOnlyClass n ∧
    ¬ FiniteRich stableOnlyClass n ∧
    ¬ WholeSuffixRich stableOnlyClass n) ∧
  (∀ n, (∃ f, Admitted allHistoryClass n f) ∧
    OneStepRich allHistoryClass n ∧
    FiniteRich allHistoryClass n ∧
    PrefixClosed allHistoryClass n ∧
    WholeSuffixRich allHistoryClass n) ∧
  (∀ n, (¬ ∃ f, Admitted emptyHistoryClass n f) ∧
    OneStepRich emptyHistoryClass n ∧
    PrefixClosed emptyHistoryClass n ∧
    ¬ WholeSuffixRich emptyHistoryClass n)

end TruthCore.Explanation.NoFoundationLawChaos
