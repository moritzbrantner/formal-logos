module

public import TruthCore.Explanation.BinaryLaw
public import TruthCore.Explanation.PSRLaterAxes
public import TruthCore.Modal.SelectedEffectBridge
public import TruthCore.Modal.STIT

/-!
# Objective probability laws: determination, the law fork and realization (#2151)

Analyst formulations, attribution deferred. A probability law is a Mathlib
`PMF` on physical outcomes: mathematical data, not a causal power and not a
measure over metaphysical worlds. Three diagnostics for the will step of
#2145 (`66aecdd7`, `4be0f774`):

1. **Determination.** What fixes a law uniquely without an agent?
   A transitive symmetry group fixes exactly one invariant law; a group with
   two orbits leaves the orbit masses free. A binary Markov kernel has a
   stationary law exactly when a real balance equation holds; positive
   switching makes it unique, zero switching leaves every law stationary.
   Uniqueness is not convergence: under the flip kernel the unique
   stationary law is never reached from a point mass. A mixture of
   invariant laws is invariant; distinct components make the mixture
   injective in its upper law, equal components erase it.
2. **The law fork.** Under the contingent-fact PSR of `PSRStrength`, a fact
   whose obtaining tracks the value of a selected law is either constant
   across accessible worlds (then it is not contingent and the PSR makes no
   demand) or has an admitted reason. The same theorem applies to a personal
   selector's adopted content: the demand is symmetric. An admitted reason
   need not fix the law.
3. **Realization and sample.** The same PMF support matches the output table
   of #462's `varying` profile and of the same profile with its causal edges
   removed; only the first realizes its outputs causally. In a STIT cell,
   seeing to it that a law is adopted is compatible with seeing to neither
   the particular sample nor its contrary.

The emptied profile is a structural independence control, NOT a countermodel
to an actual intrinsically productive disposition. Nothing here establishes
that a necessary source does or does not ground a particular law, or that
the impersonal account is defeated. See `docs/notes/objective-probability.md`.
-/

@[expose] public section

namespace TruthCore.Explanation.ObjectiveProbability

open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.BinaryLaw
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.STIT
open scoped ENNReal

/-! ## 1. Determination of a law by symmetry, stationarity and mixture -/

/-- `μ` gives the same mass to `x` and to its image under every `g ∈ G`. -/
def Invariant {E : Type} (G : Set (Equiv.Perm E)) (μ : PMF E) : Prop :=
  ∀ g ∈ G, ∀ x, μ (g x) = μ x

/-- `G` has one orbit: every outcome is carried to every outcome. -/
def ActsTransitively {E : Type} (G : Set (Equiv.Perm E)) : Prop :=
  ∀ x y, ∃ g ∈ G, g x = y

/-- The uniform law on a finite nonempty type, as a `PMF`. Hand-rolled because
the pinned Mathlib deprecates `PMF.uniformOfFintype` in favour of a uniform
`Measure`, and the controls below compose laws by `PMF.bind`. -/
noncomputable def uniformLaw (E : Type) [Fintype E] [Nonempty E] : PMF E :=
  PMF.ofFintype (fun _ => (Fintype.card E : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _))

/-- Flip the second coordinate and keep the first. -/
def flipSecond : Equiv.Perm (Bool × Bool) where
  toFun x := (x.1, !x.2)
  invFun x := (x.1, !x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- The group `{id, flipSecond}`: two orbits, distinguished by the first coordinate. -/
def firstPreserving : Set (Equiv.Perm (Bool × Bool)) := {1, flipSecond}

/-- Mass `p` spread evenly over the orbit with first coordinate `true`,
mass `q` over the other orbit. -/
noncomputable def orbitLaw (p q : ℝ≥0∞) (h : p + q = 1) : PMF (Bool × Bool) :=
  PMF.ofFintype (fun x => if x.1 then p / 2 else q / 2) (by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, ite_false,
      ENNReal.add_halves, Bool.false_eq_true]
    exact h)

/-- `μ` is unchanged by one step of the kernel `K`. -/
def Stationary {E : Type} (K : E → PMF E) (μ : PMF E) : Prop := μ.bind K = μ

/-- One step of the kernel. -/
noncomputable def step {E : Type} (K : E → PMF E) (μ : PMF E) : PMF E := μ.bind K

/-- Switching probability out of `true`, as a real number. -/
noncomputable def switchOut (K : Bool → PMF Bool) : ℝ := (K true false).toReal

/-- Switching probability into `true`, as a real number. -/
noncomputable def switchIn (K : Bool → PMF Bool) : ℝ := (K false true).toReal

/-- Balance: with `x = μ(true)`, `x · (out + in) = in`. -/
def Balance (K : Bool → PMF Bool) (μ : PMF Bool) : Prop :=
  (μ true).toReal * (switchOut K + switchIn K) = switchIn K

/-- Stay put: zero switching. -/
noncomputable def identityKernel : Bool → PMF Bool := PMF.pure

/-- Always move to `true`. -/
noncomputable def resetKernel : Bool → PMF Bool := fun _ => PMF.pure true

/-- Always switch. -/
noncomputable def flipKernel : Bool → PMF Bool := fun b => PMF.pure (!b)

/-- Three quarters on the outcome `high`, one quarter on the other. -/
noncomputable def favoring (high : Bool) : PMF Bool :=
  binaryLaw (if high then 3 / 4 else 1 / 4) (if high then 1 / 4 else 3 / 4) (by
    have h : (3 : ℝ≥0∞) / 4 + 1 / 4 = 1 := by
      rw [← ENNReal.add_div, show (3 : ℝ≥0∞) + 1 = 4 by norm_num]
      exact ENNReal.div_self (by norm_num) (by norm_num)
    cases high
    · simpa [add_comm] using h
    · simpa using h)

/-- Symmetry, stationarity and mixture: when a law is uniquely fixed by
structure alone, and when it is not. -/
def LawDeterminationControls : Prop :=
  -- transitive symmetry fixes exactly one invariant law, the uniform one
  (∀ (E : Type) [Fintype E] [Nonempty E] (G : Set (Equiv.Perm E)),
    ActsTransitively G → ∃! μ : PMF E, Invariant G μ) ∧
  (∀ (E : Type) [Fintype E] [Nonempty E] (G : Set (Equiv.Perm E)),
    ActsTransitively G → ∀ μ : PMF E, Invariant G μ →
      ∀ x, μ x = (Fintype.card E : ℝ≥0∞)⁻¹) ∧
  -- two orbits: every positive orbit mass gives an invariant full-support law,
  -- and different orbit masses give different laws
  ¬ ActsTransitively firstPreserving ∧
  (∀ (p q : ℝ≥0∞) (h : p + q = 1), 0 < p → 0 < q →
    Invariant firstPreserving (orbitLaw p q h) ∧ ∀ x, 0 < orbitLaw p q h x) ∧
  (∀ (p q p' q' : ℝ≥0∞) (h : p + q = 1) (h' : p' + q' = 1),
    orbitLaw p q h = orbitLaw p' q' h' → p = p') ∧
  (∃ μ ν : PMF (Bool × Bool), Invariant firstPreserving μ ∧
    Invariant firstPreserving ν ∧ (∀ x, 0 < μ x ∧ 0 < ν x) ∧ μ ≠ ν) ∧
  -- binary stationarity
  (∀ (K : Bool → PMF Bool) (μ : PMF Bool), Stationary K μ ↔ Balance K μ) ∧
  (∀ K : Bool → PMF Bool, 0 < switchOut K + switchIn K →
    ∃! μ : PMF Bool, Stationary K μ) ∧
  (∀ K : Bool → PMF Bool, switchOut K + switchIn K = 0 →
    ∀ μ : PMF Bool, Stationary K μ) ∧
  (∃ μ ν : PMF Bool, μ ≠ ν ∧ Stationary identityKernel μ ∧ Stationary identityKernel ν) ∧
  (∀ μ : PMF Bool, Stationary resetKernel μ ↔ μ = PMF.pure true) ∧
  (∃! μ : PMF Bool, Stationary flipKernel μ) ∧
  -- uniqueness is not convergence: the flip orbit of a point mass never
  -- reaches the unique stationary law, and returns after two steps
  (∀ n : Nat, ¬ Stationary flipKernel ((step flipKernel)^[n] (PMF.pure true))) ∧
  step flipKernel (step flipKernel (PMF.pure true)) = PMF.pure true ∧
  step flipKernel (PMF.pure true) ≠ PMF.pure true ∧
  -- mixtures
  (∀ (I E : Type) (G : Set (Equiv.Perm E)) (π : PMF I) (ν : I → PMF E),
    (∀ i, Invariant G (ν i)) → Invariant G (π.bind ν)) ∧
  (∀ ν : Bool → PMF Bool, ν true true ≠ ν false true →
    Function.Injective (fun π : PMF Bool => π.bind ν)) ∧
  (∀ (I E : Type) (ρ : PMF E) (π π' : PMF I),
    π.bind (fun _ => ρ) = π'.bind (fun _ => ρ)) ∧
  -- the slice's worked mixture: components with mass 3/4 and 1/4 at `true`
  -- give lower mass 1/4 + t/2, where t is the upper law's mass at `true`
  (∀ π : PMF Bool, ((π.bind favoring) true).toReal = 1 / 4 + (π true).toReal / 2)

/-! ## 2. The law fork under the contingent-fact PSR -/

/-- The fact `f` holds at `w` exactly when the selected value at `w` is the
value at `a`. With `sel` a law, `f` is the obtaining of the actual law; with
`sel` a selector's adopted content, `f` is the obtaining of that adoption. -/
def TracksValue {W B F X : Type} (A : Arena W B F) (f : F) (sel : W → X) (a : W) : Prop :=
  ∀ w, A.holds w f ↔ sel w = sel a

/-- The reason `r` fixes the selected value: wherever `r` holds at an
accessible world, the value is the actual one. Determination of a law, not
necessitation of its outcomes. -/
def FixesValue {W B F X : Type} (A : Arena W B F) (sel : W → X) (a : W) (r : F) : Prop :=
  ∀ v, Access A a v → A.holds v r → sel v = sel a

/-- Physical law, epistemic credence and an observed finite record, kept apart. -/
structure LawProfile (W O : Type) where
  law : W → PMF O
  credence : W → PMF O
  record : W → List O

/-- Likelihood of an ordered finite record under independent identical trials.
The product rule is a model assumption, not derived from frequencies. -/
noncomputable def iidLikelihood {O : Type} (μ : PMF O) : List O → ℝ≥0∞
  | [] => 1
  | x :: xs => μ x * iidLikelihood μ xs

/-- Two contexts with the same credence and the same record; the law differs. -/
noncomputable def matched (xs : List Bool) : LawProfile Bool Bool where
  law := favoring
  credence _ := favoring true
  record _ := xs

/-- Facts of the matched arena: a base fact true everywhere, and the
obtaining of the actual law (true only at the context `true`). -/
inductive LawFact | base | actualLaw deriving DecidableEq

/-- The matched arena, with or without the base fact admitted as a reason
for the actual law. No causal relation, no beings. -/
def lawArena (reason : Bool) : Arena Bool Empty LawFact :=
  basic everywhere
    (fun w f => match f with
      | .base => True
      | .actualLaw => w = true)
    (fun _ r f => reason = true ∧ r = .base ∧ f = .actualLaw)
    (fun r f => r = f)

/-- The fork, applied symmetrically to an impersonal law and to a personal
selector's adoption, and its two controls. -/
def LawSelectionFork : Prop :=
  -- the fork, for any selected value
  (∀ (W B F X : Type) (A : Arena W B F) (f : F) (sel : W → X) (a : W),
    TracksValue A f sel a → ContingentPSR A a →
      (∀ v, Access A a v → sel v = sel a) ∨
      ((∃ v, Access A a v ∧ sel v ≠ sel a) ∧ Explained A a f)) ∧
  -- a value constant across accessible worlds makes its fact non-contingent
  (∀ (W B F X : Type) (A : Arena W B F) (f : F) (sel : W → X) (a : W),
    TracksValue A f sel a → (∀ v, Access A a v → sel v = sel a) → ¬ Contingent A a f) ∧
  -- symmetry: an operating law that is a selector's adopted law; if it varies,
  -- both the law and the adoption need an admitted reason
  (∀ (W B F O : Type) (A : Arena W B F) (law adopt : F) (laws adopted : W → PMF O) (a : W),
    TracksValue A law laws a → TracksValue A adopt adopted a → (∀ w, laws w = adopted w) →
    ContingentPSR A a → (∃ v, Access A a v ∧ laws v ≠ laws a) →
      Explained A a law ∧ Explained A a adopt) ∧
  -- matched contexts: same record and credence, different law; neither
  -- law makes any finite record impossible
  (∀ xs : List Bool,
    let L := matched xs
    L.record true = L.record false ∧ L.credence true = L.credence false ∧
    L.law true ≠ L.law false ∧
    iidLikelihood (L.law true) xs ≠ 0 ∧ iidLikelihood (L.law false) xs ≠ 0 ∧
    (∀ r, TracksValue (lawArena r) .actualLaw L.law true) ∧
    Contingent (lawArena false) true .actualLaw ∧
    ¬ ContingentPSR (lawArena false) true ∧
    ContingentPSR (lawArena true) true ∧
    (lawArena true).explains true .base .actualLaw ∧
    ¬ FixesValue (lawArena true) L.law true .base)

/-! ## 3. Realization and sample -/

/-- #462's `varying` profile with every causal edge removed. Same source,
existence table, act and output table. -/
def emptied : OutputProfile Bool EffectBeing Unit where
  ontic := { frame := alternatingEffects.frame
             ExistsAt := alternatingEffects.ExistsAt
             Causes := fun _ _ _ => False }
  source := varying.source
  performs := varying.performs
  output := varying.output

/-- A law on world labels, read as a law on the effects `some w`. -/
noncomputable def outputLaw (μ : PMF Bool) : PMF EffectBeing := μ.map some

/-- The support of the law is exactly the set of outputs of the act. -/
def SupportMatches {W B : Type} (p : OutputProfile W B Unit) (ℓ : PMF B) : Prop :=
  ∀ x, x ∈ ℓ.support ↔ ∃ v, p.output v () x

/-- Histories `(adopted, sample)`; one agent at one moment, whose choice
cells are fixed by the adoption coordinate. -/
def lawFrame : BranchingFrame Unit (Bool × Bool) Unit where
  traverses _ _ := True
  choice _ _ := Setoid.ker fun h => h.val.1

def lawHistory (adopted sample : Bool) : lawFrame.Through () := ⟨(adopted, sample), trivial⟩

/-- The law is adopted on this history. -/
def LawAdopted (h : lawFrame.Through ()) : Prop := h.val.1 = true

/-- The particular sample on this history is `true`. -/
def SampleTrue (h : lawFrame.Through ()) : Prop := h.val.2 = true

/-- Support does not settle productive realization; adopting a law does not
settle its sample. -/
def RealizationSampleControls : Prop :=
  (∀ μ : PMF Bool, (∀ b, 0 < μ b) →
    SupportMatches varying (outputLaw μ) ∧ SupportMatches emptied (outputLaw μ)) ∧
  emptied.source = varying.source ∧
  (∀ v x, emptied.ontic.ExistsAt v x ↔ varying.ontic.ExistsAt v x) ∧
  (∀ v, emptied.performs v () ↔ varying.performs v ()) ∧
  (∀ v x, emptied.output v () x ↔ varying.output v () x) ∧
  RealizedOutputs varying ∧ ¬ RealizedOutputs emptied ∧
  -- general STIT: seeing to a law, with a history in the same cell where
  -- the effect fails, excludes seeing to the effect
  (∀ (M H A : Type) (F : BranchingFrame M H A) (m : M) (a : A) (h k : F.Through m)
    (law effect : F.Through m → Prop),
    Dstit a h law → (F.choice m a).r h k → ¬ effect k → ¬ Cstit a h effect) ∧
  Dstit () (lawHistory true true) LawAdopted ∧
  SampleTrue (lawHistory true true) ∧
  ¬ Cstit () (lawHistory true true) SampleTrue ∧
  ¬ Cstit () (lawHistory true true) (fun h => ¬ SampleTrue h)

end TruthCore.Explanation.ObjectiveProbability
