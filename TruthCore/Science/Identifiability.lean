module

public import TruthCore.Logic.InformationInvariance
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Setoid.Basic

/-! Exact recoverability of a target on a specified model class. Use a subtype
of models to restrict an admissibility profile. Identification here concerns
equality of supplied outputs and carries no estimator, probability across
models, or warrant for the profile. -/

@[expose] public section

namespace TruthCore.Science.Identifiability

variable {M O T I R : Type*}

/-- The target is constant on every attained observation fiber. -/
def Identifies (observe : M → O) (target : M → T) : Prop :=
  ∀ m n, observe m = observe n → target m = target n

/-- Every and only target value attained by models returning this observation.
An unattained observation has an empty identified set. -/
def identifiedSet (observe : M → O) (target : M → T) (o : O) : Set T :=
  target '' (observe ⁻¹' {o})

/-- Quotient elimination needs fiber constancy and uses no representative choice. -/
def quotientFactor (observe : M → O) (target : M → T)
    (h : Identifies observe target) : Quotient (Setoid.ker observe) → T :=
  Quotient.lift target h

/-- Range recovery uses Mathlib's classical quotient–range equivalence. -/
noncomputable def rangeFactor (observe : M → O) (target : M → T)
    (h : Identifies observe target) : Set.range observe → T :=
  quotientFactor observe target h ∘ (Setoid.quotientKerEquivRange observe).symm

theorem rangeFactor_apply (observe : M → O) (target : M → T)
    (h : Identifies observe target) (m : M) :
    rangeFactor observe target h ⟨observe m, ⟨m, rfl⟩⟩ = target m := by
  have eq : Setoid.quotientKerEquivRange observe ⟦m⟧ = ⟨observe m, ⟨m, rfl⟩⟩ :=
    Subtype.ext rfl
  rw [rangeFactor, Function.comp_apply, ← eq, Equiv.symm_apply_apply]
  rfl

theorem range_factor_iff (observe : M → O) (target : M → T) :
    (∃! recover : Set.range observe → T, ∀ m,
      recover ⟨observe m, ⟨m, rfl⟩⟩ = target m) ↔ Identifies observe target := by
  constructor
  · rintro ⟨recover, h, _⟩ m n same
    exact (h m).symm.trans ((congrArg recover (Subtype.ext same)).trans (h n))
  · intro h
    refine ⟨rangeFactor observe target h, rangeFactor_apply observe target h, ?_⟩
    intro recover hRecover
    funext ⟨_, m, rfl⟩
    exact (hRecover m).trans (rangeFactor_apply observe target h m).symm

/-- On the ambient observation type, off-range values can be assigned
arbitrarily. If it is inhabited, a total decoder requires an inhabited target
type even when no model is admitted. A surjective observation map requires no
off-range default. This statement concerns functions of sets, with no
measurability or effective computation guarantee. -/
theorem total_factor_iff (observe : M → O) (target : M → T) :
    (∃ recover : O → T, ∀ m, recover (observe m) = target m) ↔
      Identifies observe target ∧ (Nonempty T ∨ IsEmpty O) := by
  classical
  constructor
  · rintro ⟨recover, h⟩
    refine ⟨fun m n same => (h m).symm.trans ((congrArg recover same).trans (h n)), ?_⟩
    rcases isEmpty_or_nonempty O with empty | inhabited
    · exact Or.inr empty
    · obtain ⟨o⟩ := inhabited
      exact Or.inl ⟨recover o⟩
  · rintro ⟨h, inhabited | empty⟩
    · obtain ⟨fallback⟩ := inhabited
      refine ⟨fun o => if ho : o ∈ Set.range observe then
        rangeFactor observe target h ⟨o, ho⟩ else fallback, ?_⟩
      intro m
      simpa only [dite_eq_left (Set.mem_range_self m)] using rangeFactor_apply observe target h m
    · exact ⟨fun o => (empty.false o).elim, fun m => (empty.false (observe m)).elim⟩

/-- The pre-existing constructive proposition test remains available without
asking for equality of propositions. -/
theorem proposition_criterion_iff (observe : M → O) (p : M → Prop) :
    (∃ criterion : O → Prop, ∀ m, criterion (observe m) ↔ p m) ↔
      Identifies observe p := by
  rw [Logic.InformationInvariance.factor_iff]
  exact ⟨fun h m n same => propext (h m n same), fun h m n same => (by rw [h m n same])⟩

theorem identified_singleton_iff (observe : M → O) (target : M → T) :
    (∀ m, identifiedSet observe target (observe m) = {target m}) ↔ Identifies observe target := by
  constructor
  · intro h m n same
    have mem : target n ∈ identifiedSet observe target (observe m) := ⟨n, same.symm, rfl⟩
    rw [h m] at mem
    exact mem.symm
  · intro h m
    ext t
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact h n m hn
    · intro ht
      exact ⟨m, rfl, ht.symm⟩

/-- Restriction can shrink the identified set, including to the empty set. -/
theorem identifiedSet_restrict {observe : M → O} {target : M → T} {p : Set M} (o : O) :
    identifiedSet (fun m : p => observe m.val) (fun m => target m.val) o ⊆
      identifiedSet observe target o := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m.val, hm, rfl⟩

theorem Identifies.restrict {observe : M → O} {target : M → T}
    (h : Identifies observe target) (p : Set M) :
    Identifies (fun m : p => observe m.val) (fun m => target m.val) :=
  fun m n same => h m.val n.val same

open MeasureTheory

/-- Each admitted model supplies a probability measure on the sample space and
a measurable readout into a common observation space. -/
structure Experiment (M S O : Type*) [MeasurableSpace S] [MeasurableSpace O] where
  sampleLaw : M → Measure S
  probability : ∀ m, IsProbabilityMeasure (sampleLaw m)
  readout : M → S → O
  measurable_readout : ∀ m, Measurable (readout m)

noncomputable def Experiment.law {S : Type*} [MeasurableSpace S] [MeasurableSpace O]
    (e : Experiment M S O) (m : M) : Measure O :=
  Measure.map (e.readout m) (e.sampleLaw m)

/-- Statistical identification concerns exact equality of induced laws, not
agreement of individual samples or statistical inference at finite sample size. -/
theorem Experiment.statistical_factor_iff {S : Type*} [MeasurableSpace S] [MeasurableSpace O]
    (e : Experiment M S O) (target : M → T) :
    (∃! recover : Set.range e.law → T, ∀ m,
      recover ⟨e.law m, ⟨m, rfl⟩⟩ = target m) ↔
      ∀ m n, e.law m = e.law n → target m = target n :=
  range_factor_iff e.law target

/-- Only reports at settings in the supplied permission set enter the map.
The caller supplies the intervention semantics and warrants permission. -/
def augment (observe : M → O) (permitted : Set I) (report : M → I → R)
    (m : M) : O × (permitted → R) :=
  (observe m, fun i => report m i.val)

/-- Extra tests suffice exactly when some permitted test separates each
observationally tied pair that differs in its target. -/
theorem augment_identifies_iff (observe : M → O) (target : M → T)
    (permitted : Set I) (report : M → I → R) :
    Identifies (augment observe permitted report) target ↔
      ∀ m n, observe m = observe n → target m ≠ target n →
        ∃ i : permitted, report m i.val ≠ report n i.val := by
  classical
  constructor
  · intro h m n same diff
    by_contra hn
    push Not at hn
    exact diff (h m n (Prod.ext same (funext hn)))
  · intro h m n same
    by_contra diff
    obtain ⟨i, hi⟩ := h m n (congrArg Prod.fst same) diff
    exact hi (congrFun (congrArg Prod.snd same) i)

end TruthCore.Science.Identifiability
