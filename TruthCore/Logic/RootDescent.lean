module

/-!
# Root descent: a zero-axiom kernel for well-founded regress arguments (#1926)

Purely structural lemmas about Lean's `Acc` and `WellFounded`, with no
philosophical content. They factor the hand-rolled accessibility inductions
that many Solutions repeat: walking down a well-founded relation until a
stopping condition holds, and refuting a property that every bearer passes to
a predecessor.

An edge `r z y` points from the predecessor `z` to `y`, as in Lean's `Acc`.
What the relation means (grounding, efficient causing, explaining, moving) is
fixed by each instance, not here; nothing in this module identifies two such
relations or asserts that any real relation is well-founded.

This module imports nothing beyond Lean's prelude. Every lemma uses no axiom,
so a zero-axiom result may use it without importing Mathlib or growing its
axiom list. `Relation.ReflTransGen` is a Mathlib notion and is therefore not
used: an instance that needs the chain from the root to its start carries it
in the predicate `P`. The Mathlib-backed forms (least fixed points, edge maps
between `Regress.Graph`s) remain in `TruthCore.Logic.Regress`.
-/

@[expose] public section

namespace TruthCore.Logic.RootDescent

universe u v

variable {α : Sort u} {r : α → α → Prop}

/-! ## Inheritance: a property passed to predecessors has no accessible bearer -/

/-- Purely structural: if every bearer of `P` cannot fail to have a
predecessor bearing `P`, no `r`-accessible element bears `P`. The double
negation lets constructive instances supply the predecessor by reductio. -/
theorem acc_not_of_notNot_inherited {P : α → Prop}
    (step : ∀ y, P y → ¬¬ ∃ z, r z y ∧ P z) {x : α} (hx : Acc r x) : ¬ P x := by
  induction hx with
  | intro x _ ih => exact fun hp => step x hp fun ⟨z, hz, hpz⟩ => ih z hz hpz

/-- Purely structural: if every bearer of `P` has a predecessor bearing `P`,
no `r`-accessible element bears `P`. -/
theorem acc_not_of_inherited {P : α → Prop}
    (step : ∀ y, P y → ∃ z, r z y ∧ P z) {x : α} (hx : Acc r x) : ¬ P x :=
  acc_not_of_notNot_inherited (fun y hy hn => hn (step y hy)) hx

/-- Purely structural: under a well-founded relation, a property that cannot
fail to pass to a predecessor is empty. -/
theorem not_of_notNot_inherited {P : α → Prop} (hwf : WellFounded r)
    (step : ∀ y, P y → ¬¬ ∃ z, r z y ∧ P z) : ∀ x, ¬ P x :=
  fun x => acc_not_of_notNot_inherited step (hwf.apply x)

/-- Purely structural: under a well-founded relation, a property passed to a
predecessor is empty. -/
theorem not_of_inherited {P : α → Prop} (hwf : WellFounded r)
    (step : ∀ y, P y → ∃ z, r z y ∧ P z) : ∀ x, ¬ P x :=
  fun x => acc_not_of_inherited step (hwf.apply x)

/-! ## Descent: walking down to an element that stops -/

/-- Purely structural: starting from an accessible bearer of `P`, if every
bearer of `P` either stops or has a predecessor bearing `P`, some bearer of `P`
stops. Constructive: the case split is supplied by `step`. A chain back to the
start can be carried inside `P`. -/
theorem acc_descend {P Stop : α → Prop}
    (step : ∀ y, P y → Stop y ∨ ∃ z, r z y ∧ P z) {x : α} (hx : Acc r x) (hp : P x) :
    ∃ n, P n ∧ Stop n := by
  induction hx with
  | intro x _ ih =>
    rcases step x hp with hs | ⟨z, hz, hpz⟩
    · exact ⟨x, hp, hs⟩
    · exact ih z hz hpz

/-- Purely structural: `acc_descend` from any bearer of `P` under a
well-founded relation. -/
theorem descend {P Stop : α → Prop} (hwf : WellFounded r)
    (step : ∀ y, P y → Stop y ∨ ∃ z, r z y ∧ P z) {x : α} (hp : P x) :
    ∃ n, P n ∧ Stop n :=
  acc_descend step (hwf.apply x) hp

/-- Purely structural look-ahead descent with a chain: if every bearer of `P`
has a predecessor that stops or bears `P`, some stopping element reaches the
start by a nonempty `r`-chain (`Relation.TransGen`, which is core Lean). -/
theorem acc_exists_transGen {P Stop : α → Prop}
    (step : ∀ y, P y → ∃ z, r z y ∧ (Stop z ∨ P z)) {x : α} (hx : Acc r x) (hp : P x) :
    ∃ n, Stop n ∧ Relation.TransGen r n x := by
  induction hx with
  | intro x _ ih =>
    obtain ⟨z, hz, hs | hpz⟩ := step x hp
    · exact ⟨z, hs, .single hz⟩
    · obtain ⟨n, hn, hnz⟩ := ih z hz hpz
      exact ⟨n, hn, .tail hnz hz⟩

/-- Purely structural descent with a mark: if every marked bearer of `P` has a
predecessor bearing `P`, and the mark is decided on bearers of `P`, an
unmarked bearer of `P` exists (below the start, if `P` carries the chain). The
decision `em` is a hypothesis, so no classical axiom is used. -/
theorem acc_exists_unmarked {P Mark : α → Prop}
    (em : ∀ y, P y → Mark y ∨ ¬ Mark y)
    (step : ∀ y, P y → Mark y → ∃ z, r z y ∧ P z) {x : α} (hx : Acc r x) (hp : P x) :
    ∃ n, P n ∧ ¬ Mark n :=
  acc_descend (fun y hy => (em y hy).elim (fun hm => Or.inr (step y hy hm)) Or.inl) hx hp

/-- Purely structural, constructive form of `acc_exists_unmarked`: without a
decision for the mark, an unmarked bearer of `P` cannot fail to exist. -/
theorem acc_notNot_exists_unmarked {P Mark : α → Prop}
    (step : ∀ y, P y → Mark y → ∃ z, r z y ∧ P z) {x : α} (hx : Acc r x) (hp : P x) :
    ¬¬ ∃ n, P n ∧ ¬ Mark n :=
  fun hNone =>
    acc_not_of_notNot_inherited
      (fun y hy hNoPred => hNone ⟨y, hy, fun hm => hNoPred (step y hy hm)⟩) hx hp

/-- Purely structural "no predecessor" form: with the existence of a
predecessor bearing `P` decided on bearers of `P`, starting from an accessible
bearer of `P`, some bearer of `P` exists that has no predecessor bearing `P`
(below the start, if `P` carries the chain). -/
theorem acc_exists_minimal {P : α → Prop}
    (em : ∀ y, P y → (∃ z, r z y ∧ P z) ∨ ¬ ∃ z, r z y ∧ P z)
    {x : α} (hx : Acc r x) (hp : P x) :
    ∃ n, P n ∧ ∀ z, r z n → ¬ P z := by
  obtain ⟨n, hn, hNone⟩ := acc_exists_unmarked em (fun _ _ h => h) hx hp
  exact ⟨n, hn, fun z hz hpz => hNone ⟨z, hz, hpz⟩⟩

/-! ## Transfer of accessibility -/

/-- Purely structural: accessibility pulls back along an edge-preserving map.
Core Lean's `InvImage.accessible` and `Subrelation.accessible`, composed; the
Mathlib-importing `Regress.Graph.Map.accessible` is the same fact for `Regress.Graph`s. -/
theorem acc_of_map {β : Sort v} {s : β → β → Prop} (f : α → β)
    (hf : ∀ y x, r y x → s (f y) (f x)) {x : α} (h : Acc s (f x)) : Acc r x :=
  Subrelation.accessible (fun {y x} h => hf y x h) (InvImage.accessible f h)

/-- Purely structural: well-foundedness pulls back along an edge-preserving map. -/
theorem wellFounded_of_map {β : Sort v} {s : β → β → Prop} (f : α → β)
    (hf : ∀ y x, r y x → s (f y) (f x)) (h : WellFounded s) : WellFounded r :=
  ⟨fun x => acc_of_map f hf (h.apply (f x))⟩

/-- Purely structural: accessibility in the restriction of `r` to `Q` gives
accessibility for `s` whenever every `s`-predecessor of a member of `Q` is a
member of `Q` and an `r`-predecessor. So a well-founded restriction to a set
closed under `s`-predecessors controls `s` on that set. -/
theorem acc_of_subtype {Q : α → Prop} {s : α → α → Prop}
    (hs : ∀ y x, Q x → s y x → Q y ∧ r y x) (a : {x // Q x})
    (h : Acc (fun a b : {x // Q x} => r a.1 b.1) a) : Acc s a.1 := by
  induction h with
  | intro a _ ih =>
    refine Acc.intro a.1 fun y hy => ?_
    obtain ⟨hq, hr⟩ := hs y a.1 a.2 hy
    exact ih ⟨y, hq⟩ hr

/-! ## The generic form -/

/-- Purely structural: well-foundedness is accessibility of every element.
Many `NoInfinite…Reading` definitions are stated in one of these two forms. -/
theorem wellFounded_iff_forall_acc : WellFounded r ↔ ∀ x, Acc r x :=
  ⟨fun h => h.apply, WellFounded.intro⟩

end TruthCore.Logic.RootDescent
