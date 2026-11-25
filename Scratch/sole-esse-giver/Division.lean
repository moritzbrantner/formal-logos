import TruthCore.Mereology.LifeRestricted327

/-! Analyst control for attribution at onset. The two sides initially share the
products of processing. The generator reroutes each side's supply before the
connection closes. The supplied organism criterion and the metaphysical reading
of existential production are external to this maintenance model. -/
namespace EsseDivision

open TruthCore.Mereology.LifeRestricted327

/-- With feed, a side renews processing using its own processing and boundary.
Its boundary renewal also needs processed material: from home after rerouting,
and otherwise from the other side while the connection remains open. -/
def step (usesOwn connected : Bool) (other here : State) : State :=
  let supplied := if usesOwn then here.processing else connected && other.processing
  ⟨here.processing && here.boundary, supplied && here.boundary⟩

theorem beforeSeparation (usesOwn : Bool) :
    step usesOwn true full full = full := by
  cases usesOwn <;> rfl

/-- With its connection closed and local capacities initially occupied, even
the first apparent residual capacity on an unprepared side disappears by the
second renewal. No external replacement or standby store is present. -/
theorem afterSeparation (other : State) :
    step false false other (step false false other full) = empty ∧
    (∀ here, step true false other here = regenerate true here) := by
  exact ⟨rfl, fun _ => rfl⟩

private theorem independentRenewal (usesOwn : Bool) :
    Reciprocal (step usesOwn false full) ↔ usesOwn = true := by
  cases usesOwn with
  | false =>
    constructor
    · intro h
      cases h.1
    · intro h
      cases h
  | true => exact ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Both sides meet the existing reciprocal-renewal test after closure exactly
when the generator has rerouted both inlets. Preparing one side tests only it. -/
theorem twoIndependentRenewals (leftOwn rightOwn : Bool) :
    (Reciprocal (step leftOwn false full) ∧ Reciprocal (step rightOwn false full)) ↔
      leftOwn = true ∧ rightOwn = true := by
  exact ⟨fun h => ⟨(independentRenewal _).1 h.1, (independentRenewal _).1 h.2⟩,
    fun h => ⟨(independentRenewal _).2 h.1, (independentRenewal _).2 h.2⟩⟩

#print axioms beforeSeparation
#print axioms afterSeparation
#print axioms twoIndependentRenewals

end EsseDivision
