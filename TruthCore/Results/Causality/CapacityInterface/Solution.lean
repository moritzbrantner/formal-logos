module

public import TruthCore.Causality.CapacityInterface
public import TruthCore.Results.Explanation.BorrowedExercise.Solution

@[expose] public section

namespace TruthCore.Results.Causality.CapacityInterface
open TruthCore.Causality.CapacityInterface

variable {S E W B R : Type}

theorem agreement_of_corresponds (i : Indexing S E W B R) (cap : S → E → Prop)
    (p : Capacity W B R) (h : Corresponds i cap p) : FiberAgreement i cap := by
  intro s t e f hs hb hr
  have same : eventProfile p i s e ↔ eventProfile p i t f := by
    unfold eventProfile
    rw [hs, hb, hr]
  exact (h s e).trans (same.trans (h t f).symm)

theorem descend_corresponds (i : Indexing S E W B R) (cap : S → E → Prop)
    (h : FiberAgreement i cap) : Corresponds i cap (descend i cap) := by
  intro s e
  constructor
  · intro he
    exact ⟨s, e, rfl, rfl, rfl, he⟩
  · rintro ⟨t, f, hs, hb, hr, hf⟩
    exact (h t s f e hs hb hr).mp hf

theorem factorization : Factorization := by
  intro S E W B R i cap
  refine ⟨⟨?_, ?_⟩, descend_corresponds i cap⟩
  · intro h
    exact ⟨descend i cap, descend_corresponds i cap h⟩
  · rintro ⟨p, h⟩
    exact agreement_of_corresponds i cap p h

theorem round_trips : RoundTrips := by
  constructor
  · intro B E G S R m respect cap s e
    constructor
    · intro h
      exact ⟨rfl, rfl, h⟩
    · intro h
      exact h.2.2
  · intro W B power
    rfl

theorem borrowed_transport : BorrowedTransport := by
  intro B E G S W R m world respect cap p h
  have heq : cap = eventProfile p (exerciseIndex m world respect) :=
    funext fun s => funext fun e => propext (h s e)
  rw [heq]
  exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, Iff.rfl⟩

theorem root_consumer_transport : RootConsumerTransport := by
  intro W B Episode o a concrete power w
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem index_controls : IndexControls := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨p, h⟩
    have agree := agreement_of_corresponds collapsedEvents eventDisagreement p h
    have impossible : false = true :=
      (agree () () false true rfl rfl rfl).mpr rfl
    cases impossible
  · rintro ⟨p, h⟩
    have agree := agreement_of_corresponds collapsedScenarios scenarioDisagreement p h
    have impossible : false = true :=
      (agree false true () () rfl rfl rfl).mpr rfl
    cases impossible
  · intro s e
    exact Iff.rfl

theorem certificate : TruthCore.Causality.CapacityInterface.Certificate := by
  exact ⟨factorization, round_trips, borrowed_transport, root_consumer_transport,
    index_controls, TruthCore.Results.Explanation.BorrowedExercise.instrument_regress,
    TruthCore.Results.Explanation.BorrowedExercise.secondary_regress,
    TruthCore.Results.Explanation.BorrowedExercise.power_omission⟩

end TruthCore.Results.Causality.CapacityInterface
