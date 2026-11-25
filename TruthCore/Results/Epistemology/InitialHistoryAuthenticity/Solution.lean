module

public import TruthCore.Epistemology.InitialHistoryAuthenticity
public import TruthCore.Logic.InformationInvariance

@[expose] public section

namespace TruthCore.Results.Epistemology.InitialHistoryAuthenticity
open TruthCore.Epistemology.InitialHistoryAuthenticity
open TruthCore.Explanation.HistorySelection
open TruthCore.Modal.TemporalHistory

theorem varies_iff_of_injOn (allowed : I → Prop) (value : I → O)
    (hinj : Set.InjOn value { i | allowed i }) :
    Varies allowed value ↔ Varies allowed (fun i => i) := by
  constructor
  · rintro ⟨i, j, hi, hj, hd⟩
    refine ⟨i, j, hi, hj, ?_⟩
    intro hij
    exact hd (congrArg value hij)
  · rintro ⟨i, j, hi, hj, hd⟩
    exact ⟨i, j, hi, hj, fun he => hd (hinj hi hj he)⟩

theorem evolve_injective (step : Nat → S → S)
    (hinj : ∀ n, Function.Injective (step n)) :
    ∀ n, Function.Injective (fun i => evolve step i n) := by
  intro n
  induction n with
  | zero => exact fun _ _ he => he
  | succ n ih =>
    intro i j he
    exact ih (hinj n he)

theorem trajectories_injective (step : Nat → S → S) :
    Function.Injective (evolve step) := by
  intro i j he
  exact congrArg (fun trajectory => trajectory 0) he

theorem dynamics : Dynamics := by
  refine ⟨fun _ _ => varies_iff_of_injOn, fun _ => evolve_injective,
    fun _ => trajectories_injective, ?_, ?_⟩
  · intro S step allowed
    exact varies_iff_of_injOn allowed (evolve step)
      (fun _ _ _ _ he => trajectories_injective step he)
  · intro S O step read n allowed hinj
    exact varies_iff_of_injOn allowed (observed step read n) hinj

theorem sound_iff_fibers (allowed : I → Prop) (observe : I → O)
    (positive : O → Prop) (content : O → I → Prop) :
    RecordsSound allowed observe positive content ↔
      PositiveFibersTrue allowed observe positive content := by
  constructor
  · intro hs o ho i hi he
    subst o
    exact hs i hi ho
  · intro hf i hi hp
    exact hf (observe i) hp i hi rfl

theorem sound_iff_uniform_witnesses (allowed : I → Prop) (observe : I → O)
    (positive : O → Prop) (content : O → I → Prop) :
    RecordsSound allowed observe positive content ↔
      PositiveUniform allowed observe positive content ∧
      PositiveWitnesses allowed observe positive content := by
  constructor
  · intro hs
    constructor
    · intro i j hi hj hp he
      exact ⟨fun _ => hs j hj (he ▸ hp), fun _ => hs i hi hp⟩
    · intro i hi hp
      exact ⟨i, hi, rfl, hs i hi hp⟩
  · rintro ⟨hu, hw⟩ i hi hp
    exact TruthCore.Logic.InformationInvariance.of_representative
      (fun i j => allowed j ∧ observe i = observe j)
      (fun i => content (observe i) i) i
      (fun j related => hu i j hi related.1 hp related.2) (by
        obtain ⟨j, hj, he, ha⟩ := hw i hi hp
        exact ⟨j, ⟨hj, he.symm⟩, ha⟩)

/-- All observation-equality tests have the same truth values exactly when
the observations agree. This consumes the old SameEvidence definition. -/
theorem observation_evidence (observe : I → O) (i j : I) :
    SameEvidence (fun i o => observe i = o) (fun _ => True) i j ↔
      observe i = observe j := by
  constructor
  · intro he
    exact (he (observe j) trivial).mpr rfl
  · intro he o _
    exact ⟨fun hi => he.symm.trans hi, fun hj => he.trans hj⟩

theorem evidenceOnly_iff_uniform (allowed : I → Prop) (observe : I → O)
    (content : O → I → Prop) :
    AuthenticityEvidenceOnly allowed observe content ↔
      PositiveUniform allowed observe (fun _ => True) content := by
  constructor
  · intro he i j hi hj _ hij
    exact he ⟨i, hi⟩ ⟨j, hj⟩
      ((observation_evidence (fun (i : { i // allowed i }) => observe i.val)
        ⟨i, hi⟩ ⟨j, hj⟩).mpr hij)
  · intro hu i j he
    exact hu i.val j.val i.property j.property trivial
      ((observation_evidence (fun (i : { i // allowed i }) => observe i.val) i j).mp he)

theorem authenticity : Authenticity := by
  constructor
  · intro I O allowed observe positive content
    exact ⟨Iff.rfl, sound_iff_fibers allowed observe positive content,
      sound_iff_uniform_witnesses allowed observe positive content⟩
  · intro I O allowed observe content
    exact evidenceOnly_iff_uniform allowed observe content

theorem identified_origin_uniform (h : History I B T) (allowed : I → Prop)
    (observe : I → O) (positive : O → Prop) (bearer : I → B)
    (origin : I → B → H) (claim : O → H)
    (he : EssentialOrigin h origin) (hp : BearersPresent h allowed bearer)
    (hi : IdentifiesBearer allowed observe bearer) :
    PositiveUniform allowed observe positive (fun o i => origin i (bearer i) = claim o) := by
  intro i j hai haj _ ho
  have hb := hi i j hai haj ho
  have hbj : h.ontic.ExistsAt j (bearer i) := hb.symm ▸ hp j haj
  have hor : origin i (bearer i) = origin j (bearer j) :=
    (he i j (bearer i) (hp i hai) hbj).trans (congrArg (origin j) hb)
  exact ⟨fun hc => hor.symm.trans (hc.trans (congrArg claim ho)),
    fun hc => hor.trans (hc.trans (congrArg claim ho.symm))⟩

theorem identityBridge : IdentityBridge := by
  intro I B T H O h allowed observe positive bearer origin claim he hp hi
  have hu := identified_origin_uniform h allowed observe positive bearer origin claim he hp hi
  constructor
  · intro hs
    exact ((sound_iff_uniform_witnesses allowed observe positive
      (fun o i => origin i (bearer i) = claim o)).mp hs).2
  · intro hw
    exact (sound_iff_uniform_witnesses allowed observe positive
      (fun o i => origin i (bearer i) = claim o)).mpr ⟨hu, hw⟩

theorem erase_histories_vary : Varies all (evolve erase) := by
  refine ⟨false, true, trivial, trivial, ?_⟩
  intro he
  exact Bool.noConfusion (trajectories_injective erase he)

theorem unrestricted_record_unsound :
    ¬ RecordsSound all record positiveRecord pastContent := by
  intro hs
  exact Bool.noConfusion (hs (false, true) trivial rfl)

theorem false_fiber_uniform :
    PositiveUniform falsePositiveInputs record positiveRecord pastContent := by
  intro i j hi hj _ _
  constructor
  · intro hc
    exact (Bool.noConfusion (hi.1.symm.trans (hc.trans hi.2)))
  · intro hc
    exact (Bool.noConfusion (hj.1.symm.trans (hc.trans hj.2)))

theorem false_fiber_no_witness :
    ¬ PositiveWitnesses falsePositiveInputs record positiveRecord pastContent := by
  intro hw
  obtain ⟨j, hj, _, hc⟩ := hw (false, true) ⟨rfl, rfl⟩ rfl
  exact Bool.noConfusion (hj.1.symm.trans (hc.trans hj.2))

theorem controls : Controls := by
  refine ⟨⟨erase_histories_vary, fun _ _ => rfl, ?_⟩,
    ⟨evolve_injective reverse (fun _ _ _ he => Bool.not_inj he), ?_, ?_⟩,
    ⟨fun _ hi _ => hi, rfl, rfl, ?_⟩,
    ⟨unrestricted_record_unsound, ?_, fun _ _ _ _ _ => rfl,
      fun _ _ => trivial, ?_⟩,
    ⟨⟨rfl, rfl⟩, false_fiber_uniform, false_fiber_no_witness, ?_⟩,
    ⟨fun _ _ _ => rfl, ?_, rfl⟩, ?_⟩
  · rintro ⟨i, j, _, _, hd⟩
    exact hd rfl
  · exact ⟨false, true, trivial, trivial, Bool.noConfusion⟩
  · rintro ⟨i, j, _, _, hd⟩
    exact hd rfl
  · intro he
    exact Bool.noConfusion (congrArg Prod.fst he)
  · intro hu
    exact Bool.noConfusion ((hu (false, true) (true, true) trivial trivial rfl rfl).mpr rfl)
  · intro hi
    exact Bool.noConfusion (hi (false, true) (true, true) trivial trivial rfl)
  · intro hs
    exact Bool.noConfusion (hs (false, true) ⟨rfl, rfl⟩ rfl)
  · intro he
    exact Bool.noConfusion (congrArg Prod.snd he)
  · intro hs
    exact Bool.noConfusion (hs (false, true) trivial rfl)

end TruthCore.Results.Epistemology.InitialHistoryAuthenticity
