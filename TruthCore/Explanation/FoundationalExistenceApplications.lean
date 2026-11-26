module

public import TruthCore.Explanation.BruteContingencyParity

/-! Existence consequences of a sound intrinsic reason and necessary role occupancy. -/

@[expose] public section

namespace TruthCore.Explanation.FoundationalExistenceApplications

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Explanation.BruteContingencyParity (natureModel)
open TruthCore.Explanation.ExistencePSR (Sound)

theorem ownNatureNecessaryOfSound {W B T R P : Type}
    (F : CausalityFrame W B T R) (essenceOf esseOf : B → P)
    (hSound : Sound (natureModel F essenceOf esseOf))
    (x : B) (hIdentity : ¬ esseOf x ≠ essenceOf x) :
    ∀ v, F.history.ontic.ExistsAt v x :=
  fun v => hSound v x (.intrinsic x) ⟨rfl, hIdentity⟩

theorem occupiedRoleAtAbsence {W B : Type}
    (access : W → W → Prop) (existsAt rootAt : W → B → Prop)
    (w : W) (b : B)
    (occupied : ∀ v, access w v → ∃ x, rootAt v x)
    (rootExists : ∀ v x, rootAt v x → existsAt v x)
    (absent : ∃ v, access w v ∧ ¬ existsAt v b) :
    ∃ v, access w v ∧ ¬ existsAt v b ∧
      ∃ x, rootAt v x ∧ x ≠ b := by
  rcases absent with ⟨v, hv, hb⟩
  rcases occupied v hv with ⟨x, hx⟩
  refine ⟨v, hv, hb, x, hx, ?_⟩
  intro h
  subst x
  exact hb (rootExists v b hx)

open TruthCore.Causality.FirstMoverNecessity
open TruthCore.Causality.EsseCausePriority (DistinctEsseCausePriority)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)
open TruthCore.Case.Catholicism (IsFirstUnmovedMover ThereIsAFirstUnmovedMover
  FirstUnmovedMoverIsFirstBeing FirstUnmovedMoverIsPureAct)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Explanation.ExistencePSR (Model Reason ExistenceFact)
open TruthCore.Explanation.BruteContingencyParity (source reasonModel
  NoBruteContingentExistenceAt ContingentExistenceNotSelfExplained ExistenceReasonSourceCausesEsse)

/-- Restrict the esse-cause premise to the actual first mover selected by the other premises. -/
theorem necessityFromCauseForFirstMover {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (w : W) (hEM : TruthCore.Logic.ExcludedMiddle)
    (hThere : ThereIsAFirstUnmovedMover MovedIn F.MovesIn) (hExist : MoversExistAt F w)
    (hFirst : FirstUnmovedMoverIsFirstBeing MovedIn F.MovesIn F.PriorSimply)
    (hPure : FirstUnmovedMoverIsPureAct MovedIn F.MovesIn (PureAct InPotency))
    (hCause : ∀ f, IsFirstUnmovedMover MovedIn F.MovesIn f →
      ContingentAt F.history.ontic w f → ∃ c, c ≠ f ∧ F.CausesIn c f F.esse)
    (hPrior : DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply) :
    FirstMoverNecessaryPureActAt F MovedIn InPotency w := by
  obtain ⟨f, hm⟩ := hThere
  obtain ⟨x, r, hMoves⟩ := hm.1
  have hHere := hExist f x r hMoves
  refine ⟨f, hm, hPure f hm, hHere, fun v hv => ?_⟩
  rcases hEM (F.history.ontic.ExistsAt v f) with h | h
  · exact h
  · obtain ⟨c, hne, hc⟩ := hCause f hm ⟨hHere, v, hv, h⟩
    exact (hne (hFirst f hm c (hPrior c f hne hc))).elim

/-- When a contingent individual's existence has a reason, at least one reason
has a distinct bearer. Reasons about the individual itself are permitted. -/
def SomeExternalReasonAvailable {W B : Type} (m : Model W B) (w : W) : Prop :=
  ∀ x, ContingentAt m.ontic w x → (∃ r, m.explains w r (.fact x)) →
    ∃ r, m.explains w r (.fact x) ∧ source r ≠ x

theorem externalAvailableOfNoSelfExplanation {W B : Type} (m : Model W B) (w : W)
    (h : ContingentExistenceNotSelfExplained m w) : SomeExternalReasonAvailable m w := by
  intro x hc ⟨r, hr⟩
  exact ⟨r, hr, h x r hc hr⟩

/-- Local PSR supplies a reason, availability selects an external reason, and
the causal bridge applies to that same reason and recipient. -/
theorem causeFromAvailableExternalReason {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W)
    (hPSR : NoBruteContingentExistenceAt (reasonModel F ex) w)
    (hAvailable : SomeExternalReasonAvailable (reasonModel F ex) w)
    (hSource : ExistenceReasonSourceCausesEsse F (reasonModel F ex) w) :
    ContingentHasDistinctEsseCause F w := by
  intro x hx
  obtain ⟨r, hr, hne⟩ := hAvailable x hx (hPSR x hx)
  exact ⟨source r, hne, hSource x r hx hr hne⟩

/-- Keep each reason exactly at worlds where its target bearer exists. -/
def actualTargetReasons {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) :
    W → Reason B → ExistenceFact B → Prop
  | w, r, .fact x => ex w r (.fact x) ∧ F.history.ontic.ExistsAt w x

theorem actualTargetReasonsSound {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) :
    Sound (reasonModel F (actualTargetReasons F ex)) :=
  fun _ _ _ h => h.2

/-- The restriction leaves every token for an actual contingent bearer intact
at the selected world. Contingency already includes occurrence there. -/
theorem actualTargetReasonIff {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W) (x : B) (r : Reason B)
    (hx : ContingentAt F.history.ontic w x) :
    (reasonModel F (actualTargetReasons F ex)).explains w r (.fact x) ↔
      (reasonModel F ex).explains w r (.fact x) :=
  ⟨And.left, fun hr => ⟨hr, hx.1⟩⟩

theorem actualTargetReasonsLocalPSRIff {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W) :
    NoBruteContingentExistenceAt (reasonModel F (actualTargetReasons F ex)) w ↔
      NoBruteContingentExistenceAt (reasonModel F ex) w := by
  constructor
  · intro h x hx
    obtain ⟨r, hr⟩ := h x hx
    exact ⟨r, (actualTargetReasonIff F ex w x r hx).mp hr⟩
  · intro h x hx
    obtain ⟨r, hr⟩ := h x hx
    exact ⟨r, (actualTargetReasonIff F ex w x r hx).mpr hr⟩

open TruthCore.Causality.FirstMoverNecessity.Model (bruteFirst conserved fContingent mk
  noCause noPrior xCausesF xPriorF)
open TruthCore.Explanation.BruteContingencyParity (occasion selfAndOccasion)

private theorem firstMoverContingency
    (causes : Bool → Bool → Bool → Prop) (prior : Bool → Bool → Prop) (x : Bool) :
    ContingentAt (mk fContingent causes prior).history.ontic true x ↔ x = true := by
  constructor
  · intro hx
    cases x with
    | false =>
      obtain ⟨_, v, _, habs⟩ := hx
      exact (habs (Or.inl rfl)).elim
    | true => rfl
  · rintro rfl
    refine ⟨Or.inr rfl, false, trivial, ?_⟩
    rintro (h | h) <;> contradiction

/-- Both tokens survive at the reading world in the sound conserved model.
The local PSR, external availability and BX2 hold while universal BX1 fails. -/
theorem soundMixedReasons :
    let m := reasonModel conserved (actualTargetReasons conserved selfAndOccasion)
    Sound m ∧
      ContingentAt m.ontic true true ∧
      m.explains true (.intrinsic true) (.fact true) ∧
      m.explains true (.circumstance false) (.fact true) ∧
      NoBruteContingentExistenceAt m true ∧
      SomeExternalReasonAvailable m true ∧
      ExistenceReasonSourceCausesEsse conserved m true ∧
      ¬ ContingentExistenceNotSelfExplained m true := by
  let ex := actualTargetReasons conserved selfAndOccasion
  have hc : ContingentAt conserved.history.ontic true true :=
    (firstMoverContingency xCausesF xPriorF true).mpr rfl
  have intrinsic : ex true (.intrinsic true) (.fact true) := ⟨Or.inl rfl, hc.1⟩
  have external : ex true (.circumstance false) (.fact true) := ⟨Or.inr ⟨rfl, rfl⟩, hc.1⟩
  refine ⟨actualTargetReasonsSound conserved selfAndOccasion, hc, intrinsic, external,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain rfl := (firstMoverContingency xCausesF xPriorF x).mp hx
    exact ⟨.circumstance false, external⟩
  · intro x hx _
    obtain rfl := (firstMoverContingency xCausesF xPriorF x).mp hx
    exact ⟨.circumstance false, external, by decide⟩
  · intro x r hx _ hne
    obtain rfl := (firstMoverContingency xCausesF xPriorF x).mp hx
    cases hSource : source r with
    | false => exact ⟨rfl, rfl, rfl⟩
    | true => exact (hne hSource).elim
  · intro h
    exact h true (.intrinsic true) hc intrinsic rfl

/-- In the sound brute-first model the existing moved thing provides the
circumstance token, while its existence and the token supply no esse-cause. -/
theorem soundOccasionWithoutEsseCause :
    let m := reasonModel bruteFirst (actualTargetReasons bruteFirst occasion)
    Sound m ∧
      ContingentAt m.ontic true true ∧
      m.ontic.ExistsAt true false ∧
      m.explains true (.circumstance false) (.fact true) ∧
      NoBruteContingentExistenceAt m true ∧
      SomeExternalReasonAvailable m true ∧
      ¬ ExistenceReasonSourceCausesEsse bruteFirst m true ∧
      (∀ c, ¬ bruteFirst.CausesIn c true bruteFirst.esse) ∧
      ¬ ContingentHasDistinctEsseCause bruteFirst true := by
  let ex := actualTargetReasons bruteFirst occasion
  have hc : ContingentAt bruteFirst.history.ontic true true :=
    (firstMoverContingency noCause noPrior true).mpr rfl
  have external : ex true (.circumstance false) (.fact true) := ⟨⟨rfl, rfl⟩, hc.1⟩
  have available : SomeExternalReasonAvailable (reasonModel bruteFirst ex) true := by
    intro x hx _
    obtain rfl := (firstMoverContingency noCause noPrior x).mp hx
    exact ⟨.circumstance false, external, by decide⟩
  have noEsseCause : ∀ c, ¬ bruteFirst.CausesIn c true bruteFirst.esse :=
    fun _ h => h
  refine ⟨actualTargetReasonsSound bruteFirst occasion, hc, Or.inl rfl, external,
    ?_, available, ?_, noEsseCause, ?_⟩
  · intro x hx
    obtain rfl := (firstMoverContingency noCause noPrior x).mp hx
    exact ⟨.circumstance false, external⟩
  · intro h
    exact noEsseCause false (h true (.circumstance false) hc external (by decide))
  · intro h
    obtain ⟨c, _, hcSource⟩ := h true hc
    exact noEsseCause c hcSource

end TruthCore.Explanation.FoundationalExistenceApplications
