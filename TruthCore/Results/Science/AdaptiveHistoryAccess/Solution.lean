module

public import TruthCore.Science.AdaptiveHistoryAccess
public import TruthCore.Results.Logic.CorrectionCriterion.Solution

@[expose] public section

namespace TruthCore.Results.Science.AdaptiveHistoryAccess
open TruthCore.Science.AdaptiveHistoryAccess

private theorem runAgreement {S T A O : Type} (e : Experiment S A O)
    (f : Experiment T A O) (r : S → T → Prop) (matching : StableMatching e f r)
    (policy : List O → A) (n : Nat) :
    ∀ s t record, r s t → run e policy n s record = run f policy n t record := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
      intro s t record related
      have nextRelated := (matching s t related).2 (policy record)
      have nextReadout := (matching _ _ nextRelated).1
      simp only [run]
      rw [nextReadout]
      exact ih _ _ _ nextRelated

/-- Output-preserving transition matching survives every finite adaptive test.
The induction uses the same policy after equal earlier transcripts. -/
theorem adaptiveAgreement : AdaptiveAgreement := by
  intro S T A O e f r matching policy n s t related
  unfold transcript
  rw [(matching s t related).1]
  exact runAgreement e f r matching policy n s t _ related

/-- The latent-history control and the supplied history-sensitive discriminator
share their initial reading; only the blind interface satisfies matching. -/
theorem historyControls : HistoryControls := by
  have matching : StableMatching blind blind SameVisible := by
    intro s t same
    refine ⟨same, ?_⟩
    intro a
    change (if a then !s.2 else s.2) = (if a then !t.2 else t.2)
    rw [same]
  have agree : ∀ policy n s t, SameVisible s t →
      transcript blind policy n s = transcript blind policy n t :=
    adaptiveAgreement HistoryState HistoryState Bool Bool blind blind SameVisible matching
  refine ⟨matching, agree, ?_, rfl, rfl, ?_, ?_⟩
  · intro policy n criterion
    have invariant := (TruthCore.Results.Logic.CorrectionCriterion.characterization.1
      HistoryState (List Bool) (transcript blind policy n) PastOccurred).mp criterion
    have same := agree policy n (false, false) (true, false) rfl
    have impossible : false = true := (invariant (false, false) (true, false) same).mpr rfl
    cases impossible
  · decide
  · refine ⟨(fun readings => readings[1]? = some true), ?_⟩
    intro s
    rcases s with ⟨past, visible⟩
    change (some past = some true ↔ past = true)
    constructor
    · exact Option.some.inj
    · exact congrArg some

end TruthCore.Results.Science.AdaptiveHistoryAccess
