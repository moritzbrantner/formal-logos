module

public import TruthCore.Explanation.LimitPersistenceLaw

@[expose] public section

namespace TruthCore.Results.Explanation.LimitPersistenceLaw

open TruthCore.Modal.TemporalHistory
open TruthCore.Explanation.LimitPersistenceLaw

/-- At the abstract ω+1 limit, finite-step survival alone can lose an effect,
while an interval-wide no-destruction law permits a positive inertial history
with the same entire finite past and no concurrent esse-giving. An endpoint
destruction interpretation remains explicitly additional and disputable. This
is an unregistered structural certificate, not a real-world necessity claim. -/
theorem limitPersistenceControls :
    TruthCore.Explanation.LimitPersistenceLaw.LimitCertificate := by
  classical
  unfold TruthCore.Explanation.LimitPersistenceLaw.LimitCertificate
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v x
    simp [disappearsAtLimit]
  · intro v x
    simp [existsAtLimit, disappearsAtLimit]
  · intro x n
    simp [disappearsAtLimit, existsAtLimit]
  · intro x n _
    simp [disappearsAtLimit]
  · intro x n _
    trivial
  · simp [disappearsAtLimit]
  · simp [disappearsAtLimit]
  · trivial
  · simp [givingAtOrigin]
  · rintro ⟨g, hg⟩
    simp [givingAtOrigin] at hg
  · intro h
    obtain ⟨u, _, _, hD⟩ := h () false (0 : WithTop Nat) ⊤
      (by simp) (by simp [disappearsAtLimit])
      (by simp [disappearsAtLimit])
    exact hD
  · intro v x s t _ _ hnot
    exact False.elim (hnot (by trivial))
  · intro v x s t hst _ hnot
    change ¬ (x = true ∨ t ≠ ⊤) at hnot
    have hx : x = false := by
      cases x with
      | false => rfl
      | true => exact False.elim (hnot (Or.inl rfl))
    have ht : t = ⊤ := by
      by_contra hn
      exact hnot (Or.inr hn)
    exact ⟨t, hst, le_refl t, ⟨hx, ht⟩⟩
  · intro h
    obtain ⟨g, hg⟩ := h () false ((1 : Nat) : WithTop Nat) () 
      (by simp [TruthCore.Causality.ConcurrentActualization.Control.falseReceived])
      (by simp [existsAtLimit])
    simp [givingAtOrigin] at hg

end TruthCore.Results.Explanation.LimitPersistenceLaw
