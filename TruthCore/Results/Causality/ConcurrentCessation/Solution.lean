module

public import TruthCore.Causality.ConcurrentCessation
public import TruthCore.Results.Causality.ConcurrentActualization.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ConcurrentCessation
open TruthCore.Causality.ConcurrentCessation
open TruthCore.Causality.ProtectiveProcess
open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control

theorem consequences : Consequences := by
  classical
  intro B F P m G received
  refine ⟨?_, ?_, ?_⟩
  · intro x n hLaw hBefore hNone hAbsent
    obtain ⟨p, hp⟩ := hLaw x n hBefore hAbsent
    exact hNone p hp
  · constructor
    · intro h x n z hRec hBefore hNone hAfter
      exact hNone (h x n z hRec hBefore hAfter)
    · intro h x n z hRec hBefore hAfter
      by_contra hNone
      exact h x n z hRec hBefore hNone hAfter
  · intro hLaw hFail x n z hRec hBefore hNone
    exact hLaw x n hBefore (hFail x n z hRec hBefore hNone)

theorem consumerRestriction : ConsumerRestriction := by
  intro W B F P h G received v m hMatches hActual x n z hRec _ hAfter
  exact hActual v x (n+1) z hRec ((hMatches (n+1) x).mp hAfter)

theorem controls : Control.Controls := by
  have hInertia := TruthCore.Results.Causality.ConcurrentActualization.controls.1
  have hSustained :=
    TruthCore.Results.Causality.ConcurrentActualization.controls.2.2.2.2.2.2
  refine ⟨⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, hInertia.2.2.2.2.1⟩,
    ⟨?_, ?_, ?_, ?_, hSustained.2.2.1⟩⟩
  · intro x n hBefore hAfter
    cases x with
    | false => simp_all [Control.inertialProcesses, inertia]
    | true =>
      have hn : n = 1 := by
        simp [Control.inertialProcesses, inertia] at hBefore hAfter
        omega
      subst n
      exact ⟨(), by simp [Destroys, Control.inertialProcesses]⟩
  · intro p n x h
    simp only [Destroys, Control.inertialProcesses] at h
    rcases h with ⟨⟨hn, ht⟩, _, hx⟩
    subst n; subst x
    simp [Control.inertialProcesses, inertia]
  · simp [Destroys, Control.inertialProcesses]
  · simp [Control.inertialProcesses, inertia]
  · simp [Control.inertialProcesses, inertia]
  · intro p h
    simp [Destroys, Control.inertialProcesses] at h
  · simp [inertiaGiving]
  · intro h
    obtain ⟨g, hg⟩ := h false 1 () rfl (by simp [Control.inertialProcesses, inertia])
      (by simp [Control.inertialProcesses, inertia])
    simp [inertiaGiving] at hg
  · intro x n hBefore hAfter
    cases x <;> simp_all [Control.sustainedProcesses, sustained]
  · intro p n x h
    simp [Destroys, Control.sustainedProcesses] at h
  · exact consumerRestriction Unit Bool Unit Unit sustained sustainedGiving falseReceived
      () Control.sustainedProcesses (fun _ _ => Iff.rfl) hSustained.2.2.1
  · exact (consequences Bool Unit Unit Control.sustainedProcesses sustainedGiving
      falseReceived).2.1.mp
      (consumerRestriction Unit Bool Unit Unit sustained sustainedGiving falseReceived
        () Control.sustainedProcesses (fun _ _ => Iff.rfl) hSustained.2.2.1)

theorem certificate : TruthCore.Causality.ConcurrentCessation.Certificate :=
  ⟨consequences, consumerRestriction, controls⟩

end TruthCore.Results.Causality.ConcurrentCessation
