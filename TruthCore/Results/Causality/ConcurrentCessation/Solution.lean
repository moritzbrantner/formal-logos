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


/-- A same-world and same-bearer C3/¬C3 control, using the existing actual
grounding and cause-of-esse relations. This is an unregistered structural
certificate: it does not establish that either model is metaphysically possible
or close a corpus premise. -/
theorem c3ActualWorldControls : C3ActualWorld.Certificate := by
  unfold C3ActualWorld.Certificate
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- One history and the same substantial bearer at each temporal/world index.
  · intro v x
    cases v <;> cases x <;> simp [C3ActualWorld.history]
  -- A positive persistence rule, conditional on earlier actuality.
  · intro v x n hp
    change v = true ∧ (x = true ∨ (x = false ∧ 1 ≤ n)) at hp
    change v = true ∧ (x = true ∨ (x = false ∧ 1 ≤ n + 1))
    rcases hp with ⟨hv, hx | ⟨hx, hn⟩⟩
    · exact ⟨hv, Or.inl hx⟩
    · exact ⟨hv, Or.inr ⟨hx, by omega⟩⟩
  -- Both cause and effect are actual concrete at the selected world.
  · simp [TruthCore.Causality.NecessaryRootFork.ActualConcrete,
      C3ActualWorld.withGround, C3ActualWorld.history]
  · simp [TruthCore.Causality.NecessaryRootFork.ActualConcrete,
      C3ActualWorld.withGround, C3ActualWorld.history]
  -- The effect is contingent; here every actual bearer is contingent.
  · refine ⟨by simp [C3ActualWorld.history],
      ⟨false, by trivial, by simp [C3ActualWorld.history]⟩⟩
  · intro x _
    exact ⟨by simp [C3ActualWorld.history],
      ⟨false, by trivial, by simp [C3ActualWorld.history]⟩⟩
  -- Hence no necessary concrete being is smuggled into the rival.
  · rintro ⟨x, _, _, hn⟩
    have h := hn false (by trivial)
    simp [C3ActualWorld.withGround, C3ActualWorld.history] at h
  · rintro ⟨x, _, _, hn⟩
    have h := hn false (by trivial)
    simp [C3ActualWorld.withoutGround, C3ActualWorld.withGround,
      C3ActualWorld.history] at h
  -- The same originating esse cause is real at the selected world.
  · simp [C3ActualWorld.originFrame, C3ActualWorld.frame, trueCausesFalse]
  · refine ⟨1, ⟨by simp [C3ActualWorld.history], ?_⟩,
      by simp [C3ActualWorld.originGiving]⟩
    intro s hs hp
    simp [C3ActualWorld.history] at hp
    omega
  -- Giving at onset requires a present giver, but does not force continuation.
  · intro v c x t hg
    change v = true ∧ (c = true ∨ (c = false ∧ 1 ≤ t))
    exact ⟨hg.1, Or.inl hg.2.1⟩
  · intro v x t hg
    cases x <;> simp [C3ActualWorld.originGiving] at hg
  -- The formal cause→actual-ground bridge can hold with no present giving.
  · intro c x _ _ hc
    rcases hc with ⟨rfl, rfl⟩
    simp [TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround,
      C3ActualWorld.withGround, C3ActualWorld.history]
  -- But weak concurrent actualization and originating→sustaining both fail.
  · intro hC
    obtain ⟨g, hg⟩ := hC true false 2 () (by rfl) (by simp [C3ActualWorld.history])
    simp [C3ActualWorld.originGiving] at hg
  · intro hS
    have hs := hS true true false (by decide)
      (by simp [C3ActualWorld.originFrame, C3ActualWorld.frame, trueCausesFalse])
      ⟨1, by simp [C3ActualWorld.history]⟩
    have hg := hs.2 2 (by simp [C3ActualWorld.history])
    simp [C3ActualWorld.originGiving] at hg
  -- An otherwise identical actual ontology without the grounding edge
  -- defeats the cause→ground bridge despite an actual originating cause.
  · intro hb
    have hbad := hb true false (by decide)
      (by simp [TruthCore.Causality.NecessaryRootFork.ActualConcrete,
        C3ActualWorld.withoutGround, C3ActualWorld.withGround, C3ActualWorld.history])
      (by simp [C3ActualWorld.originFrame, C3ActualWorld.frame, trueCausesFalse])
    exact hbad.2.2
  -- A conserving source on that same history satisfies C3.
  · intro v x t z hr hp
    have hx : x = false := hr
    subst x
    have hvt : v = true ∧ 1 ≤ t := by
      change v = true ∧ (false = true ∨ (false = false ∧ 1 ≤ t)) at hp
      simpa using hp
    refine ⟨true, ?_⟩
    change v = true ∧ true = true ∧ false = false ∧ 1 ≤ t
    exact ⟨hvt.1, rfl, rfl, hvt.2⟩
  · intro v c x _ hc hp
    rcases hc with ⟨rfl, rfl⟩
    obtain ⟨t, ht⟩ := hp
    refine ⟨⟨t, ht⟩, ?_⟩
    intro s hs
    have hvs : v = true ∧ 1 ≤ s := by
      change v = true ∧ (false = true ∨ (false = false ∧ 1 ≤ s)) at hs
      simpa using hs
    change v = true ∧ true = true ∧ false = false ∧ 1 ≤ s
    exact ⟨hvs.1, rfl, rfl, hvs.2⟩
  · intro v c x t hg
    change v = true ∧ (c = true ∨ (c = false ∧ 1 ≤ t))
    exact ⟨hg.1, Or.inl hg.2.1⟩


/-- Matched-onset withdrawal versus non-destructive persistence, without
reidentifying a historical origin as a currently productive cause. This is an
unregistered structural model check, not a metaphysical-possibility claim. -/
theorem withdrawalLawControls : WithdrawalLaw.Certificate := by
  unfold WithdrawalLaw.Certificate
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- The effect's rigid world-existence agrees with its temporal presence now.
  · intro v x
    exact Iff.rfl
  -- The source is necessary in this stipulated modal frame.
  · intro v _
    simp [WithdrawalLaw.history]
  -- The effect is contingent despite its origin by that source.
  · refine ⟨by simp [WithdrawalLaw.history, WithdrawalLaw.effectAt],
      ⟨WithdrawalLaw.Scenario.absent, trivial,
        by simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]⟩⟩
  -- Conservation and inertia agree on every bearer and giving fact to t=1.
  · constructor
    · intro x t ht
      have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with rfl | rfl
      · cases x <;> simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]
      · cases x <;> simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]
    · intro c x t ht
      have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with rfl | rfl
      · cases c <;> cases x <;> simp [WithdrawalLaw.giving]
      · cases c <;> cases x <;> simp [WithdrawalLaw.giving]
  -- Inertia and loss agree on exactly the same past and originating exercise.
  · constructor
    · intro x t ht
      have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with rfl | rfl
      · cases x <;> simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]
      · cases x <;> simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]
    · intro c x t ht
      have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with rfl | rfl
      · cases c <;> cases x <;> simp [WithdrawalLaw.giving]
      · cases c <;> cases x <;> simp [WithdrawalLaw.giving]
  -- The no-positive-loss coverage law is true with either continued giving,
  -- or none at t=2. It also permits an uninstantiated effect.
  · intro x n hBefore hGone
    exfalso
    cases x <;> simp_all [WithdrawalLaw.noDestruction,
      WithdrawalLaw.history, WithdrawalLaw.effectAt] <;> omega
  · intro x n hBefore hGone
    exfalso
    cases x <;> simp_all [WithdrawalLaw.noDestruction,
      WithdrawalLaw.history, WithdrawalLaw.effectAt] <;> omega
  · intro x n hBefore hGone
    exfalso
    cases x <;> simp_all [WithdrawalLaw.noDestruction,
      WithdrawalLaw.history, WithdrawalLaw.effectAt]
  -- Loss in the no-destruction scenario is an omission of that law, not an
  -- automatic refutation of the no-giver case or of the law's real warrant.
  · intro hLaw
    obtain ⟨p, hp⟩ := hLaw false 1
      (by simp [WithdrawalLaw.noDestruction, WithdrawalLaw.history,
        WithdrawalLaw.effectAt])
      (by simp [WithdrawalLaw.noDestruction, WithdrawalLaw.history,
        WithdrawalLaw.effectAt])
    exact hp.1
  -- The same numerically distinct giver genuinely originates the effect.
  · refine ⟨1, ⟨by simp [WithdrawalLaw.history, WithdrawalLaw.effectAt], ?_⟩,
      by simp [WithdrawalLaw.giving]⟩
    intro s hs hp
    simp [WithdrawalLaw.history, WithdrawalLaw.effectAt] at hp
    omega
  -- The actual source stays present whenever its giving operates.
  · intro v c x t hg
    have hc : c = true := hg.1
    subst c
    simp [WithdrawalLaw.history]
  -- At the conservation scenario the received effect is given at each t.
  · intro x t z hreceived hAt
    have hx : x = false := hreceived
    subst x
    have ht : 1 ≤ t := by
      simpa [WithdrawalLaw.history, WithdrawalLaw.effectAt] using hAt
    refine ⟨true, ?_⟩
    simp [WithdrawalLaw.frame, WithdrawalLaw.giving, ht]
  -- Inertia falsifies the very same selected-world C3 content at t=2.
  · intro hC
    obtain ⟨c, hc⟩ := hC false 2 () (by rfl)
      (by simp [WithdrawalLaw.history, WithdrawalLaw.effectAt])
    cases c <;> simp [WithdrawalLaw.frame, WithdrawalLaw.giving] at hc
  · simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]
  · simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]
  · simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]
  · simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]
  -- The source's current exercise changes independently of the entire past.
  · intro g
    cases g <;> simp [WithdrawalLaw.frame, WithdrawalLaw.giving]
  · simp [WithdrawalLaw.frame, WithdrawalLaw.giving]
  -- No *positive* destructive process is encoded in either continuation or
  -- cessation. Calling withdrawal itself destruction would change the input.
  · simp [NoCessationCause, Destroys, WithdrawalLaw.noDestruction]
  · simp [NoCessationCause, Destroys, WithdrawalLaw.noDestruction]
  -- Causal coverage never entails that a particular effect gets instantiated.
  · intro t
    simp [WithdrawalLaw.history, WithdrawalLaw.effectAt]
  -- Classification control: the same vanished bearer and history can be
  -- coupled to a model that records withdrawal itself as a loss occurrence.
  · intro x t
    exact Iff.rfl
  · simp [Destroys, WithdrawalLaw.withdrawalAsLoss]
  · intro x n hBefore hGone
    cases x with
    | false =>
      have hn : n = 1 := by
        simpa [WithdrawalLaw.withdrawalAsLoss, WithdrawalLaw.history,
          WithdrawalLaw.effectAt] using hBefore
      subst n
      exact ⟨(), by simp [Destroys, WithdrawalLaw.withdrawalAsLoss]⟩
    | true =>
      exact (hGone (by simp [WithdrawalLaw.withdrawalAsLoss,
        WithdrawalLaw.history])).elim
  · intro hNone
    exact hNone () (by simp [Destroys, WithdrawalLaw.withdrawalAsLoss])

end TruthCore.Results.Causality.ConcurrentCessation
