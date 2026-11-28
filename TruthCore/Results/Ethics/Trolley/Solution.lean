module

public import TruthCore.Ethics.Trolley

/-! Verdicts derived from rival principles on the typed trolley cases
(analyst formulation; attribution deferred). Every verdict is computed from the
case structure in `TruthCore.Ethics.Trolley`; no theorem asserts that a
principle or a verdict is true. -/

@[expose] public section

namespace TruthCore.Results.Ethics.Trolley
open TruthCore.Ethics.Trolley

/-- A set containing the start, closed under the relation, and missing the target
shows that the target is unreachable. -/
theorem not_reach_of_closed {α : Type} {r : α → α → Prop} (S : α → Prop) {a b : α}
    (ha : S a) (hb : ¬ S b) (hS : ∀ x y, S x → r x y → S y) :
    ¬ Relation.ReflTransGen r a b := by
  intro h
  have key : ∀ c, Relation.ReflTransGen r a c → S c := by
    intro c hc
    induction hc with
    | refl => exact ha
    | tail _ hst ih => exact hS _ _ ih hst
  exact hb (key b h)

/-! ### Structural facts of each graph -/

theorem switch_killsCausally : KillsCausally switchCase :=
  (Relation.ReflTransGen.single (show Step switchCase .act .redirect from rfl)).tail
    (show Step switchCase .redirect .harmOne from rfl)

theorem switch_notNewThreat (c : Case) (h : c.edge = switchCase.edge) :
    ¬ KillsByNewThreat c := by
  refine not_reach_of_closed (fun e => e = .act) rfl (by decide) ?_
  intro x y hx hxy
  obtain ⟨he, hne⟩ := hxy
  rw [h] at he
  revert hx he hne
  cases x <;> cases y <;> decide

theorem switch_notMeans (c : Case) (h : c.edge = switchCase.edge) :
    ¬ HarmIsCausalMeans c := by
  intro ⟨_, hAvoid⟩
  apply hAvoid
  refine (Relation.ReflTransGen.single (b := .redirect) ?_).tail ?_
  · exact ⟨by rw [h]; rfl, by decide⟩
  · exact ⟨by rw [h]; rfl, by decide⟩

theorem chainMeans (c : Case) (h : c.edge = footbridgeCase.edge) :
    HarmIsCausalMeans c := by
  refine ⟨?_, ?_⟩
  · refine ((Relation.ReflTransGen.single (b := .harmOne) ?_).tail (c := .stopThreat) ?_).tail ?_ <;>
      (show c.edge _ _ = true; rw [h]; rfl)
  · refine not_reach_of_closed (fun e => e = .act) rfl (by decide) ?_
    intro x y hx hxy
    obtain ⟨he, hne⟩ := hxy
    rw [h] at he
    revert hx he hne
    cases x <;> cases y <;> decide

theorem chainNewThreat (c : Case) (h : c.edge = footbridgeCase.edge) :
    KillsByNewThreat c :=
  Relation.ReflTransGen.single ⟨by rw [h]; rfl, by decide⟩

theorem loop_means (c : Case) (h : c.edge = loopCase.edge) : HarmIsCausalMeans c := by
  refine ⟨?_, ?_⟩
  · refine (((Relation.ReflTransGen.single (b := .redirect) ?_).tail (c := .harmOne) ?_).tail
      (c := .stopThreat) ?_).tail ?_ <;>
      (show c.edge _ _ = true; rw [h]; rfl)
  · refine not_reach_of_closed (fun e => e = .act ∨ e = .redirect) (Or.inl rfl)
      (by decide) ?_
    intro x y hx hxy
    obtain ⟨he, hne⟩ := hxy
    rw [h] at he
    revert hx he hne
    cases x <;> cases y <;> decide

theorem loop_notNewThreat (c : Case) (h : c.edge = loopCase.edge) :
    ¬ KillsByNewThreat c := by
  refine not_reach_of_closed (fun e => e = .act) rfl (by decide) ?_
  intro x y hx hxy
  obtain ⟨he, hne⟩ := hxy
  rw [h] at he
  revert hx he hne
  cases x <;> cases y <;> decide

theorem sideEffect_notMeans : ¬ HarmIsCausalMeans sideEffectFootbridge := by
  intro ⟨_, hAvoid⟩
  apply hAvoid
  exact (Relation.ReflTransGen.single (b := .stopThreat) ⟨rfl, by decide⟩).tail ⟨rfl, by decide⟩

theorem sideEffect_reaches : Reach sideEffectFootbridge .act .saveFive :=
  (Relation.ReflTransGen.single (show Step sideEffectFootbridge .act .stopThreat from rfl)).tail
    (show Step sideEffectFootbridge .stopThreat .saveFive from rfl)

/-! ### Principle values on the four cases -/

theorem de_switch : DoubleEffect switchCase :=
  ⟨rfl, by decide, switch_notMeans _ rfl, by decide⟩
theorem de_footbridge : ¬ DoubleEffect footbridgeCase :=
  fun h => h.2.2.1 (chainMeans _ rfl)
theorem de_transplant : ¬ DoubleEffect transplantCase :=
  fun h => h.2.2.1 (chainMeans _ rfl)
theorem de_loop : ¬ DoubleEffect loopCase :=
  fun h => h.2.2.1 (loop_means _ rfl)

theorem ide_switch : IntentionDoubleEffect switchCase :=
  ⟨rfl, by decide, fun h => absurd h.1 (by decide), by decide⟩
theorem ide_footbridge : ¬ IntentionDoubleEffect footbridgeCase :=
  fun h => h.2.1 rfl
theorem ide_transplant : ¬ IntentionDoubleEffect transplantCase :=
  fun h => h.2.1 rfl
theorem ide_loop : IntentionDoubleEffect loopCase :=
  ⟨rfl, by decide, fun h => absurd h.1 (by decide), by decide⟩

theorem mp_switch : MeansPrinciple switchCase := ⟨switch_notMeans _ rfl, by decide⟩
theorem mp_footbridge : ¬ MeansPrinciple footbridgeCase := fun h => h.1 (chainMeans _ rfl)
theorem mp_transplant : ¬ MeansPrinciple transplantCase := fun h => h.1 (chainMeans _ rfl)
theorem mp_loop : ¬ MeansPrinciple loopCase := fun h => h.1 (loop_means _ rfl)

theorem rd_switch : Redirection switchCase := ⟨switch_notNewThreat _ rfl, by decide⟩
theorem rd_footbridge : ¬ Redirection footbridgeCase :=
  fun h => h.1 (chainNewThreat _ rfl)
theorem rd_transplant : ¬ Redirection transplantCase :=
  fun h => h.1 (chainNewThreat _ rfl)
theorem rd_loop : Redirection loopCase := ⟨loop_notNewThreat _ rfl, by decide⟩

/-! ### Reading a governed assignment -/

theorem gov_pos {X : Case → Prop} {F : Scenario → Case} {P : Scenario → Prop} {k : Scenario}
    {c : Case} (h : Governs X F P) (hk : F k = c) (hc : X c) : P k :=
  (h k).mpr (hk ▸ hc)

theorem gov_neg {X : Case → Prop} {F : Scenario → Case} {P : Scenario → Prop} {k : Scenario}
    {c : Case} (h : Governs X F P) (hk : F k = c) (hc : ¬ X c) : ¬ P k :=
  fun hp => hc (hk ▸ (h k).mp hp)

/-! ### Advertised results -/

/-- Act consequentialism with the footbridge facts makes pushing permissible. -/
theorem acFootbridge (F : Scenario → Case) (P : Scenario → Prop)
    (hAC : ActConsequentialismGoverns F P) (hF : FootbridgeFacts F) :
    FootbridgePermissible P := by
  exact gov_pos hAC hF (by decide)

/-- Act consequentialism with the transplant facts makes harvesting permissible. -/
theorem acTransplant (F : Scenario → Case) (P : Scenario → Prop)
    (hAC : ActConsequentialismGoverns F P) (hT : TransplantFacts F) :
    TransplantPermissible P := by
  exact gov_pos hAC hT (by decide)

/-- The footbridge verdict and facts exclude act consequentialism. -/
theorem footbridgeVerdictExcludesAC (F : Scenario → Case) (P : Scenario → Prop)
    (hF : FootbridgeFacts F) (hV : FootbridgeImpermissible P) :
    ActConsequentialismFails F P :=
  fun hAC => hV (acFootbridge F P hAC hF)

/-- The transplant verdict and facts exclude act consequentialism. -/
theorem transplantVerdictExcludesAC (F : Scenario → Case) (P : Scenario → Prop)
    (hT : TransplantFacts F) (hV : TransplantImpermissible P) :
    ActConsequentialismFails F P :=
  fun hAC => hV (acTransplant F P hAC hT)

/-- Causal no-killing deontology forbids switching. -/
theorem causalNoKillingSwitch (F : Scenario → Case) (P : Scenario → Prop)
    (hN : CausalNoKillingGoverns F P) (hS : SwitchFacts F) :
    SwitchImpermissible P := by
  exact gov_neg hN hS (fun h => h switch_killsCausally)

/-- The switch verdict and facts exclude causal no-killing deontology. -/
theorem switchVerdictExcludesCausalNoKilling (F : Scenario → Case) (P : Scenario → Prop)
    (hS : SwitchFacts F) (hV : SwitchPermissible P) :
    CausalNoKillingFails F P :=
  fun hN => causalNoKillingSwitch F P hN hS hV

theorem doubleEffectTriad (F : Scenario → Case) (P : Scenario → Prop)
    (hD : DoubleEffectGoverns F P) (hS : SwitchFacts F) (hFb : FootbridgeFacts F)
    (hT : TransplantFacts F) : CommonTriadVerdicts P := by
  refine ⟨?_, ?_, ?_⟩
  · exact gov_pos hD hS de_switch
  · exact gov_neg hD hFb de_footbridge
  · exact gov_neg hD hT de_transplant

theorem intentionDoubleEffectTriad (F : Scenario → Case) (P : Scenario → Prop)
    (hD : IntentionDoubleEffectGoverns F P) (hS : SwitchFacts F) (hFb : FootbridgeFacts F)
    (hT : TransplantFacts F) : CommonTriadVerdicts P := by
  refine ⟨?_, ?_, ?_⟩
  · exact gov_pos hD hS ide_switch
  · exact gov_neg hD hFb ide_footbridge
  · exact gov_neg hD hT ide_transplant

theorem meansTriad (F : Scenario → Case) (P : Scenario → Prop)
    (hM : MeansPrincipleGoverns F P) (hS : SwitchFacts F) (hFb : FootbridgeFacts F)
    (hT : TransplantFacts F) : CommonTriadVerdicts P := by
  refine ⟨?_, ?_, ?_⟩
  · exact gov_pos hM hS mp_switch
  · exact gov_neg hM hFb mp_footbridge
  · exact gov_neg hM hT mp_transplant

theorem redirectionTriad (F : Scenario → Case) (P : Scenario → Prop)
    (hR : RedirectionGoverns F P) (hS : SwitchFacts F) (hFb : FootbridgeFacts F)
    (hT : TransplantFacts F) : CommonTriadVerdicts P := by
  refine ⟨?_, ?_, ?_⟩
  · exact gov_pos hR hS rd_switch
  · exact gov_neg hR hFb rd_footbridge
  · exact gov_neg hR hT rd_transplant

theorem doubleEffectLoop (F : Scenario → Case) (P : Scenario → Prop)
    (hD : DoubleEffectGoverns F P) (hL : LoopFacts F) : LoopImpermissible P := by
  exact gov_neg hD hL de_loop

theorem meansLoop (F : Scenario → Case) (P : Scenario → Prop)
    (hM : MeansPrincipleGoverns F P) (hL : LoopFacts F) : LoopImpermissible P := by
  exact gov_neg hM hL mp_loop

theorem intentionDoubleEffectLoop (F : Scenario → Case) (P : Scenario → Prop)
    (hD : IntentionDoubleEffectGoverns F P) (hL : LoopFacts F) : LoopPermissible P := by
  exact gov_pos hD hL ide_loop

theorem redirectionLoop (F : Scenario → Case) (P : Scenario → Prop)
    (hR : RedirectionGoverns F P) (hL : LoopFacts F) : LoopPermissible P := by
  exact gov_pos hR hL rd_loop

theorem jointModels : TriadJointModels := by
  refine ⟨⟨actualCases, fun k => DoubleEffect (actualCases k), fun _ => Iff.rfl,
      rfl, rfl, rfl, rfl, ⟨de_switch, de_footbridge, de_transplant⟩, de_loop⟩,
    ⟨actualCases, fun k => MeansPrinciple (actualCases k), fun _ => Iff.rfl,
      rfl, rfl, rfl, rfl, ⟨mp_switch, mp_footbridge, mp_transplant⟩, mp_loop⟩,
    ⟨actualCases, fun k => IntentionDoubleEffect (actualCases k), fun _ => Iff.rfl,
      rfl, rfl, rfl, rfl, ⟨ide_switch, ide_footbridge, ide_transplant⟩, ide_loop⟩,
    ⟨actualCases, fun k => Redirection (actualCases k), fun _ => Iff.rfl,
      rfl, rfl, rfl, rfl, ⟨rd_switch, rd_footbridge, rd_transplant⟩, rd_loop⟩⟩

theorem controls : TrolleyControls := by
  refine ⟨⟨by funext e; cases e <;> rfl, ⟨rfl, by decide, sideEffect_notMeans, by decide⟩,
      fun h => h.2.2.1 (chainMeans _ rfl),
      ⟨sideEffect_notMeans, by decide⟩, fun h => h.1 (chainMeans _ rfl),
      ⟨rfl, by decide, fun h => absurd h.1 (by decide), by decide⟩,
      ⟨rfl, by decide, fun h => absurd h.1 (by decide), by decide⟩, by decide, by decide⟩,
    ⟨fun h => h.2.2.1 (chainMeans _ rfl),
      ⟨rfl, by decide, fun h => absurd h.1 (by decide), by decide⟩,
      fun h => h.1 (chainNewThreat _ rfl)⟩,
    ⟨fun h => h.2.1 rfl, fun h => h.2.1 rfl,
      ⟨switch_notMeans _ rfl, by decide⟩, ⟨switch_notNewThreat _ rfl, by decide⟩⟩,
    ⟨fun h => absurd h.2.2.2 (by decide), fun h => absurd h.2 (by decide),
      fun h => absurd h.2 (by decide), by decide⟩,
    ⟨switch_killsCausally, switch_notNewThreat _ rfl, chainNewThreat _ rfl,
      chainNewThreat _ rfl⟩,
    ⟨de_loop, mp_loop, ide_loop, rd_loop, loop_means _ rfl, by decide,
      fun h => h.2.1 rfl, ⟨loop_notNewThreat _ rfl, by decide⟩⟩,
    fun _ h => h.1,
    ⟨rfl, rfl⟩,
    ⟨actualCases, fun _ => False, rfl, rfl, rfl, rfl, fun h => h.1⟩,
    ⟨loop_means _ rfl, by decide, switch_notMeans _ rfl, by decide,
      chainMeans _ rfl, rfl, chainMeans _ rfl, rfl⟩,
    ⟨fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide),
      ⟨switch_notMeans _ rfl, by decide⟩, ⟨switch_notNewThreat _ rfl, by decide⟩⟩⟩

end TruthCore.Results.Ethics.Trolley
