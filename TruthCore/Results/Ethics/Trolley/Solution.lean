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

/-! ### Advertised results -/

/-- Act consequentialism with the footbridge facts makes pushing permissible. -/
theorem acFootbridge (F : Scenario → Case) (P : Scenario → Prop)
    (hAC : ActConsequentialismGoverns F P) (hF : FootbridgeFacts F) :
    FootbridgePermissible P := by
  unfold FootbridgePermissible
  rw [hAC .footbridge, hF]
  decide

/-- Act consequentialism with the transplant facts makes harvesting permissible. -/
theorem acTransplant (F : Scenario → Case) (P : Scenario → Prop)
    (hAC : ActConsequentialismGoverns F P) (hT : TransplantFacts F) :
    TransplantPermissible P := by
  unfold TransplantPermissible
  rw [hAC .transplant, hT]
  decide

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
  unfold SwitchImpermissible
  rw [hN .switch, hS]
  exact fun h => h switch_killsCausally

/-- The switch verdict and facts exclude causal no-killing deontology. -/
theorem switchVerdictExcludesCausalNoKilling (F : Scenario → Case) (P : Scenario → Prop)
    (hS : SwitchFacts F) (hV : SwitchPermissible P) :
    CausalNoKillingFails F P :=
  fun hN => causalNoKillingSwitch F P hN hS hV

theorem doubleEffectTriad (F : Scenario → Case) (P : Scenario → Prop)
    (hD : DoubleEffectGoverns F P) (hS : SwitchFacts F) (hFb : FootbridgeFacts F)
    (hT : TransplantFacts F) : CommonTriadVerdicts P := by
  refine ⟨?_, ?_, ?_⟩
  · show P .switch; rw [hD .switch, hS]; exact de_switch
  · show ¬ P .footbridge; rw [hD .footbridge, hFb]; exact de_footbridge
  · show ¬ P .transplant; rw [hD .transplant, hT]; exact de_transplant

theorem intentionDoubleEffectTriad (F : Scenario → Case) (P : Scenario → Prop)
    (hD : IntentionDoubleEffectGoverns F P) (hS : SwitchFacts F) (hFb : FootbridgeFacts F)
    (hT : TransplantFacts F) : CommonTriadVerdicts P := by
  refine ⟨?_, ?_, ?_⟩
  · show P .switch; rw [hD .switch, hS]; exact ide_switch
  · show ¬ P .footbridge; rw [hD .footbridge, hFb]; exact ide_footbridge
  · show ¬ P .transplant; rw [hD .transplant, hT]; exact ide_transplant

theorem meansTriad (F : Scenario → Case) (P : Scenario → Prop)
    (hM : MeansPrincipleGoverns F P) (hS : SwitchFacts F) (hFb : FootbridgeFacts F)
    (hT : TransplantFacts F) : CommonTriadVerdicts P := by
  refine ⟨?_, ?_, ?_⟩
  · show P .switch; rw [hM .switch, hS]; exact mp_switch
  · show ¬ P .footbridge; rw [hM .footbridge, hFb]; exact mp_footbridge
  · show ¬ P .transplant; rw [hM .transplant, hT]; exact mp_transplant

theorem redirectionTriad (F : Scenario → Case) (P : Scenario → Prop)
    (hR : RedirectionGoverns F P) (hS : SwitchFacts F) (hFb : FootbridgeFacts F)
    (hT : TransplantFacts F) : CommonTriadVerdicts P := by
  refine ⟨?_, ?_, ?_⟩
  · show P .switch; rw [hR .switch, hS]; exact rd_switch
  · show ¬ P .footbridge; rw [hR .footbridge, hFb]; exact rd_footbridge
  · show ¬ P .transplant; rw [hR .transplant, hT]; exact rd_transplant

theorem doubleEffectLoop (F : Scenario → Case) (P : Scenario → Prop)
    (hD : DoubleEffectGoverns F P) (hL : LoopFacts F) : LoopImpermissible P := by
  show ¬ P .loop; rw [hD .loop, hL]; exact de_loop

theorem meansLoop (F : Scenario → Case) (P : Scenario → Prop)
    (hM : MeansPrincipleGoverns F P) (hL : LoopFacts F) : LoopImpermissible P := by
  show ¬ P .loop; rw [hM .loop, hL]; exact mp_loop

theorem intentionDoubleEffectLoop (F : Scenario → Case) (P : Scenario → Prop)
    (hD : IntentionDoubleEffectGoverns F P) (hL : LoopFacts F) : LoopPermissible P := by
  show P .loop; rw [hD .loop, hL]; exact ide_loop

theorem redirectionLoop (F : Scenario → Case) (P : Scenario → Prop)
    (hR : RedirectionGoverns F P) (hL : LoopFacts F) : LoopPermissible P := by
  show P .loop; rw [hR .loop, hL]; exact rd_loop

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
  refine ⟨⟨⟨rfl, by decide, sideEffect_notMeans, by decide⟩, de_footbridge,
      ⟨sideEffect_notMeans, by decide⟩, mp_footbridge, by decide, by decide⟩,
    ⟨fun h => h.2.2.1 (chainMeans _ rfl),
      ⟨rfl, by decide, fun h => absurd h.1 (by decide), by decide⟩⟩,
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
    ⟨loop_means _ rfl, by decide, switch_notMeans _ rfl, by decide⟩⟩

end TruthCore.Results.Ethics.Trolley
