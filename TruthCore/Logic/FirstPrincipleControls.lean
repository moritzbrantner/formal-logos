module

public import TruthCore.Logic.FirstPrincipleRoles
public import TruthCore.Logic.RegressDomains

/-!
# Local demands for explanation and ontic requirements

The Boolean assignments compare conditions that obtain, stipulated prerequisites,
and the separate fact that a rule's conclusion is justified.
-/

@[expose] public section

namespace TruthCore.Logic.FirstPrincipleControls

open TruthCore.Logic.FirstPrincipleRoles
open TruthCore.Explanation.PSRStrength
open TruthCore.Logic.RegressDomains

theorem rejectedFactFails {W B F : Type} {A : Arena W B F} {w : W} {f : F}
    (h : LocalInexplicabilityRejection A w f) : ¬ A.holds w f :=
  fun hf => h.unexplained (h.demand hf)

theorem explanationExcludesRejection {W B F : Type} {A : Arena W B F} {w : W} {f : F}
    (he : Explained A w f) : ¬ LocalInexplicabilityRejection A w f :=
  fun h => h.unexplained he

theorem unexplainedFactDefeatsLocalDemand {W B F : Type} {A : Arena W B F} {w : W} {f : F}
    (ht : A.holds w f) (he : ¬ Explained A w f) :
    ¬ (A.holds w f → Explained A w f) := fun hd => he (hd ht)

def failedRequirement : OnticRequirements Unit Bool :=
  ⟨fun _ c => c = true, fun _ d p => d = true ∧ p = false⟩
theorem unmetPrerequisite : ¬ RequirementsRespectedAt failedRequirement () := by
  intro h
  have bad : false = true := h true false ⟨rfl, rfl⟩ rfl
  cases bad

def allActual (edge : Bool) : OnticRequirements Unit Bool :=
  ⟨fun _ _ => True, fun _ _ _ => edge = true⟩
theorem respectedWithEdge : RequirementsRespectedAt (allActual true) () := fun _ _ _ _ => True.intro
theorem respectedWithoutEdge : RequirementsRespectedAt (allActual false) () := fun _ _ _ _ => True.intro
theorem requirementVariesAtFixedActuality : (allActual true).requires () true false ∧
    ¬ (allActual false).requires () true false := by
  constructor
  · rfl
  · intro h
    cases h

def mereRule : Justification Bool where
  Rule := Unit
  premise := fun _ p => p = true
  conclusion := fun _ => false
  noninferential := fun _ => False
  justified := fun _ => False
theorem ruleAloneDoesNotJustify : mereRule.inferential true false ∧ ¬ mereRule.justified false :=
  ⟨⟨(), rfl, rfl⟩, fun h => h⟩

end TruthCore.Logic.FirstPrincipleControls
