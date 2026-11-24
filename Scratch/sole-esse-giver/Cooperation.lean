import TruthCore.Causality.SoleEsseGiver

/-! Local analyst test. A recipe records the productive inputs of one exercise.
A relay is required to transmit the input. A joint step requires both inputs.
The two switches below distinguish transmission from the secondary's own yield.
No general laws about esse or about causation are assumed. -/
namespace EsseCooperation

open TruthCore.Causality.SoleEsseGiver
open TruthCore.Causality.EsseCauseEfficiency (EfficiencyProfile)

inductive Recipe where
  | principal
  | localYield
  | through (input : Recipe)
  | jointly (left right : Recipe)

def runs (principal localYield transmits : Bool) : Recipe → Bool
  | .principal => principal
  | .localYield => localYield
  | .through input => transmits && runs principal localYield transmits input
  | .jointly left right =>
    runs principal localYield transmits left && runs principal localYield transmits right

/-- Every productive leaf in the actual recipe comes from the principal.
The interior of the tree may contain indispensable cooperating instruments. -/
def allFromPrincipal : Recipe → Prop
  | .principal => True
  | .localYield => False
  | .through input => allFromPrincipal input
  | .jointly left right => allFromPrincipal left ∧ allFromPrincipal right

theorem isolatedYieldTest (r : Recipe) :
    runs true false true r = true ↔ allFromPrincipal r := by
  induction r with
  | principal => simp [runs, allFromPrincipal]
  | localYield => simp [runs, allFromPrincipal]
  | through input ih => simpa [runs, allFromPrincipal] using ih
  | jointly left right ihL ihR => simp [runs, allFromPrincipal, ihL, ihR]

def transmitted : Recipe := .through .principal
def supplemented : Recipe := .jointly .principal (.through .localYield)

/-- Disabling the whole secondary, which also breaks transmission, never
distinguishes the histories. For both, disabling the principal stops delivery. -/
theorem wholeAgentTests (p localYield : Bool) :
    runs true true true transmitted = true ∧ runs true true true supplemented = true ∧
    runs p localYield false transmitted = false ∧ runs p localYield false supplemented = false ∧
    runs false localYield true transmitted = false ∧ runs false localYield true supplemented = false := by
  cases p <;> cases localYield <;> decide

inductive Bearer where | giver | secondary | recipient
  deriving DecidableEq
open Bearer

def acts (c x : Bearer) : Prop :=
  (c = giver ∧ x ≠ giver) ∨ (c = secondary ∧ x = recipient)

def profile : EfficiencyProfile Bearer Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => acts c x
  essenceOf := fun _ => false
  esseOf := fun x => decide (x ≠ giver)
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()
  EfficientlyCausesEsse := acts

abbrev participates (x : Bearer) := x ≠ giver
abbrev owns (x : Bearer) := x = giver

/-- At the secondary itself the principal supplies the only productive input.
At the recipient use the named recipe. Only the giver's totality is at issue. -/
def total (r : Recipe) (c x : Bearer) (_ : Unit) : Prop :=
  c = giver ∧ (x = secondary ∨ (x = recipient ∧ allFromPrincipal r))

theorem sameSoleGiver : SoleEssentialGiver profile.toProfile participates owns giver := by
  refine ⟨⟨recipient, trivial, by decide⟩, ?_⟩
  intro x _ hx
  exact ⟨⟨Ne.symm hx, trivial, rfl, Or.inl ⟨rfl, hx⟩⟩, fun _ _ _ h _ => h⟩

theorem targetTest (r : Recipe) :
    EssentialGivingIsEfficientAndTotal profile participates owns (total r) ↔
      runs true false true r = true := by
  rw [isolatedYieldTest]
  constructor
  · intro h
    have htotal := (h giver recipient trivial (by decide) (by decide) trivial rfl
      (Or.inl ⟨rfl, by decide⟩)).2
    exact htotal.2.resolve_left (by decide) |>.2
  · intro h c x _ hx _ _ hc he
    refine ⟨he, hc, ?_⟩
    cases x with
    | giver => exact False.elim (hx rfl)
    | secondary => exact Or.inl rfl
    | recipient => exact Or.inr ⟨rfl, h⟩

theorem opposedVerdicts :
    EssentialGivingIsEfficientAndTotal profile participates owns (total transmitted) ∧
    ¬ EssentialGivingIsEfficientAndTotal profile participates owns (total supplemented) := by
  exact ⟨(targetTest transmitted).2 rfl, fun h => Bool.noConfusion ((targetTest supplemented).1 h)⟩

#print axioms isolatedYieldTest
#print axioms wholeAgentTests
#print axioms sameSoleGiver
#print axioms targetTest
#print axioms opposedVerdicts
end EsseCooperation
