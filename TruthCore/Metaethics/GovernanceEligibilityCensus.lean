module

public import TruthCore.Metaethics.GoodnessStandardPriority

/-!
# Two-profile eligibility and selection controls

The tables stipulate eligibility and the compared data projection. Selection
and eligibility are separate. The consent row concerns a single waivable
claim under the note's fixed justifying conditions.
-/

@[expose] public section

namespace TruthCore.Metaethics.GovernanceEligibilityCensus

open TruthCore.Logic.CorrectionCriterion (AdmitsCriterion FiberInvariant)

abbrev Profile := Fin 2
abbrev OptionIndex := Fin 2
abbrev Table := Profile → OptionIndex → Bool

def factors (p : Table) (data : Profile → Fin 2) : Bool :=
  decide (∀ s t o, data s = data t → p s o = p t o)

theorem factors_iff (p : Table) (data : Profile → Fin 2) :
    factors p data = true ↔ ∀ o, AdmitsCriterion data (fun s => p s o = true) := by
  rw [factors, decide_eq_true_eq]
  have criterion (o : OptionIndex) : AdmitsCriterion data (fun s => p s o = true) ↔
      FiberInvariant data (fun s => p s o = true) :=
    TruthCore.Results.Logic.CorrectionCriterion.characterization.1 Profile (Fin 2)
      data (fun s => p s o = true)
  constructor
  · intro h o
    exact (criterion o).mpr (fun s t same => Bool.eq_iff_iff.mp (h s t o same))
  · intro h s t o same
    exact Bool.eq_iff_iff.mpr ((criterion o).mp (h o) s t same)

def constantData (_ : Profile) : Fin 2 := 0
def kindData (s : Profile) : Fin 2 := s

def tables : List Table := (List.range 16).map fun mask s o => mask.testBit (2 * s.val + o.val)

def singletonRows (p : Table) : Bool := decide (∀ s, p s 0 != p s 1)

theorem census :
    tables.length = 16 ∧ (tables.filter (fun p => factors p constantData)).length = 4 ∧
    (tables.filter singletonRows).length = 4 ∧
    (tables.filter (fun p => singletonRows p && factors p constantData)).length = 2 := by
  decide +kernel

def flip : Table := fun s o => (s == 0 && o == 0) || (s == 1 && o == 1)
def fixed : Table := fun _ o => o == 0
def tied : Table := fun _ _ => true
def empty : Table := fun _ _ => false

theorem rows :
    factors flip constantData = false ∧ factors flip kindData = true ∧
    (∀ s o, flip s o = (kindData s == o)) ∧
    factors fixed constantData = true ∧ factors tied constantData = true ∧
    factors empty constantData = true ∧ (∀ s o, empty s o = false) ∧
    (∀ s, tied s s = true) ∧ kindData 0 ≠ kindData 1 := by
  decide +kernel

/-- Profile 0 uses the bystander's token, profile 1 the claimant's valid
consent. Option 0 proceeds, option 1 refrains. -/
def eligibleWithConsent (holderConsented : Bool) (o : OptionIndex) : Bool :=
  holderConsented || o == 1

def consentTable : Table := fun s => eligibleWithConsent (s == 1)

theorem consent :
    consentTable 0 0 = false ∧ consentTable 0 1 = true ∧
    consentTable 1 0 = true ∧ consentTable 1 1 = true ∧
    factors consentTable constantData = false ∧ factors consentTable kindData = true := by
  decide +kernel

end TruthCore.Metaethics.GovernanceEligibilityCensus
