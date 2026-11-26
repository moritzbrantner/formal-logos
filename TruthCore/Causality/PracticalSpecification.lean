module

public import TruthCore.Causality.ThroughWill

/-! # Practical specification of universal esse giving

An analyst model of conjunctive fulfillment conditions. A practical standard
can demand someone's being as a bare output, as a good of that beneficiary,
or as ordered to a selected end. These are roles in a proposed specification.
Omission tests compare descriptions of fulfillment, with no claim that the
edited description is a possible world or a feasible production.
-/

@[expose] public section

namespace TruthCore.Causality.PracticalSpecification

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.ThroughWill (RationallyGivesAt)
open TruthCore.Causality.WillVersusChance (AgencyFrame)

/-- Clauses distinguished by the reason for counting an output as a success.
`output` checks production, `benefit` counts a respect as the recipient's own
good, and `toward` checks placement of the effect in an order to an end.
No inclusion between these roles is built into the model. -/
inductive Clause (B R E : Type)
  | output (x : B)
  | benefit (x : B) (r : R)
  | toward (x : B) (e : E)

/-- Primitive practical interpretation. `Requirement` gives the independently
specified conjunctive standard. `ApprehendsAsGood` supplies the same giver's
actual evaluative apprehension of that standard. `SpecifiesGiving` says it
actually governs the giving of this effect as the measure of fulfillment,
not merely as an accurate forecast. `Realized` marks satisfied clauses in
the giving's context. None of these fields is defined by the case's willing
or direction relations, and none makes a claim about absolute necessity. -/
structure Plan (W B R E K : Type) where
  Requirement : K → Clause B R E → Prop
  ApprehendsAsGood : W → B → K → Prop
  SpecifiesGiving : W → B → B → K → Prop
  Realized : W → B → B → Clause B R E → Prop

variable {W B T R S P E K : Type}

/-- Satisfaction of an independently specified conjunctive standard. -/
def Meets (M : Plan W B R E K) (k : K) (description : Clause B R E → Prop) : Prop :=
  ∀ c, M.Requirement k c → description c

/-- Successful giving governed by an apprehended standard. The actual
operative relation remains primitive. -/
def Governing (M : Plan W B R E K) (w : W) (g x : B) (k : K) : Prop :=
  M.ApprehendsAsGood w g k ∧ M.SpecifiesGiving w g x k ∧ Meets M k (M.Realized w g x)

/-- OPEN application to each selected-world rational giving of a distinct
being in act in esse. One plan may govern the giving of many effects. -/
def RationalGivingHasPlan (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (M : Plan W B R E K) (InAct : B → R → Prop) (w : W) : Prop :=
  ∀ g x, x ≠ g → InAct x F.esse → RationallyGivesAt F A w g x → ∃ k, Governing M w g x k

/-- Preserve the actual fulfillment description except for a specified class
of roles. This is a content comparison with no modal accessibility claim. -/
def Without (realized removed : Clause B R E → Prop) (c : Clause B R E) : Prop :=
  realized c ∧ ¬ removed c

/-- OPEN recipient test: in each successfully governed giving in the
GOD_4 case, remove just the credit for this effect's esse as its own good.
Even with the output and every other role left as before, the plan's
fulfillment standard rejects the edited description. -/
def DivinePlanRejectsBenefitOmission (F : CausalityFrame W B T R)
    (M : Plan W B R E K) (InAct : B → R → Prop) (IsGod : B → Prop) (w : W) : Prop :=
  ∀ g x k, IsGod g → x ≠ g → InAct x F.esse → Governing M w g x k →
    ¬ Meets M k (Without (M.Realized w g x) (· = .benefit x F.esse))

/-- OPEN end test: each successful governing plan for a distinct actual
recipient rejects its description with every end-placement of that recipient
erased. Its bare output, its goods and other recipients' ends stay fixed. -/
def PlanRejectsEndOmission (F : CausalityFrame W B T R) (M : Plan W B R E K)
    (InAct : B → R → Prop) (w : W) : Prop :=
  ∀ g x k, x ≠ g → InAct x F.esse → Governing M w g x k →
    ¬ Meets M k (Without (M.Realized w g x) (fun c => ∃ e, c = .toward x e))

/-- OPEN semantic recognition at w: a benefit required in the standard
actually governing this giving is willed for that beneficiary. The premise
speaks to the point of the adopted requirement and permits subordinate goods. -/
def RequiredBenefitIsWilled (M : Plan W B R E K)
    (WillsGoodFor : B → B → R → Prop) (w : W) : Prop :=
  ∀ g x k r, Governing M w g x k → M.Requirement k (.benefit x r) → WillsGoodFor g x r

/-- OPEN semantic recognition at w: a required end-placement of the effect
in the standard actually governing the giving supplies case direction to
that end. Neither downstream government nor authority is assumed here. -/
def RequiredEndIsDirected (M : Plan W B R E K) (Directs : B → B → E → Prop)
    (w : W) : Prop :=
  ∀ g x k e, Governing M w g x k → M.Requirement k (.toward x e) → Directs g x e

/-- Direction from the rational exercise of actually giving esse. Capacity,
intellect and universal causal coverage are unnecessary for this implication. -/
def RationalGivingDirects (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct : B → R → Prop) (Directs : B → B → E → Prop) (w : W) : Prop :=
  ∀ g x, x ≠ g → InAct x F.esse → RationallyGivesAt F A w g x → ∃ e, Directs g x e

namespace Control

open TruthCore.Causality.ThroughWill (DivineRationalGivingWillsEsseFor RationalUniversalGivingDirects)
open TruthCore.Causality.ThroughWill.Control (model agency acts intellect will rational)

/-- Preserve the fixed rational output in the existing two-world model.
The standard always includes the bare output and the source's self-good.
Apprehension and satisfaction are populated even in the foreseen profile.
The switches vary operative use and the two requirements separately. -/
def plan (operative benefit endRole : Bool) : Plan Bool Bool Unit Unit Unit where
  Requirement := fun _ c => match c with
    | .output x => x = true
    | .benefit x _ => x = false ∨ benefit = true
    | .toward x _ => x = true ∧ endRole = true
  ApprehendsAsGood := fun _ g _ => g = false
  SpecifiesGiving := fun _ g x _ => g = false ∧ x = true ∧ operative = true
  Realized := fun _ _ _ _ => True

/-- The source's self-directed case remains populated when recognition of
the distinct recipient is switched off. -/
def wills (recipient : Bool) (g x : Bool) (_ : Unit) : Prop :=
  g = false ∧ (x = false ∨ recipient = true)

def directs (recipient : Bool) (g x : Bool) (_ : Unit) : Prop :=
  g = false ∧ (x = false ∨ recipient = true)

def coverage (m : Plan Bool Bool Unit Unit Unit) : Prop :=
  RationalGivingHasPlan (model true false) (agency (some true)) m acts false

def benefitTest (m : Plan Bool Bool Unit Unit Unit) : Prop :=
  DivinePlanRejectsBenefitOmission (model true false) m acts will false

def endTest (m : Plan Bool Bool Unit Unit Unit) : Prop :=
  PlanRejectsEndOmission (model true false) m acts false

def recipientBridge (b : Bool) : Prop :=
  DivineRationalGivingWillsEsseFor (model true false) (agency (some true)) acts will
    (wills b) false

def directionBridge (e : Bool) : Prop :=
  RationalUniversalGivingDirects (model true false) (agency (some true)) acts intellect will
    (directs e) false

/-- The foreseen case preserves appraisal and satisfaction of a plan with both
roles. Governing use for the other effect fails. The whole-order case uses a
plan that counts bare output but neither benefit nor end for the other effect.
Each one-role case isolates benefit from direction. The last cases omit one
recognition at a time, with the full standard still governing the same output. -/
def Controls : Prop :=
  rational true false (some true) ∧
  (let m := plan false true true
   m.ApprehendsAsGood false false () ∧ Meets m () (m.Realized false false true) ∧
   ¬ coverage m ∧ benefitTest m ∧ endTest m ∧
   RequiredBenefitIsWilled m (wills false) false ∧ RequiredEndIsDirected m (directs false) false ∧
   ¬ recipientBridge false ∧ ¬ directionBridge false) ∧
  (let m := plan true false false
   coverage m ∧ ¬ benefitTest m ∧ ¬ endTest m ∧
   RequiredBenefitIsWilled m (wills false) false ∧ RequiredEndIsDirected m (directs false) false ∧
   ¬ recipientBridge false ∧ ¬ directionBridge false) ∧
  (let m := plan true false true
   coverage m ∧ ¬ benefitTest m ∧ endTest m ∧
   RequiredBenefitIsWilled m (wills false) false ∧ RequiredEndIsDirected m (directs true) false ∧
   ¬ recipientBridge false ∧ directionBridge true) ∧
  (let m := plan true true false
   coverage m ∧ benefitTest m ∧ ¬ endTest m ∧
   RequiredBenefitIsWilled m (wills true) false ∧ RequiredEndIsDirected m (directs false) false ∧
   recipientBridge true ∧ ¬ directionBridge false) ∧
  (let m := plan true true true
   coverage m ∧ benefitTest m ∧ endTest m ∧
   RequiredBenefitIsWilled m (wills true) false ∧ RequiredEndIsDirected m (directs true) false ∧
   recipientBridge true ∧ directionBridge true ∧
   ¬ RequiredBenefitIsWilled m (wills false) false ∧
   ¬ RequiredEndIsDirected m (directs false) false)

end Control
end TruthCore.Causality.PracticalSpecification
