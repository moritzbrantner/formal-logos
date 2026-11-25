module

public import TruthCore.Causality.Q44EssentialSource
public import TruthCore.Causality.CartesianAdequacy
public import TruthCore.Causality.EsseCauseEfficiencyPriority
public import TruthCore.Causality.TermSenseForks3

/-! Analyst restriction to the principal giver of participated esse. The selected
source is quantified outside the participant variable. Actuality, participation,
own being, efficient giving, totality and represented degree keep their distinct
roles. Nothing in the source selection orders the bearers. -/

@[expose] public section
namespace TruthCore.Causality.SoleEsseGiver

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.EsseCauseEfficiency (EfficiencyProfile)
open TruthCore.Causality.EsseCauseEfficiencyPriority (EfficientlyCausesEsseIn)
open TruthCore.Causality.CartesianAdequacy (gradesOf)
open TruthCore.Causality.Grades (GradesFrame)

variable {B P R : Type}

/-- Nonvacuity at the actual esse roster. -/
def ActualParticipantExists (f : Profile B P R) (Participated : B → Prop) : Prop :=
  ∃ x, f.InAct x f.esse ∧ Participated x

/-- Candidate principal givers here are actual own-being bearers causing the
esse of a distinct actual participant. Every such giver for any participant
is the same s. Ordinary secondary causes remain unrestricted. -/
def SoleEssentialGiver (f : Profile B P R) (Participated OwnBeing : B → Prop)
    (s : B) : Prop :=
  ActualParticipantExists f Participated ∧
  ∀ x, f.InAct x f.esse → Participated x →
    (s ≠ x ∧ f.InAct s f.esse ∧ OwnBeing s ∧ f.CausesIn s x f.esse) ∧
    ∀ c, c ≠ x → f.InAct c f.esse → OwnBeing c → f.CausesIn c x f.esse → c = s

/-- Open bridge from the q.3 causal role to efficient giving needing no
co-cause in esse. Neither efficiency nor totality means numerical uniqueness. -/
def EssentialGivingIsEfficientAndTotal (q : EfficiencyProfile B P R)
    (Participated OwnBeing : B → Prop) (Total : B → B → R → Prop) : Prop :=
  ∀ c x, q.InAct x q.esse → Participated x → c ≠ x → q.InAct c q.esse →
    OwnBeing c → q.CausesIn c x q.esse → q.EfficientlyCausesEsse c x ∧ Total c x q.esse

/-- Reuse the adequacy interface with only the efficient esse edges. Histories,
other respects and primitive comparisons play no role in represented adequacy. -/
def efficientGrades (q : EfficiencyProfile B P R) : GradesFrame Unit B Unit R :=
  gradesOf q.InAct (fun _ _ _ => False) (EfficientlyCausesEsseIn q) q.esse

/-- The very same actual s bounds the degree of every actual participant.
The positive preorder comparison permits distinct bearers of equal degree. -/
def BoundsParticipatedEsse {D : Type} [Preorder D] (f : Profile B P R)
    (Participated : B → Prop) (degree : R → B → D) (s : B) : Prop :=
  f.InAct s f.esse ∧ ∀ x, f.InAct x f.esse → Participated x → degree f.esse x ≤ degree f.esse s

/-- A populated interpretation with one non-self giver and one recipient.
The two bearers can realize the same represented degree. -/
def EqualDegreeControl : Prop :=
  ∃ (q : EfficiencyProfile Bool Bool Unit) (degree : Unit → Bool → Nat),
    SoleEssentialGiver q.toProfile (· = false) (· = true) true ∧
    EssentialGivingIsEfficientAndTotal q (· = false) (· = true)
      (fun c x _ => c = true ∧ x = false) ∧
    TruthCore.Causality.CartesianAdequacy.AtLeastAsMuchDegreeInTotalCause
      (efficientGrades q) (fun c x _ => c = true ∧ x = false) degree ∧
    BoundsParticipatedEsse q.toProfile (· = false) degree true ∧
    degree () false = degree () true ∧
    q.esseOf true = q.essenceOf true ∧ q.esseOf false ≠ q.essenceOf false ∧
    ¬ TruthCore.Causality.CartesianAdequacy.AtLeastAsMuchDegreeInTotalCause
      (efficientGrades q) (fun c x _ => c = true ∧ x = false)
      (fun _ b => if b then (1 : Nat) else 2)

end TruthCore.Causality.SoleEsseGiver
