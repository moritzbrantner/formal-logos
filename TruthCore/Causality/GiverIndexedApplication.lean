module

public import TruthCore.Causality.Q44SourceSupply
public import TruthCore.Latin.Aquinas.DeEnte.RootInterface
public import TruthCore.Case.Catholicism.CausalPerfectionTransfer

/-! Analyst test of the source-supply composition law. Every causal edge is in
one profile, at esse. The existing binary AsCaused classifies a link. The
primitive ternary Through a b c says that this giver a applies b's efficacy in
b's production of c's esse. It represents neither mere prior production of b
nor the totality of conditions for c. Its actual applicability is open. -/

@[expose] public section
namespace TruthCore.Causality.GiverIndexedApplication
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.Q44SourceSupply (ActualEsseCauseComposes)

variable {B P R : Type}

/-- Open binary law. The second link is an actual per se link, while a can
be ANY actual distinct giver of its intermediate b. Which giver applies b in
this exercise is not represented by AsCaused. -/
def PerSeComposition (f : Profile B P R) (AsCaused : B → B → Prop) : Prop :=
  ∀ a b c, ActualEsseCause f a b → PerSeActualEsseCause f AsCaused b c →
    f.CausesIn a c f.esse

/-- Open causal-credit interface for an individually identified application.
The effective relata and respect are those of the two actual esse links. -/
def AppliedGiverComposes (f : Profile B P R) (Through : B → B → B → Prop) : Prop :=
  ∀ a b c, ActualEsseCause f a b → ActualEsseCause f b c → Through a b c →
    f.CausesIn a c f.esse

/-- Open warrant for applying the indexed law to every preceding giver. A
binary classification of the downstream exercise carries no such index. -/
def EachGiverApplies (f : Profile B P R) (AsCaused : B → B → Prop)
    (Through : B → B → B → Prop) : Prop :=
  ∀ a b c, ActualEsseCause f a b → PerSeActualEsseCause f AsCaused b c → Through a b c

namespace Control
open TruthCore.Case.Catholicism (TransferRole)

/-- All four roles have actual esse. Source and supporter give esse to the
producer. The producer gives esse to the recipient. The supporter also gives
esse to the recipient. The switch adds that final edge for the source. -/
def cause (both : Bool) (a b : TransferRole) : Prop :=
  (b = .producer ∧ (a = .source ∨ a = .supporter)) ∨
  (b = .recipient ∧ (a = .producer ∨ a = .supporter ∨ (both = true ∧ a = .source)))

def profile (both : Bool) : Profile TransferRole Unit Unit where
  InAct := fun _ _ => True
  CausesIn := fun a b _ => cause both a b
  esse := ()
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  essentialPrinciplesAloneSufficeForEsse := fun _ => False

def asCaused (b c : TransferRole) : Prop := b = .producer ∧ c = .recipient

def through (both : Bool) (a b c : TransferRole) : Prop :=
  asCaused b c ∧ (a = .supporter ∨ (both = true ∧ a = .source))

/-- Shared positive conditions. For this finite interpretation the binary
per se marker is exactly the projection of indexed application by some
actual incoming giver; the downstream actual edge is exhibited explicitly.
Neither equality of essence and esse in the unused profile slots nor time
plays a role in this comparison. -/
def Background (both : Bool) : Prop :=
  ActualEsseCause (profile both) .source .producer ∧
  ActualEsseCause (profile both) .supporter .producer ∧
  PerSeActualEsseCause (profile both) asCaused .producer .recipient ∧
  through both .supporter .producer .recipient ∧
  (∀ b c, asCaused b c ↔ ∃ a, ActualEsseCause (profile both) a b ∧ through both a b c) ∧
  CausedEsseCauseCausesAsCaused (profile both) asCaused ∧
  AppliedGiverComposes (profile both) (through both)

/-- Give only the supporter the application, then add application AND the
corresponding effective edge for the source. A third assignment retains the
added edge while withholding source application. Every row keeps the original
givers to the producer and the producer's per se outgoing edge. -/
def Certificate : Prop :=
  Background false ∧ ¬ through false .source .producer .recipient ∧
  ¬ (profile false).CausesIn .source .recipient () ∧
  ¬ EachGiverApplies (profile false) asCaused (through false) ∧
  ¬ PerSeComposition (profile false) asCaused ∧ ¬ ActualEsseCauseComposes (profile false) ∧
  Background true ∧ through true .source .producer .recipient ∧
  (profile true).CausesIn .source .recipient () ∧
  EachGiverApplies (profile true) asCaused (through true) ∧
  PerSeComposition (profile true) asCaused ∧ ActualEsseCauseComposes (profile true) ∧
  (∀ b c, asCaused b c ↔ ∃ a, ActualEsseCause (profile true) a b ∧ through false a b c) ∧
  AppliedGiverComposes (profile true) (through false) ∧
  ¬ EachGiverApplies (profile true) asCaused (through false)
end Control
end TruthCore.Causality.GiverIndexedApplication
