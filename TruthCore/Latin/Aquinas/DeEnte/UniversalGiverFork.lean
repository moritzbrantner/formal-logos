module

public import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia
public import TruthCore.Greek.Aristotle.Metaphysics
public import TruthCore.Causality.GroundingEdgeScope

@[expose] public section
namespace TruthCore.Latin.Aquinas.DeEnte.UniversalGiverFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.SelectedSourcePath (SelectedForksJoinInOneStep)
open ClosedEsseSource (esseCauseGraph)

variable {B P R : Type}

/-- For this same maximal universal giver, the strict fork rule on a selected
recipient's complete actual esse ancestry holds precisely when every actual
esse edge into that recipient comes from the giver. Edges use the supplied
CausesIn in the esse respect. Its productive interpretation is open. -/
def SameGiverForkCriterion (p : Profile B P R) (MoreIn : R → B → B → Prop) : Prop :=
  ∃ s, IsMaximumIn p.InAct MoreIn p.esse s ∧
    CausesAllInGenus p.InAct p.CausesIn p.esse s ∧
    ∀ x : {b // ActualConcrete (esseCauseGraph p) () b},
      SelectedForksJoinInOneStep (esseCauseGraph p) () x ↔
        ∀ y, ActualEsseCause p y x.val → y = s

/-- In this three-bearer interpretation the first giver supplies both others.
The intermediate also supplies the last. The strict order calibrates causal
ascent, and all three exist. -/
def level : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

def levelProfile := ClosedEsseSource.controlProfile (fun y x => level y < level x)

def levelMore (_ : Unit) (y x : Option Bool) := level y < level x

def SecondaryGiverControl : Prop :=
  MaximeEnsCausesBeingOfAllReading levelProfile.InAct levelMore levelProfile.CausesIn () ∧
  TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
    levelProfile.CausesIn levelMore ∧
  ActualEsseCause levelProfile none (some false) ∧
  ActualEsseCause levelProfile none (some true) ∧
  ActualEsseCause levelProfile (some false) (some true) ∧
  ¬ SelectedForksJoinInOneStep (esseCauseGraph levelProfile) ()
      ⟨some true, trivial, trivial⟩

end TruthCore.Latin.Aquinas.DeEnte.UniversalGiverFork
