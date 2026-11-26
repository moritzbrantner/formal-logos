module

public import TruthCore.Case.Catholicism.AttributesFromEsse
public import TruthCore.Case.Catholicism.MaximalBeingCauseExclusion
public import TruthCore.Causality.CartesianAdequacy
public import TruthCore.Causality.Q44SourceSupply
public import TruthCore.Logic.ExcludedMiddle

@[expose] public section
namespace TruthCore.Case.Catholicism.AncestralEsseAttributes

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

/-- Add the q.3 a.4 essence and esse data to one grades frame. This preserves
its bearer type, actuality, causation and designated esse. -/
def profileOf {W B T R P : Type} (F : GradesFrame W B T R)
    (essenceOf esseOf : B → P) (sufficient : B → Prop) : Profile B P R where
  InAct := F.InAct
  CausesIn := F.CausesIn
  essenceOf := essenceOf
  esseOf := esseOf
  essentialPrinciplesAloneSufficeForEsse := sufficient
  esse := F.esse

namespace Control
open TruthCore.Case.Catholicism.AttributesFromEsse (PerfectInFrame)
open TruthCore.Causality.CartesianAdequacy (gradesOf)
open TruthCore.Causality.Q44SourceSupply.Control (Being chainCause oneIdentity)
open TruthCore.Causality.Q44EssentialSource.Control.Three
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause CommonEsseIsEssenceSource)

def act (x : Being) (r : Option Bool) : Prop := r ≠ some true ∨ x = primary

def cause (c x : Being) (r : Option Bool) : Prop := chainCause c x ∧ act x r

def more (r : Option Bool) (c x : Being) : Prop := r = none ∧ chainCause c x

def grades : GradesFrame Unit Being Unit (Option Bool) := gradesOf act more cause none

def profile : Profile Being Bool (Option Bool) :=
  profileOf grades (fun _ => false) oneIdentity (fun _ => False)

def named (x : Being) : Prop := x = primary

/-- Three actual bearers. The last bearer is actual in a further respect.
Even with transfer along each available edge, the named source has no
direct endpoint edge in being or in that further respect. -/
def ChainControl : Prop :=
  CommonEsseIsEssenceSource profile ∧
    GodIsMaximalInBeing named grades.InAct grades.MoreIn grades.esse ∧
    MaximumHasNoDistinctEsseCause grades.InAct grades.MoreIn grades.CausesIn grades.esse ∧
    ActualityOnlyInsofarAsBeingReading grades.InAct grades.esse ∧
    PerfectionsOfEffectPreexistInCauseReading grades.InAct grades.CausesIn grades.esse ∧
    GoodnessIsActualityReading act grades.InAct ∧
    CauseOfBeingCausesEveryPerfection grades.InAct grades.CausesIn grades.esse ∧
    GodExists named ∧ GodIsOne named ∧ PerfectInFrame grades named ∧ act primary none ∧
    ActualEsseCause profile primary source ∧ ActualEsseCause profile source effect ∧
    act effect (some false) ∧ ¬ cause primary effect none ∧
    ¬ cause primary effect (some false) ∧
    ¬ GodIsSupremelyGood named grades.InAct act grades.CausesIn grades.esse
end Control

end TruthCore.Case.Catholicism.AncestralEsseAttributes
