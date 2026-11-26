module

public import TruthCore.Case.Catholicism.AncestralEsseAttributes

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.AncestralEsseAttributes

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.AncestralEsseAttributes
open TruthCore.Case.Catholicism.AttributesFromEsse (PerfectInFrame)
open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause CommonEsseIsEssenceSource)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Logic (ExcludedMiddle)

private theorem noPathIntoMaximum {B P R : Type} (p : Profile B P R)
    (MoreIn : R → B → B → Prop)
    (exclude : MaximumHasNoDistinctEsseCause p.InAct MoreIn p.CausesIn p.esse)
    {n g : B} (maximum : IsMaximumIn p.InAct MoreIn p.esse g)
    (path : Relation.TransGen (ActualEsseCause p) n g) : False := by
  cases path with
  | single last => exact exclude g maximum _ last.1 last.2.2.2
  | tail _ last => exact exclude g maximum _ last.1 last.2.2.2

private theorem maximumIsAncestor {B P R : Type} (p : Profile B P R)
    (MoreIn : R → B → B → Prop)
    (exclude : MaximumHasNoDistinctEsseCause p.InAct MoreIn p.CausesIn p.esse)
    (em : ExcludedMiddle) {n g : B}
    (paths : ∀ x, p.InAct x p.esse → x ≠ n → Relation.TransGen (ActualEsseCause p) n x)
    (maximum : IsMaximumIn p.InAct MoreIn p.esse g) : g = n := by
  rcases em (g = n) with same | distinct
  · exact same
  · exact (noPathIntoMaximum p MoreIn exclude maximum (paths g maximum.1 distinct)).elim

private theorem preexistenceAlongPath {B P R : Type} (p : Profile B P R)
    (preexist : PerfectionsOfEffectPreexistInCauseReading p.InAct p.CausesIn p.esse)
    {n x : B} {r : R} (path : Relation.TransGen (ActualEsseCause p) n x)
    (actual : p.InAct x r) : p.InAct n r := by
  induction path with
  | single edge => exact preexist _ _ r edge.2.2.2 actual
  | tail _ edge prior => exact prior (preexist _ _ r edge.2.2.2 actual)

/-- Each named maximum is the common source, by exclusion at the last edge. -/
theorem oneFromAncestry {B P R : Type} (p : Profile B P R)
    (IsGod : B → Prop) (MoreIn : R → B → B → Prop)
    (source : CommonEsseIsEssenceSource p)
    (maximal : GodIsMaximalInBeing IsGod p.InAct MoreIn p.esse)
    (exclude : MaximumHasNoDistinctEsseCause p.InAct MoreIn p.CausesIn p.esse)
    (em : ExcludedMiddle) : GodIsOne IsGod := by
  obtain ⟨n, _, _, _, paths⟩ := source
  intro g hg k hk
  exact (maximumIsAncestor p MoreIn exclude em paths (maximal k hk)).trans
    (maximumIsAncestor p MoreIn exclude em paths (maximal g hg)).symm

/-- From any actual respect at a recipient, repeat the preexistence law along
its esse-cause path to the same named maximum. -/
theorem perfectFromAncestry {W B T R P : Type} (F : GradesFrame W B T R)
    (IsGod : B → Prop) (essenceOf esseOf : B → P) (sufficient : B → Prop)
    (source : CommonEsseIsEssenceSource (profileOf F essenceOf esseOf sufficient))
    (maximal : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (exclude : MaximumHasNoDistinctEsseCause F.InAct F.MoreIn F.CausesIn F.esse)
    (em : ExcludedMiddle)
    (being : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (preexist : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse) :
    PerfectInFrame F IsGod := by
  let p := profileOf F essenceOf esseOf sufficient
  obtain ⟨n, _, _, _, paths⟩ := source
  intro g hg x r actual
  have same := maximumIsAncestor p F.MoreIn exclude em paths (maximal g hg)
  rw [same]
  rcases em (x = n) with sameBearer | distinct
  · exact sameBearer ▸ actual
  · exact preexistenceAlongPath p preexist (paths x (being x r actual) distinct) actual

open TruthCore.Case.Catholicism.AncestralEsseAttributes.Control
open TruthCore.Causality.Q44SourceSupply.Control (Being chainCause)
open TruthCore.Causality.Q44EssentialSource.Control.Three

private theorem allAtEsse (x : Being) :
    grades.InAct x grades.esse :=
  Or.inl (by decide)

private theorem sourceEdge : ActualEsseCause profile primary source :=
  ⟨by decide, allAtEsse _, allAtEsse _, Or.inl ⟨rfl, rfl⟩, allAtEsse _⟩

private theorem recipientEdge : ActualEsseCause profile source effect :=
  ⟨by decide, allAtEsse _, allAtEsse _, Or.inr ⟨rfl, rfl⟩, allAtEsse _⟩

private theorem noIntoPrimary (c : Being) :
    ¬ chainCause c primary := by
  intro edge
  rcases edge with ⟨_, wrong⟩ | ⟨_, wrong⟩ <;> cases wrong

private theorem chainSource : CommonEsseIsEssenceSource profile := by
  refine ⟨primary, allAtEsse _, rfl, ?_, ?_⟩
  · exact fun c edge => noIntoPrimary c edge.2.2.2.1
  · intro x _ distinct
    cases x with
    | primary => exact (distinct rfl).elim
    | source => exact Relation.TransGen.single sourceEdge
    | effect => exact (Relation.TransGen.single sourceEdge).tail recipientEdge

private theorem chainMaximal : GodIsMaximalInBeing named grades.InAct grades.MoreIn grades.esse := by
  intro x namedX
  change x = primary at namedX
  subst x
  exact ⟨allAtEsse _, fun c greater => noIntoPrimary c greater.2⟩

private theorem chainExclusion :
    MaximumHasNoDistinctEsseCause grades.InAct grades.MoreIn grades.CausesIn grades.esse :=
  fun _ maximum c _ edge => maximum.2 c ⟨rfl, edge.1⟩

private theorem chainPreexistence :
    PerfectionsOfEffectPreexistInCauseReading grades.InAct grades.CausesIn grades.esse := by
  intro c x r edge actual
  change act x r at actual
  change act c r
  rcases actual with ordinary | sourceOnly
  · exact Or.inl ordinary
  · subst x
    exact (noIntoPrimary c edge.1).elim

private theorem chainPerfection : PerfectInFrame grades named := by
  intro g namedG _ _ _
  exact Or.inr namedG

/-- The populated finite chain satisfies the premises and conclusions of the two attribute conditionals and shows
that the same nonlogical inputs can hold with direct supreme goodness false. -/
theorem chainControl : ChainControl := by
  have noEndpoint : ¬ chainCause primary effect := by
    intro edge
    rcases edge with ⟨_, wrong⟩ | ⟨wrong, _⟩ <;> cases wrong
  refine ⟨chainSource, chainMaximal, chainExclusion, fun x _ _ => allAtEsse x,
    chainPreexistence, fun _ _ => Iff.rfl, fun _ _ _ edge actual => ⟨edge.1, actual⟩,
    ⟨primary, rfl⟩, fun _ hG _ hK => hK.trans hG.symm, chainPerfection, allAtEsse _,
    sourceEdge, recipientEdge, Or.inl (by decide), fun h => noEndpoint h.1,
    fun h => noEndpoint h.1, ?_⟩
  intro good
  exact noEndpoint ((good primary rfl).2 effect (some false) (by decide)
    (Or.inl (by decide))).1

end TruthCore.Results.Case.Catholicism.AncestralEsseAttributes
