module

public import TruthCore.Causality.NecessaryConcreteRouteBridge
public import TruthCore.Causality.GradedSupportFoundation
public import TruthCore.Causality.Round2ExistenceAct
public import TruthCore.Causality.ExistenceActuality
public import TruthCore.Causality.Round5Worklist
public import TruthCore.Causality.Frame
public import TruthCore.Case.Catholicism.CauseOfBeingHasBeing
public import TruthCore.Latin.Aquinas.DeEnte.RootInterface
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia

/-!
# One dependence order: the stage-one well-foundedness premises through actual grounding (#1926)

Analyst formulations, attribution deferred. #1926 phase 3, bridge "one
dependence order". Several stage-one premises are separate well-foundedness
assumptions over different relations:

* `NoInfiniteActualEsseCauseRegress` (De ente, fd12ad3d; its per se sibling
  ea251340): no infinite chain of actual causes of being (`CausesIn … esse`,
  CAUSE_2);
* `SimplePriorityWellFounded` (prima via, d85de8e1): no infinite chain of
  simple priority (`PriorSimply`, PRIOR_1);
* `NoInfinitePerSeEfficientCauseSeriesReading` (secunda via, 97f5850f): no
  infinite per se ordered series of efficient causes (`CausesAsCaused`);
* `NoInfiniteAscentInBeing` (quarta via, 7dfa068a): no infinite ascent in the
  comparative `MoreIn esse`;
* `ActualGroundingWF` (82cfaf26): the profile's selected grounding relation is
  well-founded on actual concreta.

The question is whether one of them, over one relation, gives the others
through explicit inclusion bridges, without identifying cause, ground,
priority and comparison by definition (#1626, #1926 rigor contract 5). The
relations stay distinct parameters. Every passage between them is an existing
or new OPEN premise.

**The kernel.** `wellFounded_of_predecessorInclusion`: if `G` is well-founded
on the elements satisfying `S`, and every `R`-predecessor `c` of anything
satisfies `S` and is a `G`-predecessor of it, then `R` is well-founded on the
whole carrier. Only the predecessor needs to satisfy `S`. Core Lean only, no
axiom. It is the identity case of the general fact that well-foundedness pulls
back along any edge-preserving map (`Logic.Regress.Graph.Map.wellFounded`, a
Mathlib-importing module not used here).

**What the module adds.** Two OPEN premises:
`PerSeEfficientCausesArePerSeEsseCauses` (every per se ordered efficient-cause
link is a per se actual cause of being, PER_SE_5; it fails on the bound sense
CAUSES_AS_CAUSED_3, see its doc comment) and `ActualEsseCauseIsActualGround`
(the weak version of cb1cdea9); the law `actualEsseCause_iff_actualGround`;
and finite or `Nat` interpretations used by the controls of
`TruthCore.Results.Causality.OneDependenceOrder`. Everything else the results
use already exists:

* esse causing into grounding: the actuality calibrations
  `ActOfEsseSufficesForExistenceAt` (546975ef) and `EsseInReIsConcrete`
  (2d9807a5), with the new weak bridge, itself derived from
  `EsseCauseIsActualConcreteGround` (cb1cdea9);
* grounding into esse causing: `ActualGroundIsDistinctEsseCause` (98efaa9e)
  with `ExistingInActAt` (0436de86);
* simple priority into grounding: `SimplyPriorIsActualConcreteGround`
  (86efed1a) with `NothingPriorToItselfReading` (32d77f18);
* grounding into ascent: `ActualGroundIsMoreInEsse` (d96105fb), already used by
  `GradedSupportFoundation.actualGroundingWFOfAscent`.

**Why not the shared frame.** `Frame.CausalityFrame` has `PriorSimply`,
`CausesIn` and `esse` but no `InAct`, `MoreIn`, concreteness or grounding. The
priority result takes the frame's `F.PriorSimply`. The esse results are stated
over the q.3 a.4 `Profile`, because the target statements fd12ad3d and
ea251340 bind `p.InAct`, `p.CausesIn` and `p.esse` of that profile.
-/

@[expose] public section

namespace TruthCore.Causality.OneDependenceOrder

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualGroundingWF)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Latin.Aquinas.DeEnte
  (ActualEsseCause NoInfiniteActualEsseCauseRegress NoInfinitePerSeActualEsseCauseRegress)

/-! ## The kernel -/

/-- Well-foundedness transfers along a predecessor inclusion. If `G` is
well-founded on the subtype `{x // S x}`, and whenever `R c x` holds the
predecessor `c` satisfies `S` and `G c x` holds, then `R` is well-founded. The
successor `x` need not satisfy `S`. -/
theorem wellFounded_of_predecessorInclusion {B : Type} (S : B → Prop) (G R : B → B → Prop)
    (hWF : WellFounded fun a b : {x // S x} => G a.1 b.1)
    (hIncl : ∀ c x, R c x → S c ∧ G c x) : WellFounded R := by
  have key : ∀ a : {x // S x}, Acc R a.1 := by
    intro a
    induction a using hWF.induction with
    | _ a ih => exact ⟨_, fun c hc => ih ⟨c, (hIncl c a.1 hc).1⟩ (hIncl c a.1 hc).2⟩
  exact ⟨fun x => ⟨_, fun c hc => key ⟨c, (hIncl c x hc).1⟩⟩⟩

/-- A relation with a two-cycle is not well-founded. -/
theorem not_wellFounded_of_twoCycle {α : Type} {R : α → α → Prop} (a b : α)
    (hab : R a b) (hba : R b a) : ¬ WellFounded R := by
  intro hWF
  have key : ∀ x, Acc R x → ∀ y, R y x → R x y → False := by
    intro x hx
    induction hx with
    | intro x _ ih => exact fun y hyx hxy => ih y hyx x hxy hyx
  exact key a (hWF.apply a) b hba hab

/-- A relation with a reflexive point is not well-founded. -/
theorem not_wellFounded_of_loop {α : Type} {R : α → α → Prop} (a : α) (haa : R a a) :
    ¬ WellFounded R := by
  intro hWF
  have key : ∀ x, Acc R x → R x x → False := by
    intro x hx
    induction hx with
    | intro x _ ih => exact fun hxx => ih x hxx hxx
  exact key a (hWF.apply a) haa

/-- A relation contained in the single edge `a → b`, `a ≠ b`, is well-founded. -/
theorem wellFounded_of_singleEdge {α : Type} {R : α → α → Prop} (a b : α) (hne : a ≠ b)
    (h : ∀ y x, R y x → y = a ∧ x = b) : WellFounded R := by
  have ha : Acc R a := ⟨_, fun y hy => (hne ((h y a hy).2)).elim⟩
  exact ⟨fun x => ⟨_, fun y hy => (h y x hy).1 ▸ ha⟩⟩

/-- The successor relation on `Nat` read upward (`y = x + 1`) is not
well-founded: every number has a greater one. -/
theorem not_wellFounded_succ : ¬ WellFounded fun y x : Nat => y = x + 1 := by
  intro hWF
  have key : ∀ n, Acc (fun y x : Nat => y = x + 1) n → False := by
    intro n hn
    induction hn with
    | intro n _ ih => exact ih (n + 1) rfl
  exact key 0 (hWF.apply 0)

/-- Well-foundedness of the whole selected relation gives `ActualGroundingWF`. -/
theorem actualGroundingWF_of_wellFounded {W B : Type} (m : Profile W B) (w : W)
    (h : WellFounded (m.grounds w)) : ActualGroundingWF m w :=
  InvImage.wf (fun a : {x // ActualConcrete m w x} => a.1) h

/-! ## The new bridge -/

open TruthCore.Latin.Aquinas.DeEnte (PerSeActualEsseCause) in
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 in
/-- OPEN analyst framework premise, attribution deferred: every per se ordered
efficient-cause link (`CausesAsCaused c x`, the secunda via's "causes as a
caused cause", sense CAUSES_AS_CAUSED_3) is a per se actual cause of being
(`PerSeActualEsseCause p AsCaused c x`, PER_SE_5): `c` is other than `x`, both
are in act as to being, `c` causes the esse of `x` (`CausesIn c x esse`,
CAUSE_2), and it does so as caused (`AsCaused c x`).

It fails on the bound sense CAUSES_AS_CAUSED_3, which the proved statement
c2880fe0 (`PerSeMoverLinkIsPerSeCauseLinkReading`, sourced to ST I q.46 a.2
ad 7) extends to per se mover links: with c2880fe0 it makes every per se mover
a per se actual cause of the moved thing's esse. Ad 7 gives as per se series
the stone moved by the stick, moved by the hand, and the generation of this
man depending on this man, the elementary body and the sun (causes of motion
and of coming to be). That the stick continues to be when the hand lets go is
an analyst observation, not ad 7's. The premise is defensible only under a
not-yet-existing existential sense of `CausesAsCaused`; the sense split is the
next test. -/
def PerSeEfficientCausesArePerSeEsseCauses {B P R : Type} (p : Profile B P R)
    (AsCaused CausesAsCaused : B → B → Prop) : Prop :=
  ∀ c x, CausesAsCaused c x → PerSeActualEsseCause p AsCaused c x

/-- OPEN analyst bridge, attribution deferred, the weak version of
`EsseCauseIsActualConcreteGround` (cb1cdea9): a cause of the esse of an actual
concretum that is itself an actual concretum at `w` and other than it grounds
it at `w`. Unlike cb1cdea9 it does not conclude that the cause is concrete or
exists at `w`; it assumes both. So a cause of being absent from `w` (an
originating cause, a cause of coming to be) does not falsify it. -/
def ActualEsseCauseIsActualGround {W B R : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ c x, ActualConcrete m w c → ActualConcrete m w x → c ≠ x → CausesIn c x esse →
    m.grounds w c x

/-! ## Interpretations for the controls

Interpretations of the shared vocabulary only. They show which premises the
results need under the encoded predicates, not that any configuration is
possible or plausible. -/

namespace Control

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

/-- A q.3 a.4 profile on carrier `B`, with trivial principles: `InAct x esse`
is `act x`, `CausesIn c x esse` is `cause c x`. -/
def q3 {B : Type} (act : B → Prop) (cause : B → B → Prop) : Profile B Unit Unit where
  InAct := fun x _ => act x
  CausesIn := fun c x _ => cause c x
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- The two-cycle on `Bool`: each being stands to the other. -/
def cyc (a b : Bool) : Prop := a ≠ b

/-- The single edge `true → false`. -/
def edgeTF (a b : Bool) : Prop := a = true ∧ b = false

/-- Every link is per se (`AsCaused` everywhere true). -/
def allLinks (_ _ : Bool) : Prop := True

/-- No relation. -/
def noRel {B : Type} (_ _ : B) : Prop := False

/-- A one-world grounding profile (`DeEnte.oneWorld`). -/
abbrev world {B : Type} (concrete exist : B → Prop) (grounds : B → B → Prop) :
    TruthCore.Causality.BruteFoundationBoundary.Profile Unit B :=
  TruthCore.Latin.Aquinas.DeEnte.oneWorld concrete exist grounds

/-- The single edge `1 → 0` on `Nat`. -/
def edge10 (a b : Nat) : Prop := a = 1 ∧ b = 0

/-- Upward successor grade on `Nat`, at every respect: `y` is more than `x`
when `y = x + 1`. -/
def succGrade (_ : Unit) (y x : Nat) : Prop := y = x + 1

/-- Everything concrete and existing; grounding is the two-cycle. -/
abbrev mCyc : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool :=
  world (fun _ => True) (fun _ => True) cyc
/-- Everything concrete and existing; nothing grounds anything. -/
abbrev mNone : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool :=
  world (fun _ => True) (fun _ => True) noRel
/-- Everything concrete and existing; `true` grounds `false`. -/
abbrev mEdge : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool :=
  world (fun _ => True) (fun _ => True) edgeTF
/-- Everything concrete; nothing exists at the world; nothing grounds. -/
abbrev mAbsent : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool :=
  world (fun _ => True) (fun _ => False) noRel
/-- Everything exists; nothing is concrete; nothing grounds. -/
abbrev mAbstract : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool :=
  world (fun _ => False) (fun _ => True) noRel

/-- Everything in act; causes of being form the two-cycle. -/
abbrev pCyc : Profile Bool Unit Unit := q3 (fun _ => True) cyc
/-- Everything in act; `true` causes the esse of `false`. -/
abbrev pEdge : Profile Bool Unit Unit := q3 (fun _ => True) edgeTF
/-- Everything in act; no cause of being. -/
abbrev pNone : Profile Bool Unit Unit := q3 (fun _ => True) noRel
/-- Nothing in act; the cause relation at esse is the two-cycle. -/
abbrev pIdle : Profile Bool Unit Unit := q3 (fun _ => False) cyc

/-- The `Nat` grade model: one world, everything concrete, existing and in act;
`1` grounds `0`, causes its esse and is simply prior to it; `y` is more in
being than `x` when `y = x + 1`. -/
abbrev mNat : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Nat :=
  world (fun _ => True) (fun _ => True) edge10
/-- Its q.3 a.4 profile. -/
abbrev pNat : Profile Nat Unit Unit := q3 (fun _ => True) edge10

end Control

/-! ## Control statements -/

open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.GradedSupportFoundation
  (ActualGroundIsDistinctEsseCause NoInfiniteAscentAmongActualConcreta)
open TruthCore.Causality.Round2Grounding (ActualGroundIsMoreInEsse)
open TruthCore.Causality.Round3FourthWay (NoInfiniteAscentInBeing GradesFoundInBeing)
open TruthCore.Causality.Round5Worklist (SimplePriorityWellFounded)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (MaximumInGenusCausesAllInGenusReading NothingPriorToItselfReading
   NoInfinitePerSeEfficientCauseSeriesReading)
open Control

/-- Omissions and nonvacuity for the esse regress from actual grounding with
the weak bridge `ActualEsseCauseIsActualGround` in place of cb1cdea9. -/
def WeakEsseRegressControls : Prop :=
  (¬ ActualGroundingWF mCyc () ∧
    ActualEsseCauseIsActualGround mCyc () pCyc.CausesIn pCyc.esse ∧
    ActOfEsseSufficesForExistenceAt mCyc.ontic pCyc.InAct pCyc.esse () ∧
    EsseInReIsConcrete mCyc pCyc.InAct pCyc.esse ∧
    ¬ NoInfiniteActualEsseCauseRegress pCyc) ∧
  (ActualGroundingWF mNone () ∧
    ¬ ActualEsseCauseIsActualGround mNone () pCyc.CausesIn pCyc.esse ∧
    ActOfEsseSufficesForExistenceAt mNone.ontic pCyc.InAct pCyc.esse () ∧
    EsseInReIsConcrete mNone pCyc.InAct pCyc.esse ∧
    ¬ NoInfiniteActualEsseCauseRegress pCyc) ∧
  (ActualGroundingWF mAbsent () ∧
    ActualEsseCauseIsActualGround mAbsent () pCyc.CausesIn pCyc.esse ∧
    ¬ ActOfEsseSufficesForExistenceAt mAbsent.ontic pCyc.InAct pCyc.esse () ∧
    EsseInReIsConcrete mAbsent pCyc.InAct pCyc.esse ∧
    ¬ NoInfiniteActualEsseCauseRegress pCyc) ∧
  (ActualGroundingWF mAbstract () ∧
    ActualEsseCauseIsActualGround mAbstract () pCyc.CausesIn pCyc.esse ∧
    ActOfEsseSufficesForExistenceAt mAbstract.ontic pCyc.InAct pCyc.esse () ∧
    ¬ EsseInReIsConcrete mAbstract pCyc.InAct pCyc.esse ∧
    ¬ NoInfiniteActualEsseCauseRegress pCyc) ∧
  (ActualGroundingWF mEdge () ∧
    ActualEsseCauseIsActualGround mEdge () pEdge.CausesIn pEdge.esse ∧
    ActOfEsseSufficesForExistenceAt mEdge.ontic pEdge.InAct pEdge.esse () ∧
    EsseInReIsConcrete mEdge pEdge.InAct pEdge.esse ∧
    NoInfiniteActualEsseCauseRegress pEdge ∧ ActualEsseCause pEdge true false)

/-- Omissions and nonvacuity for actual grounding from the esse regress (the
converse inclusion), and strictness: with the forward bridges but without the
converse ground-to-cause bridge, the esse regress, well-founded simple priority
and their bridges hold while actual grounding is not well-founded. In the
strictness conjunct the causes of being and simple priority are the empty
relation, so the forward bridges, the regress, the priority bridge,
irreflexivity and well-founded priority hold vacuously. -/
def ConverseControls : Prop :=
  (¬ NoInfiniteActualEsseCauseRegress pCyc ∧
    ActualGroundIsDistinctEsseCause mCyc () pCyc.CausesIn pCyc.esse ∧
    ExistingInActAt mCyc.ontic pCyc.InAct pCyc.esse () ∧ ¬ ActualGroundingWF mCyc ()) ∧
  (NoInfiniteActualEsseCauseRegress pNone ∧
    ¬ ActualGroundIsDistinctEsseCause mCyc () pNone.CausesIn pNone.esse ∧
    ExistingInActAt mCyc.ontic pNone.InAct pNone.esse () ∧ ¬ ActualGroundingWF mCyc ()) ∧
  (NoInfiniteActualEsseCauseRegress pIdle ∧
    ActualGroundIsDistinctEsseCause mCyc () pIdle.CausesIn pIdle.esse ∧
    ¬ ExistingInActAt mCyc.ontic pIdle.InAct pIdle.esse () ∧ ¬ ActualGroundingWF mCyc ()) ∧
  (NoInfiniteActualEsseCauseRegress pEdge ∧
    ActualGroundIsDistinctEsseCause mEdge () pEdge.CausesIn pEdge.esse ∧
    ExistingInActAt mEdge.ontic pEdge.InAct pEdge.esse () ∧ ActualGroundingWF mEdge ()) ∧
  -- strictness: AGWF is not recovered from what it implies
  (EsseCauseIsActualConcreteGround mCyc () pNone.CausesIn pNone.esse ∧
    ActOfEsseSufficesForExistenceAt mCyc.ontic pNone.InAct pNone.esse () ∧
    EsseInReIsConcrete mCyc pNone.InAct pNone.esse ∧
    SimplyPriorIsActualConcreteGround mCyc () noRel ∧ NothingPriorToItselfReading (noRel : Bool → Bool → Prop) ∧
    NoInfiniteActualEsseCauseRegress pNone ∧ SimplePriorityWellFounded (noRel : Bool → Bool → Prop) ∧
    ¬ ActualGroundingWF mCyc ())

/-- Omissions and nonvacuity for well-founded simple priority from actual
grounding. -/
def PriorityControls : Prop :=
  (¬ ActualGroundingWF mCyc () ∧ SimplyPriorIsActualConcreteGround mCyc () cyc ∧
    NothingPriorToItselfReading cyc ∧ ¬ SimplePriorityWellFounded cyc) ∧
  (ActualGroundingWF mNone () ∧ ¬ SimplyPriorIsActualConcreteGround mNone () cyc ∧
    NothingPriorToItselfReading cyc ∧ ¬ SimplePriorityWellFounded cyc) ∧
  (ActualGroundingWF mNone () ∧
    SimplyPriorIsActualConcreteGround mNone () (fun a b : Bool => a = true ∧ b = true) ∧
    ¬ NothingPriorToItselfReading (fun a b : Bool => a = true ∧ b = true) ∧
    ¬ SimplePriorityWellFounded (fun a b : Bool => a = true ∧ b = true)) ∧
  (ActualGroundingWF mEdge () ∧ SimplyPriorIsActualConcreteGround mEdge () edgeTF ∧
    NothingPriorToItselfReading edgeTF ∧ SimplePriorityWellFounded edgeTF ∧ edgeTF true false)

/-- Omissions and nonvacuity for the per se efficient series from the esse
regress. -/
def SecundaControls : Prop :=
  (NoInfinitePerSeActualEsseCauseRegress pNone allLinks ∧
    ¬ PerSeEfficientCausesArePerSeEsseCauses pNone allLinks cyc ∧
    ¬ NoInfinitePerSeEfficientCauseSeriesReading cyc) ∧
  (¬ NoInfinitePerSeActualEsseCauseRegress pCyc allLinks ∧
    PerSeEfficientCausesArePerSeEsseCauses pCyc allLinks cyc ∧
    ¬ NoInfinitePerSeEfficientCauseSeriesReading cyc) ∧
  (NoInfinitePerSeActualEsseCauseRegress pEdge allLinks ∧
    PerSeEfficientCausesArePerSeEsseCauses pEdge allLinks edgeTF ∧
    NoInfinitePerSeEfficientCauseSeriesReading edgeTF ∧ edgeTF true false)

/-- The ascent limit, on the `Nat` grade model: actual grounding is
well-founded; the four inclusions esse cause into ground (cb1cdea9), ground
into esse cause (98efaa9e), priority into ground (86efed1a) and ground into
more in esse (d96105fb) hold, so do the genus principle (vacuously: the grade
has no maximum), the actuality calibrations, the esse regress and well-founded
priority, and some being is more a being than another; yet there is an
infinite ascent in being, even among actual concreta. Grounding, causing and
priority are the single edge `1 → 0`. -/
def AscentLimit : Prop :=
  ActualGroundingWF mNat () ∧
    EsseCauseIsActualConcreteGround mNat () pNat.CausesIn pNat.esse ∧
    ActualGroundIsDistinctEsseCause mNat () pNat.CausesIn pNat.esse ∧
    SimplyPriorIsActualConcreteGround mNat () edge10 ∧
    ActualGroundIsMoreInEsse mNat () succGrade pNat.esse ∧
    MaximumInGenusCausesAllInGenusReading pNat.InAct succGrade pNat.CausesIn ∧
    ActOfEsseSufficesForExistenceAt mNat.ontic pNat.InAct pNat.esse () ∧
    EsseInReIsConcrete mNat pNat.InAct pNat.esse ∧
    ExistingInActAt mNat.ontic pNat.InAct pNat.esse () ∧
    NoInfiniteActualEsseCauseRegress pNat ∧ SimplePriorityWellFounded edge10 ∧
    GradesFoundInBeing succGrade pNat.esse ∧
    ¬ NoInfiniteAscentAmongActualConcreta mNat () succGrade pNat.esse ∧
    ¬ NoInfiniteAscentInBeing succGrade pNat.esse

/-! ## Coextension under the two-way package -/

/-- Under the five bridges cb1cdea9, 546975ef, 2d9807a5 (forward) and
98efaa9e, 0436de86 (backward), an actual cause of being is exactly a grounding
step between actual concreta. The package therefore makes the two relations
extensionally the same through explicit open premises; warrant for the package
is warrant for that identification. Lake-checked law, not a registered result;
no axiom. -/
theorem actualEsseCause_iff_actualGround {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExists : ActOfEsseSufficesForExistenceAt m.ontic p.InAct p.esse w)
    (hConcrete : EsseInReIsConcrete m p.InAct p.esse)
    (hGround : ActualGroundIsDistinctEsseCause m w p.CausesIn p.esse)
    (hInAct : ExistingInActAt m.ontic p.InAct p.esse w) (c x : B) :
    ActualEsseCause p c x ↔
      (ActualConcrete m w c ∧ ActualConcrete m w x ∧ m.grounds w c x) := by
  constructor
  · rintro ⟨hne, hc, hx, hcause⟩
    have g := hEsse c x hne ⟨hConcrete x hx, hExists x hx⟩ hcause
    exact ⟨⟨hConcrete c hc, hExists c hc⟩, ⟨hConcrete x hx, hExists x hx⟩, g.2.2⟩
  · rintro ⟨hc, hx, hg⟩
    obtain ⟨hne, hcause⟩ := hGround c x hc hx hg
    exact ⟨hne, hInAct c hc.2, hInAct x hx.2, hcause⟩

end TruthCore.Causality.OneDependenceOrder
