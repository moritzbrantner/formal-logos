module

public import TruthCore.Causality.NecessaryRootUniqueness
public import TruthCore.Results.Causality.WholeRosterFoundation.Solution

@[expose] public section

namespace TruthCore.Results.Causality.NecessaryRootUniqueness
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (NecessaryBeingHasBeing CauseOfNecessaryBeingCausesItsNecessity)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

theorem uniqueRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn) :
    UniqueNecessaryActualRootAt m w := by
  obtain ⟨n, hRoot, hNecessary⟩ :=
    WholeRosterFoundation.necessaryActualRoot m w hPop hWhole hDep hEM
  obtain ⟨maximum, hMaximum⟩ :=
    maximumExistsOfNecessaryAt m w InAct MoreIn esse n hNecessary hHasBeing hApproach hEM
  have hIdentity := (necessaryRootIsMaximumOfRoot m w CausesNecessityOf
    InAct MoreIn CausesIn esse n hRoot hNecessary hEM hBridge hGenus hHasBeing hCause).2
  refine ⟨n, hRoot, hNecessary, ?_⟩
  intro x hXRoot
  have hXNecessary : TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic w x := by
    rcases hEM (TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic w x)
      with h | h
    · exact h
    · exact ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
        (contingentRootOfNonnecessary m w hEM ⟨x, hXRoot, h⟩)).elim
  have hXIdentity := (necessaryRootIsMaximumOfRoot m w CausesNecessityOf
    InAct MoreIn CausesIn esse x hXRoot hXNecessary hEM hBridge hGenus hHasBeing hCause).2
  exact (hXIdentity maximum hMaximum).symm.trans (hIdentity maximum hMaximum)

/-- A supplied maximum reaches each distinct necessary target. The same causal
edge transfers first to a cause of necessity and then to a selected ground. -/
theorem maximumReachesNecessaryAt {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf)
    (c x : B) (hc : IsMaximumIn InAct MoreIn esse c)
    (hx : NecessaryAt m.ontic w x) (hne : x ≠ c) :
    CausesIn c x esse ∧ CausesNecessityOf c x ∧ ActualConcreteGround m w c x := by
  have hNecessary := isNecessaryOfNecessaryAt m w x hx
  have hEsse := hGenus esse c hc x hne (hHasBeing x hNecessary)
  have hNecessity := hCause c x hNecessary hEsse
  exact ⟨hEsse, hNecessity, hBridge c x (Ne.symm hne) hNecessity⟩

namespace ContingentScope

/-! In both profiles, 0 is the maximum and selected root, 1 is necessary
and grounded by 0, and 2 exists only at the actual world. The selected
edges at that world are 0 → 1 and 1 → 2 in both profiles. Vary admission
of 2 to the esse domain, with the corresponding grade and causal edge. -/

def existsAt (w : Bool) (x : Fin 3) : Prop := w = false ∨ x ≠ 2

def profile : Profile Bool (Fin 3) where
  ontic := ⟨⟨fun _ _ => True⟩, existsAt, fun _ _ _ => False⟩
  concrete := fun _ => True
  grounds := fun w c x => w = false ∧ ((c = 0 ∧ x = 1) ∨ (c = 1 ∧ x = 2))

def inAct (admit : Bool) (x : Fin 3) (_ : Unit) : Prop := x ≠ 2 ∨ admit = true

def moreIn (admit : Bool) (r : Unit) (c x : Fin 3) : Prop :=
  c = 0 ∧ x ≠ 0 ∧ inAct admit x r

def causesIn (admit : Bool) (c x : Fin 3) (r : Unit) : Prop := moreIn admit r c x

def causesNecessityOf (c x : Fin 3) : Prop := c = 0 ∧ x = 1

private theorem root : ActualRoot profile false 0 := by
  unfold ActualRoot ActualConcrete ActualConcreteGround profile existsAt
  decide +kernel

private theorem population : InhabitedConcreteAt profile.ontic profile.concrete false :=
  ⟨0, trivial, Or.inl rfl⟩

private theorem nontrapping : WholeRosterNotTrapped profile false := by
  intro _ hTrap
  exact hTrap.1 ⟨0, root.1⟩ trivial
    (fun ⟨c, hEdge⟩ => root.2 c.val ⟨c.property.1, c.property.2, hEdge⟩)

private theorem contingentGrounded : EveryContingentGroundedAt profile false := by
  unfold EveryContingentGroundedAt
    ContingentAt profile existsAt
  decide +kernel

private theorem necessityGround : NecessityCausesAreActualConcreteGrounds
    profile false causesNecessityOf := by
  unfold NecessityCausesAreActualConcreteGrounds ActualConcreteGround
    profile existsAt causesNecessityOf
  decide +kernel

private theorem necessaryHasBeing (admit : Bool) :
    NecessaryBeingHasBeing (modalPossible profile false) (modalIsAt profile) (inAct admit) () := by
  cases admit <;>
    unfold NecessaryBeingHasBeing IsNecessary PossibleNotToBe modalPossible modalIsAt
      profile existsAt inAct <;> decide +kernel

private theorem causeTransfers (admit : Bool) :
    CauseOfNecessaryBeingCausesItsNecessity (modalPossible profile false) (modalIsAt profile)
      (causesIn admit) () causesNecessityOf := by
  cases admit <;>
    unfold CauseOfNecessaryBeingCausesItsNecessity IsNecessary PossibleNotToBe modalPossible
      modalIsAt profile existsAt causesIn causesNecessityOf moreIn inAct <;> decide +kernel

private theorem maximum (admit : Bool) : IsMaximumIn (inAct admit) (moreIn admit) () 0 := by
  cases admit <;> unfold IsMaximumIn moreIn inAct <;> decide +kernel

private theorem genus (admit : Bool) :
    MaximumInGenusCausesAllInGenusReading (inAct admit) (moreIn admit) (causesIn admit) := by
  intro r
  cases r
  cases admit <;>
    unfold IsMaximumIn CausesAllInGenus causesIn moreIn inAct <;> decide +kernel

private theorem grades (admit : Bool) :
    GradesByApproachToAMaximumReading (inAct admit) (moreIn admit) := by
  intro r _
  cases r
  exact ⟨0, maximum admit⟩

/-- Apply the original uniqueness theorem in both interpretations. All eight
nonlogical inputs are witnessed above; EM is the original explicit input. -/
theorem uniqueInBoth (admit : Bool) (hEM : ExcludedMiddle) :
    UniqueNecessaryActualRootAt profile false :=
  uniqueRoot profile false causesNecessityOf (inAct admit) (moreIn admit) (causesIn admit) ()
    population nontrapping contingentGrounded hEM necessityGround (genus admit)
    (necessaryHasBeing admit) (causeTransfers admit) (grades admit)

/-- The unique selected-root conclusion permits a distinct actual necessary
being, namely 1, which has an incoming actual concrete ground from 0. -/
theorem necessaryNonroot :
    ActualRoot profile false 0 ∧ NecessaryAt profile.ontic false 0 ∧
    ActualConcrete profile false 1 ∧ NecessaryAt profile.ontic false 1 ∧
    (0 : Fin 3) ≠ 1 ∧ ActualConcreteGround profile false 0 1 := by
  refine ⟨root, ?_⟩
  unfold NecessaryAt ActualConcrete ActualConcreteGround profile existsAt
  decide +kernel

/-- At the same maximum and contingent target, actuality can fail to yield
esse actuality. After admitting that target to esse, the causal edge exists
but the cause-of-necessity and direct selected-ground edges are still absent.
The target retains an actual concrete ground from 1 in both interpretations. -/
theorem contingentTarget :
    ActualRoot profile false 0 ∧
    (∀ admit, IsMaximumIn (inAct admit) (moreIn admit) () 0) ∧
    ActualConcrete profile false 2 ∧
    ContingentAt profile.ontic false 2 ∧
    ActualConcreteGround profile false 1 2 ∧
    ¬ inAct false 2 () ∧ ¬ causesIn false 0 2 () ∧
    inAct true 2 () ∧ causesIn true 0 2 () ∧
    ¬ causesNecessityOf 0 2 ∧ ¬ ActualConcreteGround profile false 0 2 := by
  refine ⟨root, maximum, ?_⟩
  unfold ActualConcrete ContingentAt
    ActualConcreteGround profile existsAt causesIn causesNecessityOf moreIn inAct
  decide +kernel

end ContingentScope

end TruthCore.Results.Causality.NecessaryRootUniqueness
