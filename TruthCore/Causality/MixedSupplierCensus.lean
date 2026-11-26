module

public import TruthCore.Results.Causality.ConcreteRootAccess.Solution

/-!
# Mixed suppliers at one world

The roster has one to three actual candidates. Concreteness and directed
grounding are independent assignment tables and self-edges are permitted.
The grounding relation is the selected record relation.
-/

@[expose] public section

namespace TruthCore.Causality.MixedSupplierCensus

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.ClosedGroundingRoots
open TruthCore.Causality.ConcreteRootAccess

def fixture {B : Type} (concrete : B → Prop) (ground : B → B → Prop) : Profile Unit B where
  ontic := ⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩
  concrete := concrete
  grounds := fun _ => ground

def masks (n : Nat) : List (Nat × Nat) :=
  (List.range (2 ^ n)).flatMap fun c => (List.range (2 ^ (n * n))).map (c, ·)

def assigned (n : Nat) (bits : Nat × Nat) : Profile Unit (Fin n) :=
  fixture (fun x => bits.1.testBit x.val = true)
    (fun y x => bits.2.testBit (n * y.val + x.val) = true)

theorem censusSize :
    (masks 1).length + (masks 2).length + (masks 3).length = 4164 := by
  decide +kernel

/-- Both enumerated implications follow for each mask directly from the
existing general theorems. The local bridge uses the explicit logic input
of the second theorem. -/
theorem maskChecks (n : Nat) (bits : Nat × Nat) :
    let m := assigned n bits
    (ActualSuppliersOfConcretaConcrete m () → BlanketEquivalence m ()) ∧
    (NoWhollyBorrowedCollection m () → LocalizedBridge m () →
      ClosedGroundingCollectionsRooted m ()) := by
  exact ⟨TruthCore.Results.Causality.ConcreteRootAccess.blanketEquivalence _ _,
    fun hb hl => TruthCore.Results.Causality.ConcreteRootAccess.closedOfLocalized
      _ _ hb hl Classical.em⟩

abbrev Candidate := Fin 3

def roster (edges : List (Candidate × Candidate)) : Profile Unit Candidate :=
  fixture (fun x => x = 0 ∨ x = 1) (fun y x => (y, x) ∈ edges)

def mixedRoot := roster [(0, 1), (2, 1)]
def abstractRoot := roster [(0, 1), (2, 0), (2, 1)]
def abstractCycle := roster [(0, 1), (1, 0), (2, 0), (2, 1)]

def RootedRow (m : Profile Unit Candidate) : Prop :=
  ClosedGroundingCollectionsRooted m () ∧ NoWhollyBorrowedCollection m () ∧
    ¬ ActualSuppliersOfConcretaConcrete m () ∧ LocalizedBridge m ()

private theorem rowOfAccess (m : Profile Unit Candidate)
    (access : UniversalRootAccess m ()) (mixed : ¬ ActualSuppliersOfConcretaConcrete m ()) :
    RootedRow m := by
  have ccr := TruthCore.Results.Causality.ConcreteRootAccess.closedOfAccess m () access
  exact ⟨ccr, TruthCore.Results.Causality.ConcreteRootAccess.borrowedOfClosed m () ccr,
    mixed, fun x _ hx _ _ _ => access x hx⟩

theorem mixedRows : RootedRow mixedRoot ∧ RootedRow abstractRoot := by
  constructor
  all_goals
    apply rowOfAccess
    · intro x hx
      have hx' : x = 0 ∨ x = 1 := hx.1
      rcases hx' with rfl | rfl
      · apply RootAccess.root
        simp only [ActualRoot, ActualConcrete, ActualConcreteGround, mixedRoot, abstractRoot,
          roster, fixture] <;> decide +kernel
      · refine RootAccess.step (y := 0) (.root ?_) ?_ ?_
        all_goals
          simp only [ActualRoot, ActualConcrete, ActualConcreteGround, mixedRoot, abstractRoot,
            roster, fixture] <;> decide +kernel
    · intro hc
      have := hc 1 2 ⟨Or.inr rfl, trivial⟩ trivial (by
        simp only [mixedRoot, abstractRoot, roster, fixture] <;> decide)
      exact (by decide : ¬ ((2 : Candidate) = 0 ∨ (2 : Candidate) = 1)) this

theorem cycleRow :
    ¬ ClosedGroundingCollectionsRooted abstractCycle () ∧
    NoWhollyBorrowedCollection abstractCycle () ∧
    ¬ ActualSuppliersOfConcretaConcrete abstractCycle () ∧
    ¬ LocalizedBridge abstractCycle () := by
  have noRoot : ∀ x, ¬ ActualRoot abstractCycle () x := by
    unfold ActualRoot ActualConcrete ActualConcreteGround abstractCycle roster fixture
    decide +kernel
  have noAccess {x} (h : RootAccess abstractCycle () x) : False := by
    induction h with
    | root h => exact noRoot _ h
    | step _ _ _ ih => exact ih
  have concrete0 : ActualConcrete abstractCycle () 0 := ⟨Or.inl rfl, trivial⟩
  have notConcrete2 : ¬ abstractCycle.concrete 2 := by
    change ¬ ((2 : Candidate) = 0 ∨ (2 : Candidate) = 1)
    decide
  have supply0 : abstractCycle.grounds () 2 0 := by
    change ((2, 0) : Candidate × Candidate) ∈ [(0, 1), (1, 0), (2, 0), (2, 1)]
    decide
  refine ⟨fun ccr => noAccess
    (TruthCore.Results.Causality.ConcreteRootAccess.accessOfClosed
      abstractCycle () ccr Classical.em 0 concrete0), ?_,
    fun hc => notConcrete2 (hc 0 2 concrete0 trivial supply0),
    fun h => noAccess (h 0 2 concrete0 trivial notConcrete2 supply0)⟩
  intro S closed _ x hx
  have edge : abstractCycle.grounds () 2 x := by
    have hx' : x = 0 ∨ x = 1 := (closed.1 x hx).1
    rcases hx' with rfl | rfl
    · exact supply0
    · change ((2, 1) : Candidate × Candidate) ∈ [(0, 1), (1, 0), (2, 0), (2, 1)]
      decide
  exact notConcrete2 (closed.1 2 (closed.2 x 2 hx trivial edge)).1

end TruthCore.Causality.MixedSupplierCensus
