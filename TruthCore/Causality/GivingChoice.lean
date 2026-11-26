module

public import TruthCore.Modal.STIT
public import TruthCore.Causality.ThroughWill
public import TruthCore.Modal.WillChoiceCensus

/-! Analyst interpretation for #2059. Histories of a STIT decision are
represented by worlds of the shared causality frame. The decision moment
indexes a whole-output comparison. It need not be a time at which a
tenseless universal cause deliberates. No actual decision partition, temporal
transition in that cause, or exhaustiveness of the represented worlds follows. -/

@[expose] public section

namespace TruthCore.Causality.GivingChoice

open TruthCore.Modal.STIT
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.ThroughWill (RationallyGivesAt)
open TruthCore.Causality.WillVersusChance (AgencyFrame SetupSameIn WilledTwoWayAt)
open TruthCore.Causality.NarDerivation (FixedTowardAt)
open TruthCore.Modal.PrussPowerPremises (GivesTo)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)

variable {W B T R S P M H : Type}
variable {C : BranchingFrame M H B} {m : M}

/-- OPEN interpretation of the represented continuations. Each mapped world
is accessible from the selected world and retains this same giver. This
one-way inclusion suffices to test fixity; it does not identify the
historical and metaphysical modalities. -/
def Admissible (F : CausalityFrame W B T R) (world : C.Through m → W) (w : W) (g : B) : Prop :=
  ∀ k, F.history.ontic.frame.access w (world k) ∧ F.history.ontic.ExistsAt (world k) g

/-- OPEN. The existing two-way giving sense specifically keeps the giver's
intrinsic states and external conditions fixed; accessibility alone does not. -/
def SameSetup (A : AgencyFrame W B S P) (world : C.Through m → W) (w : W) (g : B) : Prop :=
  ∀ k, SetupSameIn A g w (world k)

/-- The production proposition evaluated across histories in a choice cell. -/
def Produces (F : CausalityFrame W B T R) (world : C.Through m → W) (g x : B) :
    C.Through m → Prop :=
  fun k => GivesTo F (world k) g x

/-- OPEN identification of this recipient's existence with its production
by this giver, in just the represented worlds. Factivity and exclusive
dependence are both needed for the biconditional. -/
def TracksExistence (F : CausalityFrame W B T R) (world : C.Through m → W) (g x : B) : Prop :=
  ∀ k, Produces F world g x k ↔ F.history.ontic.ExistsAt (world k) x

theorem gives_and_can_refrain_of_existence
    {F : CausalityFrame W B T R} {world : C.Through m → W} {g x : B}
    {h : C.Through m} {available : TruthCore.Modal.Frame (C.Through m)}
    (track : TracksExistence F world g x)
    (actual : Cstit g h (fun k => F.history.ontic.ExistsAt (world k) x))
    (alternative : CanEnsure available g h (fun k => ¬ F.history.ontic.ExistsAt (world k) x)) :
    Dstit g h (Produces F world g x) ∧ CanEnsure available g h (fun k => ¬ Produces F world g x k) := by
  have positive : Cstit g h (Produces F world g x) := fun k hk => (track k).2 (actual k hk)
  obtain ⟨k, accessible, cell⟩ := alternative
  have negative : CanEnsure available g h (fun k => ¬ Produces F world g x k) :=
    ⟨k, accessible, fun j hj giving => cell j hj ((track j).1 giving)⟩
  exact ⟨dstit_of_canEnsure_not positive negative, negative⟩

/-- Dstit about this giver's production conflicts with NECESSITATE_5 once
every history in the comparison maps to an accessible world retaining g. -/
theorem dstit_excludes_fixed
    {F : CausalityFrame W B T R} {world : C.Through m → W} {w : W} {g x : B}
    {h : C.Through m} (admit : Admissible F world w g)
    (does : Dstit g h (Produces F world g x)) : ¬ FixedTowardAt F w g x := by
  intro fixed
  exact does.2 (fun k => fixed.2 (world k) (admit k).1 (admit k).2)

/-- The same actual rational exercise and an available withholding cell
suffice for the existing existential same-setup giving sense. This is a
one-way consequence: mere withholding at a world need not be an action. -/
theorem willed_two_way_of_cell
    {F : CausalityFrame W B T R} {A : AgencyFrame W B S P} {world : C.Through m → W}
    {h : C.Through m} {w : W} {g x : B} {available : TruthCore.Modal.Frame (C.Through m)}
    (existsHere : F.history.ontic.ExistsAt w g) (admit : Admissible F world w g)
    (same : SameSetup A world w g) (rational : RationallyGivesAt F A w g x)
    (cell : CanEnsure available g h (fun k => ¬ Produces F world g x k)) :
    WilledTwoWayAt F A w g := by
  obtain ⟨p, owned, rationalPower, givesBy⟩ := rational
  obtain ⟨k, _, withheld⟩ := canEnsure_can cell
  exact ⟨existsHere, p, x, world k, owned, rationalPower, (admit k).1, (admit k).2,
    same k, givesBy, withheld⟩

/-- OPEN, for the selected grounding profile. Each actual root's grounded
actual concretum admits an entire withholding cell. The cell may vary with
the recipient; this is weaker than a cell that withholds all creation.
No conclusion about alternative-world accessibility is built into this premise. -/
def RootsHaveWithholdingCells (F : CausalityFrame W B T R) (world : C.Through m → W)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ g x, ActualRoot (groundProfile F concrete G) w g →
    ActualConcrete (groundProfile F concrete G) w x →
    ActualConcreteGround (groundProfile F concrete G) w g x →
    ∃ k, Cstit g k (fun j => ¬ Produces F world g x j)

/-- OPEN scope for the represented continuations of the roots. -/
def RootHistoriesAdmissible (F : CausalityFrame W B T R) (world : C.Through m → W)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ g, ActualRoot (groundProfile F concrete G) w g → Admissible F world w g

end TruthCore.Causality.GivingChoice
