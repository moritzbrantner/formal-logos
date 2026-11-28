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
by this giver, in just the represented worlds. Giving entails presence of x,
and presence of x entails giving by g. Exclusive dependence on g is one
possible rationale for the converse. A represented world where x exists
and g does not give x being falsifies that converse. -/
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
suffice for the existing existential same-setup giving sense. The all-history
premises supply the giver’s presence at the selected history and accessibility,
presence and setup agreement at the withholding witness. -/
theorem willed_two_way_of_cell
    {F : CausalityFrame W B T R} {A : AgencyFrame W B S P} {world : C.Through m → W}
    {h : C.Through m} {g x : B} {available : TruthCore.Modal.Frame (C.Through m)}
    (admit : Admissible F world (world h) g)
    (same : SameSetup A world (world h) g) (rational : RationallyGivesAt F A (world h) g x)
    (cell : CanEnsure available g h (fun k => ¬ Produces F world g x k)) :
    WilledTwoWayAt F A (world h) g := by
  obtain ⟨p, owned, rationalPower, givesBy⟩ := rational
  obtain ⟨k, _, withheld⟩ := canEnsure_can cell
  exact ⟨(admit h).2, p, x, world k, owned, rationalPower, (admit k).1, (admit k).2,
    same k, givesBy, withheld⟩

/-- WITHHOLD_1 (choice-cell withholding): every history in `g`'s choice cell
represented by `k` maps to a world where `g` does not give `x` being. This is
agentive STIT control over the cell (definition c54f0922), not one history of
nonproduction, and it says nothing about accessibility or about `g`'s presence. -/
def WithholdsByCell (F : CausalityFrame W B T R) (world : C.Through m → W) (g x : B)
    (k : C.Through m) : Prop :=
  Cstit g k (fun j => ¬ Produces F world g x j)

/-- WITHHOLD_2 (accessible per-effect non-giving): some world accessible from
`w` has `g` existing and not giving `x` being. No choice, control or agency is
part of this sense; it is the matrix of `NarDerivation.ActualRootsWithholdEachGrounded`. -/
def WithholdsAtAccessible (F : CausalityFrame W B T R) (w : W) (g x : B) : Prop :=
  ∃ v, F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v g ∧ ¬ GivesTo F v g x

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

/-- OPEN sufficient interpretation for the represented continuations of the
roots. The root withholding result applies it only at each chosen representative. -/
def RootHistoriesAdmissible (F : CausalityFrame W B T R) (world : C.Through m → W)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ g, ActualRoot (groundProfile F concrete G) w g → Admissible F world w g

/-- The cell premise is WITHHOLD_1 for each actual root and grounded actual
concretum. -/
theorem rootsHaveWithholdingCells_iff (F : CausalityFrame W B T R) (world : C.Through m → W)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W) :
    RootsHaveWithholdingCells F world concrete G w ↔
      ∀ g x, ActualRoot (groundProfile F concrete G) w g →
        ActualConcrete (groundProfile F concrete G) w x →
        ActualConcreteGround (groundProfile F concrete G) w g x →
        ∃ k, WithholdsByCell F world g x k :=
  Iff.rfl

/-- Premise (a) of the NAR route is WITHHOLD_2 for each actual root and
grounded actual concretum. -/
theorem actualRootsWithholdEachGrounded_iff (F : CausalityFrame W B T R)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W) :
    TruthCore.Causality.NarDerivation.ActualRootsWithholdEachGrounded F concrete G w ↔
      ∀ g x, ActualRoot (groundProfile F concrete G) w g →
        ActualConcrete (groundProfile F concrete G) w x →
        ActualConcreteGround (groundProfile F concrete G) w g x →
        WithholdsAtAccessible F w g x :=
  Iff.rfl

end TruthCore.Causality.GivingChoice
