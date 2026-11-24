import TruthCore.Causality.WorldwiseCompositeGround
import TruthCore.Results.Science.InductionSelection.Solution
import TruthCore.Results.Logic.ForeknowledgeDiscrimination.Solution
import TruthCore.Results.Causality.Q44SourceSupply.Solution
import TruthCore.Latin.Aquinas.DeEnte.ExtrinsicSource

/-! Local diagnostics for #1811. The slot test uses the existing #1097 whole.
The reception test takes an independently missing perfection at the whole. -/
namespace NecessaryWhole
open TruthCore.Causality.WorldwiseCompositeGround

def exchange : Body → Body
  | .whole => .whole
  | .atom cohort slot => .atom cohort (!slot)

theorem exchangeTwice (x : Body) : exchange (exchange x) = x := by
  cases x <;> simp [exchange]

theorem sameExistence (w : Bool) (x : Body) : existsAt w (exchange x) ↔ existsAt w x := by
  cases x <;> rfl

theorem sameSupport (w : Bool) (c x : Body) :
    support w (exchange c) (exchange x) ↔ support w c x := by
  cases c <;> cases x <;> simp [support, exchange]

private theorem membership (x : Body) (b : Bool) :
    b ∈ (content (exchange x)).val ↔ (!b) ∈ (content x).val := by
  cases x with
  | whole => rfl
  | atom c k =>
    change b = !k ↔ (!b) = k
    cases b <;> cases k <;> decide

theorem sameParthood (w : Bool) (x y : Body) :
    actualPart w (exchange x) (exchange y) ↔ actualPart w x y := by
  simp only [actualPart, sameExistence, and_congr_right_iff]
  intro _ _
  change ((content (exchange x)).val ⊆ (content (exchange y)).val) ↔
    (content x).val ⊆ (content y).val
  constructor
  · intro h b hb
    have hx := (membership x (!b)).mpr (by simpa using hb)
    simpa using (membership y (!b)).mp (h hx)
  · intro h b hb
    exact (membership y b).mpr (h ((membership x b).mp hb))

/-- Any proposed *qualitative* role using only exchange-invariant data must
treat these two actual slots alike. Names which distinguish slots are available
in Lean; invariance is the test on the proposed explanation. -/
theorem noUniqueSlot (w : Bool) (role : Body → Prop)
    (hinv : ∀ x, role (exchange x) ↔ role x) (slot : Bool) :
    ¬ (∀ k, role (.atom w k) ↔ k = slot) := by
  intro unique
  open TruthCore.Science.InductionSelection in
    have fixed := (TruthCore.Results.Science.InductionSelection.symmetry Unit Bool symmetric
      (fun _ k => role (.atom w k)) () (fun _ k => hinv (.atom w k)) rfl).2 slot unique
  cases slot <;> contradiction

/-- In a separate mechanical illustration the normalized restoring force is
the negative of this stiffness response. Exchange fixes both response spaces
setwise, although it need not fix the individual displacements. -/
private def stiffness (a b : Int) : Int × Int := (2*a - b, 2*b - a)

theorem commonAndOpposed (a b : Int) :
    (stiffness a b = (a, b) ↔ a = b) ∧
    (stiffness a b = (3*a, 3*b) ↔ a = -b) := by
  simp only [stiffness, Prod.mk.injEq]
  constructor <;> constructor <;> omega

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile DistinctEsseAt)
open TruthCore.Causality.WholePowerPerfection
open TruthCore.Causality.ReceptionLimitation
open TruthCore.Causality.EsseReception
open TruthCore.Latin.Aquinas.DeEnte

variable {B P R D : Type} (f : Profile B P R) (Received : B → P → Prop)
    (Potency : P → P → Prop) (OwnBeing : B → Prop)
    (Has : B → D → Prop) (OfBeing : D → Prop)

/-- The single missing determination must belong to being under the very
possession relation used by the fullness premise. Both conclusions concern W.
The second records the constructive boundary for an actual reception witness. -/
theorem restrictionAtWhole
    (hOwn : EsseReceivedOnlyInOwnEssence f.essenceOf Received)
    (hPot : ReceiverInPotencyToReceivedEsseReading f.esseOf Received Potency)
    (hIrrefl : NothingInReceptivePotencyToItself Potency)
    (hUnreceived : UnreceivedEsseIsOwnBeing Received OwnBeing)
    (hFull : OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing)
    (W : B) (d : D) (actual : f.InAct W f.esse) (hd : OfBeing d) (missing : ¬ Has W d) :
    DistinctEsseAt f W ∧ ¬¬ Received W (f.essenceOf W) := by
  have notOwn : ¬ OwnBeing W := fun h => missing (hFull W h d hd)
  constructor
  · exact ⟨actual, fun eq => notOwn (TruthCore.Results.Causality.Q44SourceSupply.ownBeingOfIdentity
      f Received Potency OwnBeing hOwn hPot hIrrefl hUnreceived eq)⟩
  · intro noReception
    apply notOwn (hUnreceived W ?_)
    intro r hr
    exact noReception (hOwn W r hr ▸ hr)

/-- Test a particular proposed restriction independently of the reception
premises. W has the same complete cognitive basis at u and v on this account.
One settled content differs. Factivity at the comparison world is sufficient. -/
theorem missingDiscernmentAt {B D World State : Type} (W : B) (d : D)
    (Has : B → D → Prop) (E : B → TruthCore.Modal.Frame World)
    (basis : World → State) (C : (World → Bool) → Prop) (u v : World)
    (possession : Has W d → TruthCore.Logic.ForeknowledgeDiscrimination.Complete (E W) C u)
    (exhaustive : TruthCore.Logic.ForeknowledgeDiscrimination.Supervenes (E W) basis)
    (sameBasis : basis u = basis v) (factiveAtV : (E W).access v v)
    (p : World → Bool) (selected : C p) (differs : p u ≠ p v) : ¬ Has W d := by
  intro has
  have reachable := (exhaustive u v sameBasis v).mpr factiveAtV
  have agrees := (TruthCore.Results.Logic.ForeknowledgeDiscrimination.core.1 World
    (E W) C u).mp (possession has) v reachable
  exact differs (agrees p selected).symm

theorem causeAtWhole (W : B) (distinct : DistinctEsseAt f W)
    (coverage : DistinctEsseHasSomeCause f)
    (noSelf : TruthCore.Causality.TermSenseForks.NothingCausesItsOwnBeing f.CausesIn f.esse) :
    ∃ c, c ≠ W ∧ f.CausesIn c W f.esse := by
  obtain ⟨c, causes⟩ := coverage W distinct
  exact ⟨c, fun eq => noSelf W (eq ▸ causes), causes⟩

#print axioms commonAndOpposed
#print axioms missingDiscernmentAt
#print axioms causeAtWhole
#print axioms sameParthood
#print axioms sameSupport
#print axioms noUniqueSlot
#print axioms restrictionAtWhole
end NecessaryWhole
