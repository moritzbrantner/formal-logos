module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import TruthCore.Explanation.NoFoundationLawChaos
public import TruthCore.Science.AdaptiveHistoryAccess
public import TruthCore.Science.Identifiability

/-! Analyst formulations for #2103, with attribution deferred. The only
probability laws used here are the point masses forced by deterministic
readout at each fixed model. There is no distribution over histories. -/

@[expose] public section

namespace TruthCore.Science.HistoryObservationLaws

open MeasureTheory
open TruthCore.Modern.Hume.Induction (Trace)
open TruthCore.Explanation.NoFoundationLawChaos (generated copySchedule toggleFrom)
open TruthCore.Science.Identifiability (Identifies)
open TruthCore.Science.AdaptiveHistoryAccess

/-- Each model always returns its prescribed observation. The fixed Boolean
sample is unused; it assigns no weight to competing models. -/
noncomputable def deterministic {M O : Type} [MeasurableSpace O] (observe : M → O) :
    Identifiability.Experiment M Bool O where
  sampleLaw _ := Measure.dirac false
  probability _ := inferInstance
  readout m _ := observe m
  measurable_readout _ := measurable_const

scoped instance : MeasurableSpace (List Bool) := ⊤

scoped instance : MeasurableSingletonClass (List Bool) := ⟨fun _ => trivial⟩

/-- Within the supplied blind interface every finite adaptive experiment
leaves the past bit unidentified even from its exact observation law. The
selected history-sensitive audit identifies that bit over the same inputs. -/
def HistoricalBoundary : Prop :=
  (∀ policy n, ¬ Identifies (deterministic (transcript blind policy n)).law PastOccurred) ∧
  Identifies (deterministic (transcript audit probe 1)).law PastOccurred

/-- Read only the finite record through the cutoff, inclusive. -/
def recordThrough (n : Nat) (f : Trace) : Fin (n + 1) → Bool := fun i => f i.val

/-- If the two schedules are supplied, the exact law of the old record
cannot distinguish them. The observation at the switching successor has
distinct laws. The cutoffs do not select the metaphysically admitted laws. -/
def ScheduleBoundary : Prop :=
  ∀ n k, n ≤ k →
    let copy := generated copySchedule
    let switched := generated (toggleFrom k)
    (deterministic (recordThrough n)).law copy = (deterministic (recordThrough n)).law switched ∧
    (deterministic (fun f : Trace => f (k + 1))).law copy ≠
      (deterministic (fun f : Trace => f (k + 1))).law switched

end TruthCore.Science.HistoryObservationLaws
