module

public import TruthCore.Causality.Frame
public import TruthCore.Causality.ConcurrentActualization
public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.CausalMapsBatch1

/-!
# Adapters: existing causality statements over one `CausalityFrame`

Owner decision 2026-11-19 (#1784). Each definition below instantiates an
existing proposition, unchanged, from the fields of a `CausalityFrame`:
`ConcurrentActualization` and `SustainingCausation` (history and being-giving),
`Round2Grounding` (causes of esse and dependence for being) and
`CausalMapsBatch1` (moving, causing a perfection, dependence and simple
priority). The adapter adds no premise and asserts nothing. It only
supplies the arguments. Each one comes with a check, by `Iff.rfl`, that its
statement unfolds to the original body written in frame fields. So the
adapted statements of different modules share the symbols `F.GivesAt`,
`F.CausesIn`, `F.DependsForBeing` and `F.PriorSimply`. They are still
related only by the explicit bridges the corpus records as open premises.

Parameters that are not frame fields stay parameters: `EsseReceivedIn`
(DEF-ESSE-RECEIVED-IN, with its own principle type) and `Participates`
(DEF-PARTICIPATED-ESSE).
-/

@[expose] public section

namespace TruthCore.Causality.FrameAdapters

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.SustainingCausation (BeingGiving SustainsBeing)

variable {W B T R : Type} (F : CausalityFrame W B T R)

/-- The frame's being-giving as the `SustainingCausation` structure. -/
def giving : BeingGiving W B T := ⟨F.GivesAt⟩

/-! ## ConcurrentActualization and SustainingCausation -/

/-- Concurrent actualization, weak version, over the frame. -/
def ConcurrentlyActualized {P : Type} (EsseReceivedIn : B → P → Prop) : Prop :=
  ConcurrentActualization.ConcurrentlyActualized F.history (giving F) EsseReceivedIn

theorem concurrentlyActualized_iff {P : Type} (EsseReceivedIn : B → P → Prop) :
    ConcurrentlyActualized F EsseReceivedIn ↔
      ∀ v x t z, EsseReceivedIn x z → F.history.IsAt v x t → ∃ g, F.GivesAt v g x t :=
  Iff.rfl

/-- Concurrence of causes of being, over the frame: the existing open bridge
from the tenseless `CausesIn … esse` to time-indexed `GivesAt`. -/
def CausesOfBeingConcur : Prop :=
  ConcurrentActualization.CausesOfBeingConcur (giving F) F.CausesIn F.esse

theorem causesOfBeingConcur_iff :
    CausesOfBeingConcur F ↔
      ∀ v c g x t, c ≠ x → F.CausesIn c x F.esse → F.GivesAt v g x t → F.GivesAt v c x t :=
  Iff.rfl

/-- The weak sustaining reading, over the frame. -/
def CausingAnothersBeingIsSustaining : Prop :=
  ConcurrentActualization.CausingAnothersBeingIsSustaining F.history (giving F) F.CausesIn F.esse

theorem causingAnothersBeingIsSustaining_iff :
    CausingAnothersBeingIsSustaining F ↔
      ∀ v c x, c ≠ x → F.CausesIn c x F.esse → (∃ t, F.history.IsAt v x t) →
        SustainsBeing F.history (giving F) v c x :=
  Iff.rfl

/-- CAUSE_OF_BEING_2 over the frame: `c` gives `x` being whenever `x` is present. -/
theorem sustainsBeing_iff (v : W) (c x : B) :
    SustainsBeing F.history (giving F) v c x ↔
      (∃ t, F.history.IsAt v x t) ∧ ∀ t, F.history.IsAt v x t → F.GivesAt v c x t :=
  Iff.rfl

/-! ## Round2Grounding -/

/-- A thing whose esse is caused by another depends for its being on it, over
the frame. -/
def EsseEffectDependsOnItsCause : Prop :=
  Round2Grounding.EsseEffectDependsOnItsCause F.CausesIn F.esse F.DependsForBeing

theorem esseEffectDependsOnItsCause_iff :
    EsseEffectDependsOnItsCause F ↔
      ∀ c x, c ≠ x → F.CausesIn c x F.esse → F.DependsForBeing x c :=
  Iff.rfl

/-- Participated esse has a distinct cause, over the frame. -/
def ParticipatedEsseHasDistinctCause (Participates : B → Prop) : Prop :=
  Round2Grounding.ParticipatedEsseHasDistinctCause Participates F.CausesIn F.esse

theorem participatedEsseHasDistinctCause_iff (Participates : B → Prop) :
    ParticipatedEsseHasDistinctCause F Participates ↔
      ∀ x, Participates x → ∃ c, c ≠ x ∧ F.CausesIn c x F.esse :=
  Iff.rfl

/-- Dependence for being is asymmetric, over the frame. -/
def DependenceForBeingAsymmetric : Prop :=
  Round2Grounding.DependenceForBeingAsymmetric F.DependsForBeing

theorem dependenceForBeingAsymmetric_iff :
    DependenceForBeingAsymmetric F ↔
      ∀ x y, F.DependsForBeing x y → ¬ F.DependsForBeing y x :=
  Iff.rfl

/-! ## CausalMapsBatch1 -/

/-- Nonmutual dependence suffices for simple priority, over the frame. -/
def NonmutualDependenceSufficesForPriority : Prop :=
  CausalMapsBatch1.NonmutualDependenceSufficesForPriority F.PriorSimply F.DependsForBeing

theorem nonmutualDependenceSufficesForPriority_iff :
    NonmutualDependenceSufficesForPriority F ↔
      ∀ y x, F.DependsForBeing x y → ¬ F.DependsForBeing y x → F.PriorSimply y x :=
  Iff.rfl

/-- Whatever moves another in a respect causes that other's being so, over the
frame: the existing open bridge from CAUSE_1 to CAUSE_2. -/
def MoverCausesWhatItMovesTo : Prop :=
  CausalMapsBatch1.MoverCausesWhatItMovesTo F.MovesIn F.CausesIn

theorem moverCausesWhatItMovesTo_iff :
    MoverCausesWhatItMovesTo F ↔ ∀ y x r, F.MovesIn y x r → F.CausesIn y x r :=
  Iff.rfl

end TruthCore.Causality.FrameAdapters
