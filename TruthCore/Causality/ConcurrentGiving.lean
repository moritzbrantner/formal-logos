module

public import Mathlib.Data.Bool.Basic
public import TruthCore.Causality.FrameAdapters
public import TruthCore.Causality.RelationalReceipt
public import TruthCore.Causality.TimeSymmetricGiving

/-! Same-moment giving and distinctness on the shared causality frame.
The model fixes the recipient, originator and effect-side moment across the
explanation, origin and receipt tests. Applicability to reality remains open.
-/

@[expose] public section

namespace TruthCore.Causality.ConcurrentGiving

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FrameAdapters (giving)
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized CausesOfBeingConcur)
open TruthCore.Causality.PresentReceipt
open TruthCore.Causality.RelationalReceipt
open TruthCore.Causality.SustainingCausation (CausingBeingIsSustaining GiverPresentWhenGiving)
open TruthCore.Causality.TimeSymmetricGiving

/-- Scope the exclusion of direct self-giving to received-esse bearers at
their moments of presence. This leaves earlier-to-later explanations and
operations of a thing on its proper parts open. -/
def NoReceivedSelfGiving {W B T R P : Type} (F : CausalityFrame W B T R)
    (E : B → P → Prop) : Prop :=
  ∀ v x t z, E x z → F.history.IsAt v x t → ¬ F.GivesAt v x x t

namespace Control

/-- One history with two beings present at both supplied moments
(`false` for moment 0, `true` for moment 1). The originator gives the
recipient being at moment 0 only. -/
def inertia : CausalityFrame Unit Bool Bool Unit where
  history :=
    { ontic := ⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ c x => c = true ∧ x = false⟩
      IsAt := fun _ _ _ => True
      now := true }
  GivesAt := fun _ c x t => c = true ∧ x = false ∧ t = false
  CausesIn := fun c x _ => c = true ∧ x = false
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun x c => x = false ∧ c = true
  PriorSimply := fun _ _ => False
  esse := ()

/-- The origin relation holds at both moments, including when the originator
is idle. -/
def origin : OriginRelation Unit Bool Bool :=
  ⟨fun _ x c _ => x = false ∧ c = true⟩

/-- No inducer of existential cessation occurs at either supplied moment. -/
def noInducer : Unit → Bool → Bool → Prop := fun _ _ _ => False

open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)

/-- A common inertia control for explanation, origin and standing receipt.
The originator's contact while giving, strict non-self-giving and concurrence
all hold. Concurrence is silent at the later, giverless moment. -/
def JointInertia : Prop :=
  let h := inertia.history
  let G := giving inertia
  let E := falseReceived
  let X := originOrInertia h G noInducer
  let R := standingReceipt h E
  MomentaryPSR h X E ∧ CessationNeedsInducer h noInducer ∧
  RelationAccompaniesEsse h origin E ∧ FoundedOnReceivedEsse h origin E ∧
  Irreflexive origin ∧ TermCoexists h origin ∧
  ReceptionIsPresent h R E ∧
  NoReceivedSelfGiving inertia E ∧ GiverPresentWhenGiving h G ∧
  CausesOfBeingConcur G inertia.CausesIn inertia.esse ∧
  ¬ ExplanationNeedsGiver h G X E ∧ ¬ TermGives G origin ∧
  ¬ ReceivingIsCorrelativeWithGiving G R ∧
  ¬ ConcurrentlyActualized h G E ∧
  ¬ CausingBeingIsSustaining h G inertia.CausesIn inertia.esse

/-- Same inertia frame, with receipt read as passion. Receipt at onset and
correlativity both hold, but receipt at every moment of presence fails. -/
def OnsetOnlyPassion : Prop :=
  let h := inertia.history
  let G := giving inertia
  let E := falseReceived
  let R := passionReceipt G E
  ReceptionAtOnset h R E ∧ ReceivingIsCorrelativeWithGiving G R ∧
  ¬ ReceptionIsPresent h R E ∧ ¬ ConcurrentlyActualized h G E

end Control
end TruthCore.Causality.ConcurrentGiving
