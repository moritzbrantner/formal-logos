module

public import TruthCore.Causality.FirstMoverNecessity
public import TruthCore.Causality.TimeSymmetricGiving
public import TruthCore.Causality.UnderivedNonComposite

/-!
# Received esse and an actually present giver

Fixes the shared CausalityFrame, reading world, CAUSE_2 respect and bearer.
Reception in an intrinsic principle and causing that bearer's esse by a distinct
cause (mode unspecified) remain different relations. Actuality of the world-free esse-cause is
not built into either relation. See docs/notes/modal-spine.md.

The following stronger endpoint is not asserted as established; its two
support bundles and their OPEN causal/presence interfaces are explicit in the
Results module. The First Way consumes its weaker projection B2, so no
independent first-mover witness is introduced.
-/

@[expose] public section

namespace TruthCore.Causality.ReceivedEsseActualGiver

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

/-- Stronger than B2: each contingent actual bearer has a distinct CAUSE_2 of
its esse which is itself actual at the same selected world. This says nothing
about whether receipt is into an essence, whether the cause is efficient or
sustaining, or whether the giver is itself metaphysically necessary. -/
def ContingentHasActualEsseGiverAt {W B T R : Type}
    (F : CausalityFrame W B T R) (w : W) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x →
    ∃ c, c ≠ x ∧ F.history.ontic.ExistsAt w c ∧ F.CausesIn c x F.esse


/-! ## Source presence is strictly stronger than a tenseless CAUSE_2 edge -/

namespace Control

/-- The mover `true` is contingent and exists at the reading world `true`; its
stipulated CAUSE_2 `false` exists at no world. No `IsFirstUnmovedMover` fact is
asserted of it. This is a structural interpretation, *not* a metaphysical
possibility certificate. -/
def absentSourceExists (v x : Bool) : Prop := v = true ∧ x = true
def absentSourceCauses (c x r : Bool) : Prop := c = false ∧ x = true ∧ r = true

def absentSourceFrame : CausalityFrame Bool Bool Unit Bool :=
  FirstMoverNecessity.Model.mk absentSourceExists absentSourceCauses
    FirstMoverNecessity.Model.noPrior

/-- Route 1 omission witness: the mover `true` receives its esse (in any
principle). -/
def receivedByMover (x _ : Bool) : Prop := x = true

/-- Route 2 omission witness: everything is in act of esse; essence is the
being itself and every esse is the principle `false`, so only the mover `true`
has esse distinct from essence. No sufficiency of essential principles. -/
def actAll (_ _ : Bool) : Prop := True
def esseFalse (_ : Bool) : Bool := false
def essenceSelf (b : Bool) : Bool := b
def noSuffice (_ : Bool) : Prop := False

open TruthCore.Causality.FirstMoverNecessity
  (ContingentReceivesEsse ContingentHasDistinctEsse ContingentHasDistinctEsseCause esseProfile)
open TruthCore.Causality.TimeSymmetricGiving (ReceivedEsseHasCauseOfBeing)
open TruthCore.Causality.UnderivedNonComposite (UnitingCausesPresent)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseRequiresExternalCauseReading)

/-- Presence controls in the same absent-source frame, a structural
interpretation only. The mover `true` is contingent; B2 holds and the
actual-giver endpoint fails, so B2 does not entail it (strictness). Both
routes' premises other than the world-presence interface hold here: route 1's
R1 and reception-to-CAUSE_2 coverage (with `receivedByMover`), and route 2's
B6, selected-world actuality and q.3 a.4 reading (with `actAll`, `essenceSelf`,
`esseFalse`). The world-presence interface `UnitingCausesPresent` fails and so
does the endpoint, so neither route's conclusion follows without it. -/
def PresenceControls : Prop :=
  ContingentAt absentSourceFrame.history.ontic true true ∧
  ContingentHasDistinctEsseCause absentSourceFrame true ∧
  ¬ ContingentHasActualEsseGiverAt absentSourceFrame true ∧
  ¬ UnitingCausesPresent absentSourceFrame.history.ontic absentSourceFrame.CausesIn
    absentSourceFrame.esse true ∧
  ContingentReceivesEsse absentSourceFrame true receivedByMover ∧
  ReceivedEsseHasCauseOfBeing absentSourceFrame.CausesIn absentSourceFrame.esse
    receivedByMover ∧
  ContingentHasDistinctEsse absentSourceFrame true essenceSelf esseFalse ∧
  ExistingInActAt absentSourceFrame.history.ontic actAll absentSourceFrame.esse true ∧
  DistinctEsseRequiresExternalCauseReading
    (esseProfile absentSourceFrame actAll essenceSelf esseFalse noSuffice)

end Control

end TruthCore.Causality.ReceivedEsseActualGiver
