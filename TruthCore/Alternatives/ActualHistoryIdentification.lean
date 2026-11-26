module

public import TruthCore.Alternatives.PhysicalGround
public import TruthCore.Explanation.NoFoundationLawChaos
public import TruthCore.Science.Identifiability

/-! The complete output of one represented Boolean history, compared at the
same structural role in the #468 ground models. The #1867 copy/toggle schedule
generates this output. Which schedule obtains is separate from what, if
anything, explains its actuality. The product below leaves that explanatory
dependence open. See the actual-history comparison in the #311 note. -/

@[expose] public section

namespace TruthCore.Alternatives.ActualHistoryIdentification

open PhysicalGround
open TruthCore.Explanation.NoFoundationLawChaos (generated)
open TruthCore.Modern.Hume.Induction (Trace)
open TruthCore.Latin.Aquinas.SummaTheologiae (WillFollowsIntellectReading)
open TruthCore.Science.Identifiability

/-- A #468 route and an explicitly supplied schedule for its represented
history. The schedule describes Boolean transitions, without a source-to-law
production rule. -/
structure Model where
  route : Route Bool Unit Unit
  switches : Nat → Bool

/-- Common necessary underived signature, structural premises, and the same
designated maximum in each alternative. -/
def admitted : Set Model :=
  {m | Signature m.route ∧ m.route.Structural ∧ m.route.Maximum false}

abbrev Profile := {m // m ∈ admitted}

def history (m : Model) : Trace := generated m.switches

/-- The two existing Stage 2 attributes at the designated root. This target
tests the intellect and will bridges at their original predicates. -/
def attributes (m : Model) : Prop × Prop :=
  (m.route.HasIntellect false, m.route.HasWill false)

/-- Explicit profile restriction by the two existing independent attribute
premises. Their real-world applicability remains open to inquiry. -/
def attributeAdmitted : Set Model :=
  {m | m ∈ admitted ∧ m.route.Immaterial ∧
    WillFollowsIntellectReading m.route.HasIntellect m.route.HasWill}

/-- Exact result for the stipulated history profile. Full trace identifies
the copy/toggle schedule. Each attribute fails to be identified even though
the designated necessary root and structural conditions are held fixed.
Adding the two attribute premises gives a nonempty identifying restriction.
For any supplied report family, splitting every tied pair that differs in the
attribute pair is the exact criterion for the augmented map. -/
def Boundary : Prop :=
  Identifies (fun m : Profile => history m.val) (fun m => m.val.switches) ∧
  (∃ p q : Profile, history p.val = history q.val ∧
    (attributes p.val).1 ∧ (attributes p.val).2 ∧
    ¬ (attributes q.val).1 ∧ ¬ (attributes q.val).2) ∧
  ¬ Identifies (fun m : Profile => history m.val) (fun m => (attributes m.val).1) ∧
  ¬ Identifies (fun m : Profile => history m.val) (fun m => (attributes m.val).2) ∧
  attributeAdmitted.Nonempty ∧
  (∀ m : attributeAdmitted, attributes m.val = (True, True)) ∧
  (∀ (I R : Type) (allowed : Set I) (report : Profile → I → R),
    Identifies (augment (fun m : Profile => history m.val) allowed report)
      (fun m => attributes m.val) ↔
      ∀ p q : Profile, history p.val = history q.val → attributes p.val ≠ attributes q.val →
        ∃ i : allowed, report p i.val ≠ report q i.val)

end TruthCore.Alternatives.ActualHistoryIdentification
