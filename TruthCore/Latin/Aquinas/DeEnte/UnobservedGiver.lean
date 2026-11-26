module

public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
public import TruthCore.Causality.SupplierAuditCertificates
public import TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit

/-! Pair observations of actual esse causes on one fixed, countably infinite roster. -/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.UnobservedGiver

open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit (EveryActualEsseBearerHasFiniteRootAudit)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The roster and actuality of its members are fixed. With `none` as giver
there are two ranks. With another giver, `none` takes the intermediate rank.
The direction is from lower rank (more in esse) to higher rank. -/
def rank (giver x : Option Nat) : Nat :=
  if x = giver then 0 else if giver = none ∨ x = none then 1 else 2

def rankedProfile (giver : Option Nat) :=
  controlProfile (fun x y => rank giver x < rank giver y)

/-- The comparison is allowed to vary with the candidate giver. -/
def moreIn (giver : Option Nat) (_ : Unit) (x y : Option Nat) : Prop :=
  rank giver x < rank giver y

/-- The selected giver is the unique maximum, the direct actual esse cause
of every other bearer, and the unique supplierless ancestor of every bearer.
Both causal comparison readings use the same assignment at the sole respect. -/
def RankedGiverProfile (giver : Option Nat) : Prop :=
  let p := rankedProfile giver
  (∀ x, p.InAct x p.esse) ∧
  (∀ x, rank giver x ≤ 2) ∧
  NoInfiniteActualEsseCauseRegress p ∧
  ClosedActualEsseCollectionsRooted p ∧
  CauseOfQualityInAnotherIsMoreSuchReading p.CausesIn (moreIn giver) ∧
  CauseOfBeingIsMoreInBeing p.CausesIn (moreIn giver) p.esse ∧
  MaximeEnsCausesBeingOfAllReading p.InAct (moreIn giver) p.CausesIn p.esse ∧
  (∀ x, IsMaximumIn p.InAct (moreIn giver) p.esse x ↔ x = giver) ∧
  (∀ x, x ≠ giver → ActualEsseCause p giver x) ∧
  (∀ x r, RootAncestor r x (ActualEsseCause p) ↔ r = giver) ∧
  EveryActualEsseBearerHasFiniteRootAudit p

/-- Every finite set of tested ordered pairs admits a matching rank profile
with a distinct unique maximal direct giver. The new giver is absent from
both projections of the tested pairs and directly gives `none` its esse.
These are structural interpretations of the actual cause dictionary. -/
def FinitePairGiverControl : Prop :=
  (∀ giver, RankedGiverProfile giver) ∧
  ∀ tested : Set (Option Nat × Option Nat), tested.Finite →
    ∃ h : Option Nat, h ≠ none ∧
      (∀ c x, (c, x) ∈ tested → c ≠ h ∧ x ≠ h ∧
        (ActualEsseCause (rankedProfile none) c x ↔
          ActualEsseCause (rankedProfile h) c x)) ∧
      ActualEsseCause (rankedProfile h) h none ∧
      ¬ RootAncestor none none (ActualEsseCause (rankedProfile h))

end TruthCore.Latin.Aquinas.DeEnte.UnobservedGiver
