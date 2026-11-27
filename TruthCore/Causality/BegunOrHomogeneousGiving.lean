module

public import TruthCore.Causality.SustainingDependence
public import TruthCore.Causality.TimeSymmetricGiving

/-!
# Begun and homogeneous histories together give concurrent actualization (#2103)

Analyst formulation, attribution deferred. Note:
`docs/notes/ca-horizontal-support.md`.

Two restrictions of weak concurrent actualization `40a97664`
(`ConcurrentActualization.ConcurrentlyActualized`) are already derived:

* for things with a first moment of presence (`f4850897`,
  `SustainingDependence.ConcurrentlyActualizedOnceBegun`, from onset `fa3e228b`
  and parity `5b24ef26`, by a transcription);
* for homogeneous things (`eb928359`,
  `TimeSymmetricGiving.ConcurrentlyActualizedIfHomogeneous`, from coverage,
  exercise and time symmetry).

The gap between them and `40a97664` is a structural premise about histories,
`BegunOrHomogeneous`: every received-esse thing that is present at some moment
of a history either has a first moment of presence there or is homogeneous
there. It mentions no giving and no cause. It excludes, for received-esse
things, exactly the beginningless histories whose moments the supplied `Facts`
or presence pattern distinguish (a beginningless *changing* thing), the case the
note's "Next test" leaves open.

`Control.Certificate` records, on one world with integer times and `false`
alone with received esse:

1. omitting the coverage premise: an eternal history in which a supplied fact
   marks moment `0`; nothing gives. Both restrictions hold vacuously, coverage
   and `40a97664` fail;
2. omitting the homogeneous restriction: the eternal stationary history with no
   giving. Coverage and the begun restriction hold, `40a97664` fails;
3. omitting the begun restriction: the begun history with giving at moment `0`
   only. Coverage and the homogeneous restriction hold, `40a97664` fails;
4. strictness: the eternal marked history with giving at every moment.
   `40a97664` holds and coverage fails, so the three premises together are
   strictly stronger than `40a97664`.

Applicability of every premise to reality remains OPEN. A countermodel shows
that a premise is needed in that interpretation, not that it is false.
-/

@[expose] public section

namespace TruthCore.Causality.BegunOrHomogeneousGiving

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized)
open TruthCore.Causality.SustainingDependence (ConcurrentlyActualizedOnceBegun)
open TruthCore.Causality.TimeSymmetricGiving
  (HomogeneousIn ConcurrentlyActualizedIfHomogeneous)

/-- Coverage of received-esse things by the two restricted cases: in every
history `v`, every received-esse thing that is present at some moment has a first
moment of presence in `v` (`BeginsAt`) or is homogeneous in `v` relative to the
supplied facts. -/
def BegunOrHomogeneous {W B T P : Type} [Preorder T] (h : History W B T)
    (Facts : W → B → T → Prop) (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x t z, EsseReceivedIn x z → h.IsAt v x t →
    (∃ b, BeginsAt h v x b) ∨ HomogeneousIn h Facts v x

namespace Control

open TruthCore.Causality.TimeSymmetricGiving.Control (eternal begun noGivingZ givesAtZero
  givesAlways noFacts)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)

/-- One supplied non-giving fact: `false` is marked at moment `0`. -/
def markedZero : Unit → Bool → Int → Prop := fun _ y t => y = false ∧ t = 0

/-- Omission and strictness controls for the begun-or-homogeneous combination,
on one world with integer times, `false` alone with received esse.
(1) Eternal history, moment `0` marked, no giving: both restrictions hold,
coverage and `40a97664` fail. (2) Eternal history, no marks, no giving: the
begun restriction and coverage hold, `40a97664` fails. (3) Begun history, no
marks, giving at moment `0` only: the homogeneous restriction and coverage
hold, `40a97664` fails. (4) Eternal history, moment `0` marked, giving at every
moment: `40a97664` holds and coverage fails. -/
def Certificate : Prop :=
  (ConcurrentlyActualizedOnceBegun eternal noGivingZ falseReceived ∧
    ConcurrentlyActualizedIfHomogeneous eternal noGivingZ markedZero falseReceived ∧
    ¬ BegunOrHomogeneous eternal markedZero falseReceived ∧
    ¬ ConcurrentlyActualized eternal noGivingZ falseReceived) ∧
  (ConcurrentlyActualizedOnceBegun eternal noGivingZ falseReceived ∧
    BegunOrHomogeneous eternal noFacts falseReceived ∧
    ¬ ConcurrentlyActualizedIfHomogeneous eternal noGivingZ noFacts falseReceived ∧
    ¬ ConcurrentlyActualized eternal noGivingZ falseReceived) ∧
  (ConcurrentlyActualizedIfHomogeneous begun givesAtZero noFacts falseReceived ∧
    BegunOrHomogeneous begun noFacts falseReceived ∧
    ¬ ConcurrentlyActualizedOnceBegun begun givesAtZero falseReceived ∧
    ¬ ConcurrentlyActualized begun givesAtZero falseReceived) ∧
  (ConcurrentlyActualized eternal givesAlways falseReceived ∧
    ¬ BegunOrHomogeneous eternal markedZero falseReceived)

end Control

end TruthCore.Causality.BegunOrHomogeneousGiving
