module

public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Causality.GradesFrame
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1

/-!
# The q.4 a.2 sentence "omnium perfectiones pertinent ad perfectionem essendi"

Analyst formulations, attribution deferred. This module serves the warrant
evaluation of the one ST I q.4 a.2 co. sentence (`5c5281dd`, "omnium autem
perfectiones pertinent ad perfectionem essendi: secundum hoc enim aliqua perfecta
sunt, quod aliquo modo esse habent") on which two loci of the case rest.

* **Universal transfer.** `791fa216` (`PerfectionsAreModesOfBeing`: whatever a
  thing has in act is a mode of its being) together with `2f6b9eff` (a total cause
  of a thing's being causes each of its modes of being). `ModeOfBeing` is a
  primitive parameter (DEF-MODE-OF-BEING).
* **Subsistent esse.** `c4fb87a6` (`PurePerfectionsPertainToBeing`: every pure
  perfection is a perfection of being) together with `d164b1ff`
  (`OwnBeingLacksNoPerfectionOfBeing`: what is its own being has every perfection
  of being). `OfBeing` is a primitive parameter.

In every registered consumer each primitive occurs in exactly the two premises of
its pair. `modesPairIffTotalTransfer` and `ownBeingPairIffEveryPure` show what such
a pair says when nothing else constrains the primitive: exactly the composite
claim, with the primitive as a middle term. A decomposition of this kind adds no
warrant beyond whatever fixes the primitive's meaning. `dependenceReading` shows
how the load moves under the weakest reading of "mode of being", the one the
sentence's own "secundum hoc enim" clause supplies.

Everything about transfer is over the shared `GradesFrame` (`F.InAct` IN_ACT_4,
`F.CausesIn` CAUSE_2, `F.esse`). `TotalCauseOfBeing` is the primitive of
DEF-TOTAL-CAUSE-OF-BEING. The subsistent-esse vocabulary (`OwnBeing`, `Has`,
`Pure`) is that of `WholePowerPerfection`, over real determinations `D`, not
respects. -/

@[expose] public section

namespace TruthCore.Causality.ModeOfBeingMiddleTerm

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.Round2PerfectionPrimacy
  (PerfectionsAreModesOfBeing TotalCauseCausesModesOfBeing)
open TruthCore.Causality.WholePowerPerfection
  (OwnBeingLacksNoPerfectionOfBeing PurePerfectionsPertainToBeing)
open TruthCore.Latin.Aquinas.SummaTheologiae (ActualityOnlyInsofarAsBeingReading)

variable {W B T R D : Type}

/-- The composite of the transfer pair: a total cause of a thing's being causes
each perfection that thing has in act. -/
def TotalCauseCausesEveryActualPerfection (F : GradesFrame W B T R)
    (TotalCauseOfBeing : B → B → Prop) : Prop :=
  ∀ c x r, TotalCauseOfBeing c x → F.InAct x r → F.CausesIn c x r

/-- The transfer pair is the composite with a middle term: for some reading of
"mode of being", every actual perfection is a mode of being and a total cause of
being causes each mode, exactly when a total cause of being causes each actual
perfection. -/
def ModesPairIffTotalTransfer (F : GradesFrame W B T R)
    (TotalCauseOfBeing : B → B → Prop) : Prop :=
  (∃ ModeOfBeing : B → R → Prop,
      PerfectionsAreModesOfBeing F.InAct ModeOfBeing ∧
      TotalCauseCausesModesOfBeing TotalCauseOfBeing ModeOfBeing F.CausesIn) ↔
    TotalCauseCausesEveryActualPerfection F TotalCauseOfBeing

/-- The dependence reading of "mode of being", from the sentence's own ground
("secundum hoc enim aliqua perfecta sunt, quod aliquo modo esse habent"): `r` is a
mode of `x`'s being when `x` has `r` in act and has being. -/
def DependenceMode (F : GradesFrame W B T R) (x : B) (r : R) : Prop :=
  F.InAct x r ∧ F.InAct x F.esse

/-- On the dependence reading, given that nothing has actuality except insofar as
it is (`7067553d`, q.4 a.1 ad 3), the mode premise holds, and the total-cause
premise is exactly the composite: the whole load moves to `2f6b9eff`. -/
def DependenceReadingShiftsLoad (F : GradesFrame W B T R)
    (TotalCauseOfBeing : B → B → Prop) : Prop :=
  ActualityOnlyInsofarAsBeingReading F.InAct F.esse →
    PerfectionsAreModesOfBeing F.InAct (DependenceMode F) ∧
    (TotalCauseCausesModesOfBeing TotalCauseOfBeing (DependenceMode F) F.CausesIn ↔
      TotalCauseCausesEveryActualPerfection F TotalCauseOfBeing)

/-- The composite of the subsistent-esse pair: whatever is its own being has every
pure perfection. -/
def OwnBeingHasEveryPurePerfection (OwnBeing : B → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) : Prop :=
  ∀ x, OwnBeing x → ∀ d, Pure d → Has x d

/-- The subsistent-esse pair is the composite with a middle term: for some reading
of "perfection of being", what is its own being has every perfection of being and
every pure perfection is a perfection of being, exactly when what is its own being
has every pure perfection. -/
def OwnBeingPairIffEveryPure (OwnBeing : B → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) : Prop :=
  (∃ OfBeing : D → Prop,
      OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing ∧
      PurePerfectionsPertainToBeing Pure OfBeing) ↔
    OwnBeingHasEveryPurePerfection OwnBeing Has Pure

/-! ## Two readings of "perfection of being" on one subsistent source -/

namespace Control

/-- Beings: `false` is a source that is its own being, `true` a living effect.
Determinations: `false` stands for being, `true` for life, a Boolean stand-in,
not any recorded sense of LIVING. -/
def ownBeing (b : Bool) : Prop := b = false

/-- Both determinations are stipulated pure. -/
def pure (_ : Bool) : Prop := True

/-- The thin reading: the source has being and nothing further; the effect has
both. -/
def hasThin (b d : Bool) : Prop := d = false ∨ b = true

/-- On the thin reading only being is a perfection of being. -/
def ofBeingThin (d : Bool) : Prop := d = false

/-- The act reading: every pure determination is a perfection of being, and the
source has every determination. -/
def hasAct (_ _ : Bool) : Prop := True

/-- Statements about these two profiles only. Thin profile: the source is its own
being and lacks no perfection of being (`d164b1ff` holds), but the pure
determination standing for life is not a perfection of being (`c4fb87a6` fails),
and the source lacks it. Act profile, with the same source and purity: both
premises hold and the source has every pure determination. -/
def Controls : Prop :=
  OwnBeingLacksNoPerfectionOfBeing ownBeing hasThin ofBeingThin ∧
  ¬ PurePerfectionsPertainToBeing pure ofBeingThin ∧
  ¬ OwnBeingHasEveryPurePerfection ownBeing hasThin pure ∧
  OwnBeingLacksNoPerfectionOfBeing ownBeing hasAct pure ∧
  PurePerfectionsPertainToBeing pure pure ∧
  OwnBeingHasEveryPurePerfection ownBeing hasAct pure

end Control

end TruthCore.Causality.ModeOfBeingMiddleTerm
