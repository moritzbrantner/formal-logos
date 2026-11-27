module

public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Causality.GradesFrame
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
public import TruthCore.Causality.ReceptionLimitation

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
a pair says when nothing else constrains the primitive: existentially closed over
the primitive, the pair is equivalent to the composite claim. This is a general fact
about any such middle-term decomposition, not something special to these pairs.
`dependenceReading` shows how the load moves under the weakest reading of "mode of
being", the one the sentence's "secundum hoc enim" clause yields when read as a
necessary condition. Aquinas uses that clause for a constitutive reading; that use
is not encoded here.

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

/-- MODE_OF_BEING_1, the dependence reading of "mode of being": the sentence's
ground ("secundum hoc enim aliqua perfecta sunt, quod aliquo modo esse habent")
read as a necessary condition. `r` is a
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

/-! ## Senses and the two act-of-being theses

"Perfection of being" has two readings that the pair leaves open.
PERFECTION_OF_BEING_1, thin: only being itself is a perfection of being
(`ThinOfBeing`). PERFECTION_OF_BEING_2, intensive esse: a perfection of esse
itself, a way of being that the act of being includes (`IntensiveEsseFrame.OfEsse`,
an explicitly primitive field).

Two different act-of-being theses are separated here. R-act₁
(`FiniteEsseReceivedAndLimited`): the esse of whatever is not its own being is
received in a principle and limited. R-act₂ (`IntensiveEsse`): every pure
perfection is a perfection of esse itself. The controls show that R-act₁, with the
reception and purity interfaces, does not give R-act₂. -/

/-- PERFECTION_OF_BEING_1, thin reading: `d` is a perfection of being only if it is
the determination `being` itself. -/
def ThinOfBeing (being : D) (d : D) : Prop := d = being

/-- The primitive of PERFECTION_OF_BEING_2. -/
structure IntensiveEsseFrame (D : Type) where
  /-- `OfEsse d`: `d` is a perfection of esse itself, a way of being that the act
  of being includes (intensive esse). Explicitly primitive. -/
  OfEsse : D → Prop

/-- R-act₂, intensive esse: every pure perfection is a perfection of esse itself. -/
def IntensiveEsse (I : IntensiveEsseFrame D) (Pure : D → Prop) : Prop :=
  ∀ d, Pure d → I.OfEsse d

/-- R-act₁: the esse of whatever is not its own being is received in a principle,
as act in receiving potency, and is limited. -/
def FiniteEsseReceivedAndLimited {P : Type} (OwnBeing : B → Prop)
    (EsseReceivedIn : B → P → Prop) (EsseLimited : B → Prop) : Prop :=
  ∀ x, ¬ OwnBeing x → (∃ p, EsseReceivedIn x p) ∧ EsseLimited x

/-- Ad 3 read formally or eminently: whatever is its own being lacks no perfection
of being, being in act in it in the shared frame's `F.InAct` (IN_ACT_4, the mode of
possession left open: formal, virtual or eminent), "nulla de perfectionibus essendi
potest deesse". It does not say that the bearer has the perfection as a real
determination (`Has`, HAVING_EVERY_PERFECTION_2). -/
def OwnBeingLacksNoPerfectionOfBeingInAct (F : GradesFrame W B T R)
    (OwnBeing : B → Prop) (OfBeing : R → Prop) : Prop :=
  ∀ x, OwnBeing x → ∀ r, OfBeing r → F.InAct x r

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

/-- Recipients: only the effect. -/
def recipient (b : Bool) : Prop := b = true

/-- The effect's esse is received in its (single) principle and is limited. -/
def received (b : Bool) (_ : Unit) : Prop := b = true

def limited (b : Bool) : Prop := b = true

/-- A grades frame on the same beings and determinations, with every determination
in act in every being in the mode-open sense (IN_ACT_4): the source lacks nothing,
formally or eminently. Determination `false` (being) is `esse`. -/
def eminentFrame : GradesFrame Unit Bool Unit Bool where
  history :=
    { ontic := ⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩
      IsAt := fun _ _ _ => True
      now := () }
  GivesAt := fun _ _ _ _ => False
  CausesIn := fun _ _ _ => False
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := false
  InAct := fun _ _ => True
  MoreIn := fun _ _ _ => False

/-- Statements about these two profiles only. Thin profile: the source is its own
being and lacks no perfection of being (`d164b1ff` holds), but the pure
determination standing for life is not a perfection of being (`c4fb87a6` fails),
and the source lacks it. Act profile, with the same source and purity: both
premises hold and the source has every pure determination. On the thin profile,
with the effect as the only recipient, R-act₁ (`FiniteEsseReceivedAndLimited`),
own being is no recipient (`7338142d`) and a nonrecipient's determinations are
pure (`32695660`) all hold, while R-act₂ (`IntensiveEsse`) with the thin reading
fails; with the intensive reading taken as purity it holds. These two R-act results
are non-entailment from the vocabulary alone: R-act₁ and the two interfaces never
mention `OfEsse`.

Locus (b) needs `d164b1ff` as well as R-act₂. On the thin profile with the
intensive reading taken as purity, R-act₂, purity and own being hold, but the source
does not really have the stand-in for life, so `d164b1ff` read intensively fails.
Keeping `9a0a4951` (lacking nothing in the mode-open act, in `eminentFrame`) while
rejecting real having is satisfiable on the same source. -/
def Controls : Prop :=
  OwnBeingLacksNoPerfectionOfBeing ownBeing hasThin ofBeingThin ∧
  ¬ PurePerfectionsPertainToBeing pure ofBeingThin ∧
  ¬ OwnBeingHasEveryPurePerfection ownBeing hasThin pure ∧
  OwnBeingLacksNoPerfectionOfBeing ownBeing hasAct pure ∧
  PurePerfectionsPertainToBeing pure pure ∧
  OwnBeingHasEveryPurePerfection ownBeing hasAct pure ∧
  FiniteEsseReceivedAndLimited ownBeing received limited ∧
  TruthCore.Causality.ReceptionLimitation.OwnBeingIsNoRecipient ownBeing recipient ∧
  TruthCore.Causality.ReceptionLimitation.NonRecipientDeterminationsArePure
    recipient hasThin pure ∧
  ¬ IntensiveEsse ⟨ofBeingThin⟩ pure ∧
  IntensiveEsse ⟨pure⟩ pure ∧
  -- locus (b) without d164b1ff: R-act₂, purity and own being, no real having
  ownBeing false ∧ pure true ∧ ¬ hasThin false true ∧
  ¬ OwnBeingLacksNoPerfectionOfBeing ownBeing hasThin pure ∧
  -- keep 9a0a4951 (formal or eminent), reject real having
  OwnBeingLacksNoPerfectionOfBeingInAct eminentFrame ownBeing pure

end Control

end TruthCore.Causality.ModeOfBeingMiddleTerm
