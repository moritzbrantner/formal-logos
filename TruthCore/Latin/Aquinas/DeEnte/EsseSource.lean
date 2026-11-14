module

public import TruthCore.Latin.Aquinas.DeEnte.ExtrinsicSource
public import TruthCore.Latin.Aquinas.DeEnte.EsseReception
public import TruthCore.Causality.EsseReception
public import TruthCore.Causality.NecessaryRootFork

/-!
# De ente: at most one being is its own esse, and every received esse goes back to it (#1628)

Thomas Aquinas, *De ente et essentia* c.3 in the Baur/Koch numbering of the
pinned Corpus Thomisticum witness (`AQUINAS-DE-ENTE-C3-4`, anchor [69874]; c.4
in the Leonine numbering). After arguing that a quiddity can be understood
without knowing whether it exists, the passage says esse is other than essence
"nisi forte sit aliqua res, cuius quiditas sit ipsum suum esse", argues that
such a thing "non potest esse nisi una et prima" from an inventory of the ways
anything is multiplied, infers that in every other thing esse is other than
quiddity, takes over the extrinsic-source step formalized in `ExtrinsicSource`
(#1629), and concludes:

> Et quia omne, quod est per aliud, reducitur ad illud quod est per se sicut ad
> causam primam, oportet quod sit aliqua res, quae sit causa essendi omnibus
> rebus, eo quod ipsa est esse tantum. Alias iretur in infinitum in causis, cum
> omnis res, quae non est esse tantum, habeat causam sui esse, ut dictum est.

Everything is stated on the shared q.3 a.4 `Profile`: `InAct x esse` (x is in
act as to being), `CausesIn c x esse` (the tenseless cause of being,
DEF-CAUSE-OF-PERFECTION, mode of causing not fixed by the type), and the
represented `essenceOf` / `esseOf` values in one `Principle` sort. "A thing
whose quiddity is its esse" is the represented identity
`esseOf x = essenceOf x`; nothing here gives it modal necessity, simplicity,
infinity or a divine name.

Three primitives (`Plurification`) carry the multiplication inventory; they are
constrained only by the readings that use them. The inventory is read
only at pairs of beings whose esse is their essence; there its third mode,
"one absolute and the other received in something", is the reception of esse
(`EsseReceivedIn` of `EsseReception`), since their nature is their esse.

The regress step is explicit: `NoInfiniteActualEsseCauseRegress` is
well-foundedness of the relation "c, in act, is a cause of being of the actual
x other than c". The passage's reduction principle (what is "per aliud" goes
back to what is "per se", here read only as: a distinct esse goes back to a
being whose esse is its essence, not as any sense of DISAMB per se) is not
assumed; it is derived from that premise and the #1629 step
`DistinctEsseHasOtherActualCause`. The cause relation is not restricted to
essentially ordered or simultaneous causes and is not called efficient.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

variable {B P R : Type}

/-- The three ways of multiplying something named in *De ente* c.3 [69874], as
primitive parameters. -/
structure Plurification (Being : Type) where
  /-- x and y are two candidates of one shared nature, so that their being two
  would be a multiplication (*plurificatio*) of that nature. -/
  SharesNature : Being → Being → Prop
  /-- Some difference is added to x's nature, as a genus is multiplied into
  species by differentiae. -/
  AddsDifference : Being → Prop
  /-- x's nature (form) is received in matter, as a species is multiplied into
  individuals by being received in different matters. -/
  InMatter : Being → Prop

/-- *De ente* c.3 [69874], "impossibile est, ut fiat plurificatio alicuius nisi
per additionem alicuius differentiae ..., vel per hoc quod forma recipitur in
diversis materiis ..., vel per hoc quod unum est absolutum et aliud in aliquo
receptum".

Read only at the instance the passage applies it to: two actual beings, each
of whose esse is its essence, that share a nature are one and the same unless
a difference is added to the nature in one of them, or one of them has it
received in matter, or one of them has its esse received in some principle.
For such beings the shared nature is esse, so "one absolute and another
received in something" is the reception of esse. The general inventory over
every nature is not encoded. Its exhaustiveness is the passage's assertion. -/
def PlurificationOnlyByThreeModesReading (p : Profile B P R) (q : Plurification B)
    (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ x y, p.InAct x p.esse → p.InAct y p.esse →
    p.esseOf x = p.essenceOf x → p.esseOf y = p.essenceOf y → q.SharesNature x y →
    ¬ (q.AddsDifference x ∨ q.AddsDifference y) →
    ¬ (q.InMatter x ∨ q.InMatter y) →
    ¬ ((∃ r, EsseReceivedIn x r) ∨ (∃ r, EsseReceivedIn y r)) → x = y

/-- OPEN analyst premise, attribution deferred (the #697
`UNRECEIVED-ESSE-INDIVIDUATION-BRIDGE` gap): any two actual beings each of
whose esse is its essence share one nature, so that their being two would be a
multiplication of it. The passage treats "a thing that is esse tantum" as one
nature without arguing it. A rival denies it: two such beings would differ as
wholes (primitive individuation, or two different whole essences each
identical with its own esse) without either being a multiplication of a common
nature. -/
def EsseIsEssenceBeingsShareNature (p : Profile B P R) (q : Plurification B) : Prop :=
  ∀ x y, p.InAct x p.esse → p.InAct y p.esse →
    p.esseOf x = p.essenceOf x → p.esseOf y = p.essenceOf y → q.SharesNature x y

/-- *De ente* c.3 [69874], "si autem ponatur aliqua res, quae sit esse tantum,
ita ut ipsum esse sit subsistens, hoc esse non recipiet additionem differentiae,
quia iam non esset esse tantum, sed esse et praeter hoc forma aliqua".

Read as: no difference is added to the nature of a being whose esse is its
essence. -/
def EsseTantumReceivesNoDifferenceReading (p : Profile B P R) (q : Plurification B) : Prop :=
  ∀ x, p.esseOf x = p.essenceOf x → ¬ q.AddsDifference x

/-- *De ente* c.3 [69874], "et multo minus reciperet additionem materiae, quia
iam esset esse non subsistens sed materiale".

Read as: the nature of a being whose esse is its essence is not received in
matter. -/
def EsseTantumNotInMatterReading (p : Profile B P R) (q : Plurification B) : Prop :=
  ∀ x, p.esseOf x = p.essenceOf x → ¬ q.InMatter x

/-- At most one actual being has its esse identical with its essence (*De ente*
c.3 [69874], "talis res, quae sit suum esse, non potest esse nisi una"). Only
"at most one": no such being is said to exist. -/
def AtMostOneEsseIsEssence (p : Profile B P R) : Prop :=
  ∀ x y, p.InAct x p.esse → p.InAct y p.esse →
    p.esseOf x = p.essenceOf x → p.esseOf y = p.essenceOf y → x = y

/-- c, in act as to being and other than x, is a cause of the esse of x, which
is also in act (`CausesIn c x esse`, mode unspecified, tenseless). -/
def ActualEsseCause (p : Profile B P R) (c x : B) : Prop :=
  c ≠ x ∧ p.InAct c p.esse ∧ p.InAct x p.esse ∧ p.CausesIn c x p.esse

/-- OPEN analyst premise, attribution deferred ("alias iretur in infinitum in
causis"): the relation `ActualEsseCause` is well-founded, so there is no
infinite descending chain of actual causes of being. It covers every cause of
being, not only essentially ordered or simultaneous ones, and says nothing
about causes of coming to be. The passage presupposes a no-regress principle
for some order of causes of esse; this unrestricted version is the
analyst's. -/
def NoInfiniteActualEsseCauseRegress (p : Profile B P R) : Prop :=
  WellFounded (ActualEsseCause p)

/-- Every actual x whose esse differs from its essence descends, through a
finite chain of actual causes of being (`Relation.TransGen`), from some actual
n whose esse is its essence: n heads that chain. n is not said to be
uncaused, the direct cause, the only such being, or necessary. -/
def EveryDistinctEsseHasEsseIsEssenceSource (p : Profile B P R) : Prop :=
  ∀ x, DistinctEsseAt p x →
    ∃ n, p.InAct n p.esse ∧ p.esseOf n = p.essenceOf n ∧
      Relation.TransGen (ActualEsseCause p) n x

/-- OPEN, ordinary existence premise: at least two different beings are in act
as to being. -/
def TwoActualBeings (p : Profile B P R) : Prop :=
  ∃ x y, x ≠ y ∧ p.InAct x p.esse ∧ p.InAct y p.esse

/-- One actual n whose esse is its essence has no actual cause of its esse and
heads a finite chain of actual causes of being to every other actual being: a
first cause of being of all others in that order ("aliqua res, quae sit causa
essendi omnibus rebus, eo quod ipsa est esse tantum"). Not asserted: that n
causes every esse directly, conserves it now, exists necessarily, is concrete
at a world, or is God. -/
def CommonEsseIsEssenceSource (p : Profile B P R) : Prop :=
  ∃ n, p.InAct n p.esse ∧ p.esseOf n = p.essenceOf n ∧
    (∀ c, ¬ ActualEsseCause p c n) ∧
    ∀ x, p.InAct x p.esse → x ≠ n → Relation.TransGen (ActualEsseCause p) n x

/-- Any two actual concrete roots of the selected grounding relation at w
(`NecessaryRootFork.ActualRoot`: concrete, existing at w, with no actual
concrete ground) are the same. Only "at most one": no root is said to exist,
and nothing is said about necessity or God identification. -/
def AtMostOneActualRootAt {W Bg : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W Bg) (w : W) : Prop :=
  ∀ x y, TruthCore.Causality.NecessaryRootFork.ActualRoot m w x →
    TruthCore.Causality.NecessaryRootFork.ActualRoot m w y → x = y

/-! ## Finite controls

Interpretations of the shared vocabulary only. They show which premises the
conclusions need under the encoded predicates, not that an infinite regress,
brute esse or two first beings is possible or plausible. -/

/-- Four beings for the two-source and nonvacuity controls. -/
inductive Four where
  | a | b | c | d

/-- Infinite regress: on `Nat`, n+1 causes the esse of n, all are in act and
none has esse equal to essence. The #1629 other-cause step holds and some
actual being has distinct esse; well-foundedness and the conclusion fail. -/
def InfiniteRegressControl : Prop :=
  ∃ p : Profile Nat Bool Unit,
    DistinctEsseHasOtherActualCause p ∧ DistinctEsseAt p 0 ∧
    ¬ NoInfiniteActualEsseCauseRegress p ∧
    ¬ EveryDistinctEsseHasEsseIsEssenceSource p

/-- Uncaused distinct esse: nothing causes anything, the regress premise holds,
the #1629 other-cause step fails, and so does the conclusion. -/
def UncausedDistinctEsseControl : Prop :=
  ∃ p : Profile Bool Bool Unit,
    DistinctEsseAt p false ∧ NoInfiniteActualEsseCauseRegress p ∧
    ¬ DistinctEsseHasOtherActualCause p ∧
    ¬ EveryDistinctEsseHasEsseIsEssenceSource p

/-- Two first sources (the #697 two-root shape): `a` and `b` each have esse
equal to essence, `a` causes the esse of `c` and `b` that of `d`. Every input of
the at-most-one argument holds except that the two share a nature; every input
of the regress and of the common-source argument holds except at-most-one. Both
at-most-one and the common source fail. -/
def TwoSourcesControl : Prop :=
  ∃ (p : Profile Four Bool Unit) (q : Plurification Four)
    (EsseReceivedIn : Four → Bool → Prop) (ReceptivePotencyTo : Bool → Bool → Prop),
    PlurificationOnlyByThreeModesReading p q EsseReceivedIn ∧
    EsseTantumReceivesNoDifferenceReading p q ∧ EsseTantumNotInMatterReading p q ∧
    TruthCore.Causality.EsseReception.EsseReceivedOnlyInOwnEssence p.essenceOf EsseReceivedIn ∧
    ReceiverInPotencyToReceivedEsseReading p.esseOf EsseReceivedIn ReceptivePotencyTo ∧
    TruthCore.Causality.EsseReception.NothingInReceptivePotencyToItself ReceptivePotencyTo ∧
    ¬ EsseIsEssenceBeingsShareNature p q ∧
    DistinctEsseHasOtherActualCause p ∧ NoInfiniteActualEsseCauseRegress p ∧
    EveryDistinctEsseHasEsseIsEssenceSource p ∧ TwoActualBeings p ∧
    ¬ AtMostOneEsseIsEssence p ∧ ¬ CommonEsseIsEssenceSource p

/-- Nonvacuity: `a` has esse equal to essence and causes the esse of `b`, `c`
and `d`, whose esse differs from their essence and is received in their
essence. Every input of the three arguments holds, and so do at-most-one, the
regress conclusion and the common source. -/
def EsseSourceNonvacuity : Prop :=
  ∃ (p : Profile Four Bool Unit) (q : Plurification Four)
    (EsseReceivedIn : Four → Bool → Prop) (ReceptivePotencyTo : Bool → Bool → Prop),
    PlurificationOnlyByThreeModesReading p q EsseReceivedIn ∧
    EsseIsEssenceBeingsShareNature p q ∧
    EsseTantumReceivesNoDifferenceReading p q ∧ EsseTantumNotInMatterReading p q ∧
    TruthCore.Causality.EsseReception.EsseReceivedOnlyInOwnEssence p.essenceOf EsseReceivedIn ∧
    ReceiverInPotencyToReceivedEsseReading p.esseOf EsseReceivedIn ReceptivePotencyTo ∧
    TruthCore.Causality.EsseReception.NothingInReceptivePotencyToItself ReceptivePotencyTo ∧
    (∃ x r, EsseReceivedIn x r) ∧
    DistinctEsseHasOtherActualCause p ∧ NoInfiniteActualEsseCauseRegress p ∧
    TwoActualBeings p ∧
    AtMostOneEsseIsEssence p ∧ EveryDistinctEsseHasEsseIsEssenceSource p ∧
    CommonEsseIsEssenceSource p

/-- All four controls together. -/
def EsseSourceControls : Prop :=
  InfiniteRegressControl ∧ UncausedDistinctEsseControl ∧ TwoSourcesControl ∧
    EsseSourceNonvacuity

end TruthCore.Latin.Aquinas.DeEnte
