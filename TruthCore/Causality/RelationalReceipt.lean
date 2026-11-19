module

public import TruthCore.Causality.PresentReceipt

/-!
# Receipt of esse as a real relation to the principle of being (after ST I q.45 a.3)

Analyst formulations, attribution deferred. Research note:
`docs/notes/sustaining-vs-existential-inertia.md`, section 6.

The present-receipt test (attempt `50e08b09`) found that on each defined
sense of present-tense receipt (disambiguation `71d3bdb7`) one of its two
premises restates weak concurrent actualization `40a97664`. Its named next
test was a relational reading of receipt that carries content beyond
reception plus presence, and on which correlativity has warrant independent
of `40a97664`.

ST I q.45 a.3 co. (read in the pinned Leonine witness, passage `fb7bd7bb`)
says that creation in the creature is nothing but a certain relation to the
Creator as to the principle of its being. Ad 1 says the creature's relation
to God is real and God's relation to the creature is of reason only. Ad 3 says
the creature is the subject of that relation and prior to it in being, as a
subject is to an accident, but that the relation has a certain priority on the
side of its term, the principle of the creature. ST I q.13 a.7 co. (passage
`12d8ecc5`) places the creature's relation to God among relations real in one
extreme and of reason in the other, and makes relations between a being and a
non-being, and of a thing to itself, relations of reason. These readings are
recorded in the note and are not claims.

**Origin relation** (`OriginRelation.RelatedAt v x g t`, explicitly
PRIMITIVE). In history `v`, at moment `t`, `x` bears a real relation to `g` as
to the principle of its being. It says nothing about whether `g` is acting at
`t`. No axiom ties it to `GivesAt` or to presence.

**Foundation** (`FoundedOnReceivedEsse`). Whatever bears the relation at `t`
has its esse received in some principle and is present at `t`: a necessary
condition suggested by the subject-to-accident order of q.45 a.3 ad 3. The
priority itself is not typed.

**Irreflexivity** (`Irreflexive`) and **non-mutuality** (`NonMutual`). No
thing bears the relation to itself; the term bears no origin relation back to
its bearer. These type the structural part of q.13 a.7's classification: a
relation of a thing to itself is of reason, and the creature's relation to God
is real in the creature only.

**RECEIVES_ESSE_AT_3, relational receipt** (`relationalReceipt`). `z` receives
`x`'s esse at `t` iff `x`'s esse is received in `z`, `x` is present at `t`,
and `x` bears the origin relation at `t` to something. It is standing receipt
(RECEIVES_ESSE_AT_2) with the relation added.

Three open premises about the relation:

- **Accompaniment** (`RelationAccompaniesEsse`). Whatever has received esse
  bears the relation to something at every moment at which it is present.
- **Coexistence of the term** (`TermCoexists`). Whoever is the term of the
  relation at `t` is present at `t`. A real relation needs an existing term;
  a relation to what is not is one of reason only.
- **Giving by the term** (`TermGives`). Whoever is the term of the relation at
  `t` is giving the bearer being at `t`.

Results: the present-tense reading on RECEIVES_ESSE_AT_3 is accompaniment.
Given accompaniment, correlativity on RECEIVES_ESSE_AT_3 is equivalent to
`40a97664`. Accompaniment and giving by the term give `40a97664`. With the
relation left open, some founded, accompanying relation whose term gives
exists iff `40a97664` holds; for a fixed relation, giving by the term is
stronger than `40a97664` requires (`Control` part 5). Foundation,
irreflexivity, non-mutuality, accompaniment and coexistence of the term do not
entail `40a97664`, even when received onset is given
(`CoexistentTermDoesNotCarryTheCrux`, witnessed by `Control` part 1: a
creator present throughout who gives at onset only).

Applicability of every premise below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.RelationalReceipt

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.SustainingDependence (ReceivedOnsetIsGiven)
open TruthCore.Causality.PresentReceipt

/-- Origin relation, an explicitly primitive relation: `RelatedAt v x g t`
says that in history `v`, at moment `t`, `x` bears a real relation to `g` as to
the principle of its being. -/
structure OriginRelation (W B T : Type) where
  RelatedAt : W → B → B → T → Prop

/-- Foundation on received esse: whatever bears the origin relation at `t` has
its esse received in some principle and is present at `t`. -/
def FoundedOnReceivedEsse {W B T P : Type} (h : History W B T) (O : OriginRelation W B T)
    (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x g t, O.RelatedAt v x g t → (∃ z, EsseReceivedIn x z) ∧ h.IsAt v x t

/-- Irreflexivity: no thing bears the origin relation to itself. -/
def Irreflexive {W B T : Type} (O : OriginRelation W B T) : Prop :=
  ∀ v x g t, O.RelatedAt v x g t → g ≠ x

/-- Non-mutuality: the term of the origin relation bears no origin relation
back to its bearer at the same moment. -/
def NonMutual {W B T : Type} (O : OriginRelation W B T) : Prop :=
  ∀ v x g t, O.RelatedAt v x g t → ¬ O.RelatedAt v g x t

/-- Accompaniment: in every history, whatever has its esse received in some
principle bears the origin relation to something at every moment at which it
is present. -/
def RelationAccompaniesEsse {W B T P : Type} (h : History W B T) (O : OriginRelation W B T)
    (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x z t, EsseReceivedIn x z → h.IsAt v x t → ∃ g, O.RelatedAt v x g t

/-- Coexistence of the term: in every history, the term of the origin relation
at `t` is present at `t`. -/
def TermCoexists {W B T : Type} (h : History W B T) (O : OriginRelation W B T) : Prop :=
  ∀ v x g t, O.RelatedAt v x g t → h.IsAt v g t

/-- Giving by the term: in every history, the term of the origin relation at
`t` gives the bearer being at `t`. -/
def TermGives {W B T : Type} (G : BeingGiving W B T) (O : OriginRelation W B T) : Prop :=
  ∀ v x g t, O.RelatedAt v x g t → G.GivesAt v g x t

/-- RECEIVES_ESSE_AT_3, receipt as a real relation to the principle of being:
`z` receives `x`'s esse at `t` iff `x`'s esse is received in `z`, `x` is present
at `t`, and `x` bears the origin relation at `t` to something. -/
def relationalReceipt {W B T P : Type} (h : History W B T) (O : OriginRelation W B T)
    (EsseReceivedIn : B → P → Prop) : Receipt W B T P :=
  ⟨fun v z x t => EsseReceivedIn x z ∧ h.IsAt v x t ∧ ∃ g, O.RelatedAt v x g t⟩

/-- On the relational sense the present-tense reading of reception is
accompaniment, for every history, origin relation and reception predicate. -/
def RelationalPresentIsAccompaniment : Prop :=
  ∀ (W B T P : Type) (h : History W B T) (O : OriginRelation W B T)
    (EsseReceivedIn : B → P → Prop),
    ReceptionIsPresent h (relationalReceipt h O EsseReceivedIn) EsseReceivedIn ↔
      RelationAccompaniesEsse h O EsseReceivedIn

/-- On the relational sense, given accompaniment, correlativity of receiving
and giving is equivalent to weak concurrent actualization, for every history,
giving relation, origin relation and reception predicate. -/
def RelationalReadingIsTheCrux : Prop :=
  ∀ (W B T P : Type) (h : History W B T) (G : BeingGiving W B T)
    (O : OriginRelation W B T) (EsseReceivedIn : B → P → Prop),
    RelationAccompaniesEsse h O EsseReceivedIn →
      (ReceivingIsCorrelativeWithGiving G (relationalReceipt h O EsseReceivedIn) ↔
        ConcurrentlyActualized h G EsseReceivedIn)

/-- Some founded, accompanying origin relation whose term gives exists iff weak
concurrent actualization holds, for every history, giving relation and
reception predicate. -/
def SomeRelationCarriesTheCrux : Prop :=
  ∀ (W B T P : Type) (h : History W B T) (G : BeingGiving W B T)
    (EsseReceivedIn : B → P → Prop),
    (∃ O : OriginRelation W B T, FoundedOnReceivedEsse h O EsseReceivedIn ∧
      RelationAccompaniesEsse h O EsseReceivedIn ∧ TermGives G O) ↔
    ConcurrentlyActualized h G EsseReceivedIn

/-- Foundation, irreflexivity, non-mutuality, accompaniment and coexistence of
the term, even with received onset given, do not entail weak concurrent
actualization: it is not the case that they do for every history, giving
relation, origin relation and reception predicate over a preordered time. -/
def CoexistentTermDoesNotCarryTheCrux : Prop :=
  ¬ ∀ (W B T P : Type) [Preorder T] (h : History W B T) (G : BeingGiving W B T)
    (O : OriginRelation W B T) (EsseReceivedIn : B → P → Prop),
    FoundedOnReceivedEsse h O EsseReceivedIn → Irreflexive O → NonMutual O →
    RelationAccompaniesEsse h O EsseReceivedIn →
    TermCoexists h O → ReceivedOnsetIsGiven h G EsseReceivedIn →
    ConcurrentlyActualized h G EsseReceivedIn

namespace Control

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control

/-- `false` bears the origin relation to `true` at every moment from time `1`
on. -/
def persistingOrigin : OriginRelation Unit Bool Nat :=
  ⟨fun _ x g t => x = false ∧ g = true ∧ 1 ≤ t⟩

/-- `false` bears the origin relation to `true` at time `1` only. -/
def onsetOrigin : OriginRelation Unit Bool Nat :=
  ⟨fun _ x g t => x = false ∧ g = true ∧ t = 1⟩

/-- Controls on one world, natural-number times, `false` alone with received
esse; histories and givings from `SustainingCausation.Control`.
(1) Creator present throughout, giving at onset only (`sustained`, where
`true` is always present and `false` from time `1`; `inertiaGiving`, `true`
gives `false` being at time `1` only), persisting relation: foundation,
irreflexivity, non-mutuality, accompaniment, coexistence of the term, received
onset given and the present-tense reading on RECEIVES_ESSE_AT_3 hold; giving by
the term, correlativity on RECEIVES_ESSE_AT_3 and `40a97664` fail.
(2) Same history and giving, relation at onset only (an analyst variant):
foundation, coexistence of the term, giving by the term and correlativity on
RECEIVES_ESSE_AT_3 hold; accompaniment, the present-tense reading on
RECEIVES_ESSE_AT_3 and `40a97664` fail.
(3) Term absent after onset (`inertia`, `true` present up to time `1` only),
persisting relation: foundation and accompaniment hold; coexistence of the
term fails.
(4) Sustaining (`sustained`, `sustainedGiving`), persisting relation: every
premise, correlativity on RECEIVES_ESSE_AT_3 and `40a97664` hold.
(5) Same history, `false` giving itself being from time `1` on
(`selfGiving`), persisting relation to `true`: `40a97664` holds and giving by
the term fails, so for a fixed relation `40a97664` does not entail giving by
the term. -/
def Certificate : Prop :=
  (FoundedOnReceivedEsse sustained persistingOrigin falseReceived ∧
    Irreflexive persistingOrigin ∧ NonMutual persistingOrigin ∧
    RelationAccompaniesEsse sustained persistingOrigin falseReceived ∧
    TermCoexists sustained persistingOrigin ∧
    ReceivedOnsetIsGiven sustained inertiaGiving falseReceived ∧
    ReceptionIsPresent sustained (relationalReceipt sustained persistingOrigin falseReceived)
      falseReceived ∧
    ¬ TermGives inertiaGiving persistingOrigin ∧
    ¬ ReceivingIsCorrelativeWithGiving inertiaGiving
      (relationalReceipt sustained persistingOrigin falseReceived) ∧
    ¬ ConcurrentlyActualized sustained inertiaGiving falseReceived) ∧
  (FoundedOnReceivedEsse sustained onsetOrigin falseReceived ∧
    TermCoexists sustained onsetOrigin ∧
    TermGives inertiaGiving onsetOrigin ∧
    ReceivingIsCorrelativeWithGiving inertiaGiving
      (relationalReceipt sustained onsetOrigin falseReceived) ∧
    ¬ RelationAccompaniesEsse sustained onsetOrigin falseReceived ∧
    ¬ ReceptionIsPresent sustained (relationalReceipt sustained onsetOrigin falseReceived)
      falseReceived ∧
    ¬ ConcurrentlyActualized sustained inertiaGiving falseReceived) ∧
  (FoundedOnReceivedEsse inertia persistingOrigin falseReceived ∧
    RelationAccompaniesEsse inertia persistingOrigin falseReceived ∧
    ¬ TermCoexists inertia persistingOrigin) ∧
  (FoundedOnReceivedEsse sustained persistingOrigin falseReceived ∧
    RelationAccompaniesEsse sustained persistingOrigin falseReceived ∧
    TermCoexists sustained persistingOrigin ∧
    TermGives sustainedGiving persistingOrigin ∧
    ReceivingIsCorrelativeWithGiving sustainedGiving
      (relationalReceipt sustained persistingOrigin falseReceived) ∧
    ConcurrentlyActualized sustained sustainedGiving falseReceived) ∧
  (ConcurrentlyActualized sustained selfGiving falseReceived ∧
    ¬ TermGives selfGiving persistingOrigin)

end Control

end TruthCore.Causality.RelationalReceipt
