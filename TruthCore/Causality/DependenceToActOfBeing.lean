module

public import TruthCore.Causality.ModeOfBeingMiddleTerm
public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Causality.EsseReception

/-!
# The "unde" inference: from dependence on being to the act of being

Analyst formulations, attribution deferred except where a doc comment quotes a
read passage. This module formalizes the inference of ST I q.4 a.1 ad 3,
read in full in the pinned SCTA witness:

> ipsum esse est perfectissimum omnium: comparatur enim ad omnia ut actus.
> Nihil enim habet actualitatem, nisi inquantum est: **unde** ipsum esse est
> actualitas omnium rerum, et etiam ipsarum formarum. **Unde** non comparatur
> ad alia sicut recipiens ad receptum: sed magis sicut receptum ad recipiens.
> Cum enim dico esse hominis, vel equi, vel cuiuscumque alterius, ipsum esse
> consideratur ut formale et receptum: non autem ut illud cui competit esse.

It answers objection 3 ("ipsum esse videtur esse imperfectissimum: cum sit
communissimum, et recipiens omnium additiones"). The parallel second proof of
q.3 a.4 co. reads: "esse est actualitas omnis formae vel naturae: non enim
bonitas vel humanitas significatur in actu, nisi prout significamus eam esse.
Oportet igitur quod ipsum esse comparetur ad essentiam quae est aliud ab ipso,
sicut actus ad potentiam."

Start: R-dep, `ActualityOnlyInsofarAsBeingReading F.InAct F.esse` (`7067553d`).
Targets: R-act₁ `FiniteEsseReceivedAndLimited` (`8c64b036`) and R-act₂
`IntensiveEsse` (`254ee26f`). The steps:

* first "unde", `DependenceIsActualization`: what every actuality of a thing
  depends on is the act through which it is actual;
* second "unde", with q.3 a.4's "oportet igitur",
  `ActualizedQuiddityReceivesEsse`: a nature actual through an esse other than
  itself receives that esse as potency receives act;
* `QuiddityInAct`: each being in the domain has its nature in act;
* the existing `ReceptionLimitation.ReceivedEsseIsLimited` (`7de89edb`);
* for R-act₂, `PurePerfectionsActualSomewhere` and
  `ActualizedPureIsOfEsse`.

`ActualizationFrame.ActualizedBy` is ACTUALIZATION_2, a primitive with the act
reading ("r is actual in x through the act a"). `DeflatedActualizedBy` is
ACTUALIZATION_1, the dependence reading. Respect identity in `GradesFrame`
is identity of content (humanity is not being), which every view considered
grants (De ente c.3's "possum enim intelligere quid est homo vel Phoenix et
tamen ignorare an esse habeat in rerum natura"). It is not real distinction. -/

@[expose] public section

namespace TruthCore.Causality.DependenceToActOfBeing

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.ModeOfBeingMiddleTerm
  (FiniteEsseReceivedAndLimited IntensiveEsseFrame IntensiveEsse)
open TruthCore.Latin.Aquinas.SummaTheologiae (ActualityOnlyInsofarAsBeingReading)

variable {W B T R : Type}

/-- The extra structure the inference needs on a `GradesFrame`. -/
structure ActualizationFrame (B R : Type) where
  /-- `quiddity x`: the nature of `x`, as the respect in which `x` is actually
  what it is ("humanitas ... in actu", q.3 a.4). -/
  quiddity : B → R
  /-- ACTUALIZATION_2, explicitly primitive: in `x`, the respect `r` is actual
  through the act `a` ("ipsum esse est actualitas ... ipsarum formarum"). Not
  the dependence relation `DeflatedActualizedBy`; no law relates the two. -/
  ActualizedBy : B → R → R → Prop

/-- "Cuius quiditas est ipsum suum esse" (De ente c.3): the nature of `x` is
being itself, *esse tantum*. Read with the frame's content identity, so a
creature whose existence is really identical with its essence (Suárez) is not
thereby its own being in this sense. -/
def OwnBeingByQuiddity (F : GradesFrame W B T R) (A : ActualizationFrame B R)
    (x : B) : Prop :=
  A.quiddity x = F.esse

/-- ACTUALIZATION_1, the dependence reading: `r` is actual in `x` "through" `a`
when `x` has both in act. -/
def DeflatedActualizedBy (F : GradesFrame W B T R) (x : B) (r a : R) : Prop :=
  F.InAct x r ∧ F.InAct x a

/-- The first "unde" as a bridge: whatever a thing has in act, given that it
has being, is actual in it through esse. -/
def DependenceIsActualization (F : GradesFrame W B T R)
    (A : ActualizationFrame B R) : Prop :=
  ∀ x r, F.InAct x r → F.InAct x F.esse → A.ActualizedBy x r F.esse

/-- What the first "unde" concludes: esse is the actuality of every form had
in act ("actualitas omnium rerum, et etiam ipsarum formarum"). -/
def EsseIsActualityOfEveryForm (F : GradesFrame W B T R)
    (A : ActualizationFrame B R) : Prop :=
  ∀ x r, F.InAct x r → A.ActualizedBy x r F.esse

/-- The second "unde" with q.3 a.4's "oportet igitur", in its weakest form, at
the nature: a nature that is actual through an esse other than itself receives
that esse as potency receives act (RECEPTION_OF_ESSE_1). -/
def ActualizedQuiddityReceivesEsse (F : GradesFrame W B T R)
    (A : ActualizationFrame B R) (EsseReceivedIn : B → R → Prop) : Prop :=
  ∀ x, A.ActualizedBy x (A.quiddity x) F.esse → A.quiddity x ≠ F.esse →
    EsseReceivedIn x (A.quiddity x)

/-- Every being in the domain has its nature in act. The domain is actual
beings. -/
def QuiddityInAct (F : GradesFrame W B T R) (A : ActualizationFrame B R) : Prop :=
  ∀ x, F.InAct x (A.quiddity x)

/-- The reception half of R-act₁, at the nature. -/
def QuiddityReceivesEsse (F : GradesFrame W B T R) (A : ActualizationFrame B R)
    (EsseReceivedIn : B → R → Prop) : Prop :=
  ∀ x, ¬ OwnBeingByQuiddity F A x → EsseReceivedIn x (A.quiddity x)

/-- Every pure perfection is had in act by something. -/
def PurePerfectionsActualSomewhere (F : GradesFrame W B T R) (Pure : R → Prop) :
    Prop :=
  ∀ d, Pure d → ∃ x, F.InAct x d

/-- Inclusion: a pure perfection actual through esse is a perfection of esse
itself (PERFECTION_OF_BEING_2). -/
def ActualizedPureIsOfEsse (F : GradesFrame W B T R) (A : ActualizationFrame B R)
    (I : IntensiveEsseFrame R) (Pure : R → Prop) : Prop :=
  ∀ x d, A.ActualizedBy x d F.esse → Pure d → I.OfEsse d

/-- q.7 a.2 ad 1, "contra rationem facti, quod essentia rei sit ipsum esse
eius": no creature is its own being. -/
def NoCreatureIsOwnBeing (Creature OwnBeing : B → Prop) : Prop :=
  ∀ x, Creature x → ¬ OwnBeing x

/-! ## Limitation at matching scope

The explanandum shared by every view: a being whose nature is not being itself
lacks some pure perfection. -/

/-- The capacity of a nature, explicitly primitive. -/
structure CapacityFrame (R : Type) where
  /-- `Admits n d`: the nature `n` admits the perfection `d` (the nature's
  capacity, "capacitas naturae recipientis", De ente c.4). -/
  Admits : R → R → Prop

/-- Essence-only account: a being has in act only what its nature admits. -/
def HasOnlyWhatNatureAdmits (F : GradesFrame W B T R) (A : ActualizationFrame B R)
    (C : CapacityFrame R) : Prop :=
  ∀ x d, F.InAct x d → C.Admits (A.quiddity x) d

/-- Reception account, De ente c.4 "limitatum ... ad capacitatem naturae
recipientis": what has its esse received in its nature has in act only what
that nature admits. -/
def ReceivedEsseOnlyToCapacity (F : GradesFrame W B T R) (A : ActualizationFrame B R)
    (C : CapacityFrame R) (EsseReceivedIn : B → R → Prop) : Prop :=
  ∀ x d, EsseReceivedIn x (A.quiddity x) → F.InAct x d → C.Admits (A.quiddity x) d

/-- Shared by both accounts: a nature other than being itself excludes some
pure perfection. -/
def NatureOtherThanBeingExcludesSomePure (F : GradesFrame W B T R)
    (A : ActualizationFrame B R) (C : CapacityFrame R) (Pure : R → Prop) : Prop :=
  ∀ x, A.quiddity x ≠ F.esse → ∃ d, Pure d ∧ ¬ C.Admits (A.quiddity x) d

/-- The explanandum, finitude in perfection: what is not its own being lacks
some pure perfection. -/
def FiniteInPerfection (F : GradesFrame W B T R) (A : ActualizationFrame B R)
    (Pure : R → Prop) : Prop :=
  ∀ x, ¬ OwnBeingByQuiddity F A x → ∃ d, Pure d ∧ ¬ F.InAct x d

/-! ## The load map and the comparison, as universal statements -/

/-- Given R-dep, each "unde" bridge is equivalent to what it delivers. Read as
dependence (ACTUALIZATION_1), the first bridge holds in every frame. -/
def UndeLoadMap : Prop :=
  ∀ (W B T R : Type) (F : GradesFrame W B T R) (A : ActualizationFrame B R)
    (EsseReceivedIn : B → R → Prop) (I : IntensiveEsseFrame R) (Pure : R → Prop),
    (ActualityOnlyInsofarAsBeingReading F.InAct F.esse →
      (DependenceIsActualization F A ↔ EsseIsActualityOfEveryForm F A)) ∧
    (ActualityOnlyInsofarAsBeingReading F.InAct F.esse →
      DependenceIsActualization F A → QuiddityInAct F A →
      (ActualizedQuiddityReceivesEsse F A EsseReceivedIn ↔
        QuiddityReceivesEsse F A EsseReceivedIn)) ∧
    (ActualityOnlyInsofarAsBeingReading F.InAct F.esse →
      DependenceIsActualization F A → PurePerfectionsActualSomewhere F Pure →
      (ActualizedPureIsOfEsse F A I Pure ↔ IntensiveEsse I Pure)) ∧
    DependenceIsActualization F ⟨A.quiddity, DeflatedActualizedBy F⟩

/-- Both accounts of finitude need the same nature premise, and reception adds
nothing to the derivation: the reception account implies the essence-only
account on every being that is not its own being. -/
def LimitationComparison : Prop :=
  ∀ (W B T R : Type) (F : GradesFrame W B T R) (A : ActualizationFrame B R)
    (C : CapacityFrame R) (EsseReceivedIn : B → R → Prop) (Pure : R → Prop),
    (HasOnlyWhatNatureAdmits F A C →
      NatureOtherThanBeingExcludesSomePure F A C Pure →
      FiniteInPerfection F A Pure) ∧
    (QuiddityReceivesEsse F A EsseReceivedIn →
      ReceivedEsseOnlyToCapacity F A C EsseReceivedIn →
      NatureOtherThanBeingExcludesSomePure F A C Pure →
      FiniteInPerfection F A Pure) ∧
    (QuiddityReceivesEsse F A EsseReceivedIn →
      ReceivedEsseOnlyToCapacity F A C EsseReceivedIn →
      ∀ x, ¬ OwnBeingByQuiddity F A x → ∀ d, F.InAct x d → C.Admits (A.quiddity x) d)

/-! ## The q.7 a.1 bridge

The candidate bridge from reception toward intensive esse (ST I q.7 a.1 co.,
"infinitum secundum quod se tenet ex parte formae non determinatae per materiam,
habet rationem perfecti. Illud autem quod est maxime formale omnium, est ipsum
esse"): unreceived esse is unlimited, so it includes every pure perfection. It runs
through own being as no recipient (`7338142d`), limitation only through reception
(`1304b462`) and unlimited esse having every pure perfection. -/

/-- Unlimited esse has every pure perfection: a being whose esse is not limited
really has every pure perfection (`Has`, real determinations). -/
def UnlimitedEsseHasEveryPure {D : Type} (EsseLimited : B → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) : Prop :=
  ∀ x, ¬ EsseLimited x → ∀ d, Pure d → Has x d

/-- The measure reading of limited esse, defined: `x`'s esse is limited when `x`
lacks some pure perfection (finite in formal perfection). -/
def LimitedByMeasure {D : Type} (Has : B → D → Prop) (Pure : D → Prop) (x : B) : Prop :=
  ∃ d, Pure d ∧ ¬ Has x d

/-- The q.7 a.1 bridge gives the locus-(b) composite without `d164b1ff` and
`c4fb87a6`; on the measure reading of limitation its third premise is analytic, so
the content moves to `1304b462`. -/
def Q7BridgeLoadMap : Prop :=
  ∀ (B P D : Type) (OwnBeing : B → Prop) (EsseReceivedIn : B → P → Prop)
    (EsseLimited : B → Prop) (Has : B → D → Prop) (Pure : D → Prop),
    (ReceptionLimitation.OwnBeingIsNoRecipient OwnBeing (fun x => ∃ r, EsseReceivedIn x r) →
      TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading
        EsseLimited EsseReceivedIn →
      UnlimitedEsseHasEveryPure EsseLimited Has Pure →
      TruthCore.Causality.ModeOfBeingMiddleTerm.OwnBeingHasEveryPurePerfection OwnBeing Has Pure) ∧
    UnlimitedEsseHasEveryPure (LimitedByMeasure Has Pure) Has Pure

/-! ## Controls -/

namespace Control

/-- A grades frame on two beings and three respects: `0` being, `1` a nature
(humanity, say), `2` a pure perfection (wisdom, say). Stand-ins only. -/
def gframe (InAct : Bool → Fin 3 → Prop) : GradesFrame Unit Bool Unit (Fin 3) where
  history :=
    { ontic := ⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩
      IsAt := fun _ _ _ => True
      now := () }
  GivesAt := fun _ _ _ _ => False
  CausesIn := fun _ _ _ => False
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := 0
  InAct := InAct
  MoreIn := fun _ _ _ => False

/-- World 1: both beings have being and the nature, neither has wisdom. -/
def act1 (_ : Bool) (r : Fin 3) : Prop := r ≠ 2

/-- World 2: as world 1, and `true` also has wisdom. -/
def act2 (x : Bool) (r : Fin 3) : Prop := r ≠ 2 ∨ x = true

/-- World 3: both beings have everything. -/
def act3 (_ : Bool) (_ : Fin 3) : Prop := True

/-- The nature of each being is respect `1`. -/
def nature (_ : Bool) : Fin 3 := 1

/-- The act-of-being reading: what a being has is actual in it through being. -/
def thomist (InAct : Bool → Fin 3 → Prop) : ActualizationFrame Bool (Fin 3) :=
  ⟨nature, fun x r a => InAct x r ∧ a = 0⟩

/-- No actualization recorded. -/
def idle : ActualizationFrame Bool (Fin 3) := ⟨nature, fun _ _ _ => False⟩

/-- Esse received in the nature, and limited. -/
def received (_ : Bool) (r : Fin 3) : Prop := r = 1
def limited (_ : Bool) : Prop := True

/-- No reception, no limitation recorded. -/
def noReceived (_ : Bool) (_ : Fin 3) : Prop := False
def noLimited (_ : Bool) : Prop := False

def pure (d : Fin 3) : Prop := d = 2

/-- Natures admit everything but wisdom; or everything. -/
def admitsNotWisdom : CapacityFrame (Fin 3) := ⟨fun _ d => d ≠ 2⟩
def admitsAll : CapacityFrame (Fin 3) := ⟨fun _ _ => True⟩

/-- Statements about these finite profiles only.

* **Act profile, world 1:** R-dep, both "unde" bridges, `QuiddityInAct` and
  `7de89edb` hold, and so does R-act₁.
* **Non-reception profile, world 1**, read with the act field (Suárez: esse
  is the actuality of the nature, not received in it) and with the dependence
  relation (quantifier view): R-dep, the first bridge, `QuiddityInAct` and
  `7de89edb` hold; the second bridge and R-act₁ fail. On the same profile the
  essence-only account and finitude hold.
* **Omitting the first bridge** (no actualization): R-dep, the vacuous second
  bridge, `QuiddityInAct` and `7de89edb` hold; R-act₁ fails.
* **Reception without the nature premise, world 3:** R-act₁, `7de89edb` and
  the capacity bridge hold with every nature admitting everything; finitude
  fails.
* **World 2:** R-dep, the first bridge and the witness premise hold. With
  inclusion read intensively both inclusion and R-act₂ hold; read thinly,
  inclusion and R-act₂ fail. With no actualization, inclusion holds vacuously
  and thin R-act₂ fails. -/
def Controls : Prop :=
  -- act profile, world 1
  ActualityOnlyInsofarAsBeingReading (gframe act1).InAct (gframe act1).esse ∧
  DependenceIsActualization (gframe act1) (thomist act1) ∧
  ActualizedQuiddityReceivesEsse (gframe act1) (thomist act1) received ∧
  QuiddityInAct (gframe act1) (thomist act1) ∧
  ReceptionLimitation.ReceivedEsseIsLimited limited received ∧
  FiniteEsseReceivedAndLimited (OwnBeingByQuiddity (gframe act1) (thomist act1))
    received limited ∧
  -- non-reception profile, world 1: the act field (Suárez) ...
  DependenceIsActualization (gframe act1) (thomist act1) ∧
  ¬ ActualizedQuiddityReceivesEsse (gframe act1) (thomist act1) noReceived ∧
  ReceptionLimitation.ReceivedEsseIsLimited noLimited noReceived ∧
  ¬ FiniteEsseReceivedAndLimited (OwnBeingByQuiddity (gframe act1) (thomist act1))
    noReceived noLimited ∧
  -- ... and the dependence relation (quantifier view)
  DependenceIsActualization (gframe act1) ⟨nature, DeflatedActualizedBy (gframe act1)⟩ ∧
  ¬ ActualizedQuiddityReceivesEsse (gframe act1)
    ⟨nature, DeflatedActualizedBy (gframe act1)⟩ noReceived ∧
  -- essence-only limitation on the non-reception profile
  HasOnlyWhatNatureAdmits (gframe act1) idle admitsNotWisdom ∧
  NatureOtherThanBeingExcludesSomePure (gframe act1) idle admitsNotWisdom pure ∧
  FiniteInPerfection (gframe act1) idle pure ∧
  -- omitting the first bridge
  ¬ DependenceIsActualization (gframe act1) idle ∧
  ActualizedQuiddityReceivesEsse (gframe act1) idle noReceived ∧
  QuiddityInAct (gframe act1) idle ∧
  -- reception without the nature premise, world 3
  FiniteEsseReceivedAndLimited (OwnBeingByQuiddity (gframe act3) idle) received limited ∧
  ReceivedEsseOnlyToCapacity (gframe act3) idle admitsAll received ∧
  ¬ NatureOtherThanBeingExcludesSomePure (gframe act3) idle admitsAll pure ∧
  ¬ FiniteInPerfection (gframe act3) idle pure ∧
  -- world 2, R-act₂
  ActualityOnlyInsofarAsBeingReading (gframe act2).InAct (gframe act2).esse ∧
  DependenceIsActualization (gframe act2) (thomist act2) ∧
  PurePerfectionsActualSomewhere (gframe act2) pure ∧
  ActualizedPureIsOfEsse (gframe act2) (thomist act2) ⟨fun _ => True⟩ pure ∧
  IntensiveEsse (⟨fun _ => True⟩ : IntensiveEsseFrame (Fin 3)) pure ∧
  ¬ ActualizedPureIsOfEsse (gframe act2) (thomist act2) ⟨fun d => d = 0⟩ pure ∧
  ¬ IntensiveEsse (⟨fun d => d = 0⟩ : IntensiveEsseFrame (Fin 3)) pure ∧
  ActualizedPureIsOfEsse (gframe act2) idle ⟨fun d => d = 0⟩ pure

/-! ### The q.7 a.1 bridge on a quantifier-view source

Beings: `false` a source that is its own being, `true` an effect. Determinations:
`false` being, `true` a stand-in for life; both pure. The source has only being. -/

def own (b : Bool) : Prop := b = false
def recv (b : Bool) (_ : Unit) : Prop := b = true
def hasOnlyBeing (b d : Bool) : Prop := d = false ∨ b = true
def allPure (_ : Bool) : Prop := True
/-- Role reading: only what is received is limited. -/
def limitedRole (b : Bool) : Prop := b = true

/-- Statements about this profile only. Role reading: own being is no recipient
and limitation is only through reception, but unlimited esse does not have every
pure perfection, and the source lacks life. Measure reading: unlimited esse has
every pure perfection (analytically), but the source is limited without being
received, so limitation only through reception fails. -/
def Q7Controls : Prop :=
  ReceptionLimitation.OwnBeingIsNoRecipient own (fun x => ∃ r, recv x r) ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading
    limitedRole recv ∧
  ¬ UnlimitedEsseHasEveryPure limitedRole hasOnlyBeing allPure ∧
  ¬ TruthCore.Causality.ModeOfBeingMiddleTerm.OwnBeingHasEveryPurePerfection own hasOnlyBeing allPure ∧
  UnlimitedEsseHasEveryPure (LimitedByMeasure hasOnlyBeing allPure) hasOnlyBeing allPure ∧
  ¬ TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading
    (LimitedByMeasure hasOnlyBeing allPure) recv

end Control

end TruthCore.Causality.DependenceToActOfBeing
