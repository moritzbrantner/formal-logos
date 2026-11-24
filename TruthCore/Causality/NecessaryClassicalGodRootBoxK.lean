module

public import TruthCore.Causality.NecessarySenseFork

/-!
# The classical-God root and the box K node of the sense fork (#1926, phase 0)

Analyst formulation, attribution deferred. `NecessaryClassicalGodRootAt`
(STMT-NECESSARY-CLASSICAL-GOD-ROOT) and `NecessaryRootBoxK`
(STMT-NECESSARY-ROOT-BOX-K) are stated over the SAME `Signature`, the SAME
`Profile W σ.Being` and the SAME world `w`. The necessity clause of the first
is `NecessaryAt m.ontic w n`, which is the box-existence of the second by
`necessaryAt_iff_boxExistsAt` (`Iff.rfl`), over the same frame `m.ontic.frame`.
So the box K node is a structural projection of the classical-God root; the
projection is proved in `TruthCore.Results.Causality.NecessaryClassicalGodRootBoxK`.

This module only adds the strictness control of that projection: a two-point
model in which the box K node holds and the classical-God root fails only
through selected-root uniqueness, with no supplied predicate emptied so that an
attribute fails, plus a restored-relation control with non-empty orders,
causation, potency, composition and matter/form. The models are statements
about this formal interpretation only.
-/

@[expose] public section

namespace TruthCore.Causality.NecessaryClassicalGodRootBoxK
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

namespace Separation

/-- A two-point signature: of the beings `false` and `true`, only `true` is
GOD_4; both have the primitive classical-attributes field. The historical and
creedal fields are unused placeholders. No source reading. -/
def pairSignature : Signature where
  Being := Bool
  IsGod := fun b => b = true
  HasClassicalAttributes := fun _ => True
  RevealsRecognizably := fun _ => False
  jesus := false
  ClaimedDivineAuthority := fun _ => False
  RoseFromTheDead := fun _ => False
  Society := Unit
  catholicChurch := ()
  Founded := fun _ _ => False
  VisibleWithAuthority := fun _ => False
  FoundedAsTeachingAuthority := fun _ _ => False
  DefinitivelyProposesAsRevealed := fun _ _ => False
  creedOneGodFatherAlmightyCreator := False
  creedOneLordJesusChristOnlyBegottenConsubstantial := False
  creedIncarnateOfSpiritAndVirginMary := False
  creedCrucifiedUnderPilateSufferedBuried := False
  creedRoseOnTheThirdDay := False
  creedAscendedSeatedAtRightHand := False
  creedWillComeToJudgeKingdomWithoutEnd := False
  creedHolySpiritLordGiverOfLife := False
  creedOneHolyCatholicApostolicChurch := False
  creedOneBaptismForForgiveness := False
  creedResurrectionOfTheDead := False
  creedLifeOfTheWorldToCome := False

/-- One world accessing itself; both beings exist there and are concrete, and
nothing grounds anything. So both are actual roots. -/
def pairProfile : Profile Unit pairSignature.Being where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- A q.3 a.4 profile on the two-point model: every being is in act in the one
respect, every being causes every being in it (`CausesIn` is a relation
distinct from `grounds`; no bridge between them is assumed), and represented
esse and essence coincide. No source reading. -/
def pairQ3Profile : PrimaPars.Question3.Article4.Profile Bool Unit Unit where
  InAct := fun _ _ => True
  CausesIn := fun _ _ _ => True
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  essentialPrinciplesAloneSufficeForEsse := fun _ => True
  esse := ()

/-- The classical-God root on the two-point model, with `GoodIn`, `Infinite`,
`Eternal`, `HasIntellect` and `HasWill` everywhere true and `InPotency`,
`MoreIn`, `PriorSimply`, `ComponentOf`, `Composite` and `MatterForm` empty,
so that goodness, infinity, eternity, intellect, will, immutability, maximum,
firstness, remoteness, simplicity and matter/form exclusion all hold. -/
def PairClassicalRoot : Prop :=
  NecessaryClassicalGodRootAt pairSignature pairProfile () pairQ3Profile
    (fun _ _ => True) (fun _ _ => False) (fun _ _ _ => False) (fun _ _ => False)
    (fun _ _ => False) (fun _ => False) (fun _ => False) (fun _ => True) (fun _ => True)
    (fun _ => True) (fun _ => True)

/-- Every conjunct of the body of `PairClassicalRoot` at `n`, except the
selected-root uniqueness conjunct of `PerfectRootAt`
(`∀ x, ActualRoot pairProfile () x → x = n`). -/
def PairBodyExceptRootUniqueness (n : Bool) : Prop :=
  ActualRoot pairProfile () n ∧ NecessaryAt pairProfile.ontic () n ∧
    IsMaximumIn pairQ3Profile.InAct (fun (_ : Unit) (_ _ : Bool) => False) pairQ3Profile.esse n ∧
    IsPerfect pairQ3Profile.InAct n ∧
    pairQ3Profile.esseOf n = pairQ3Profile.essenceOf n ∧ IsFirstBeing (fun _ _ => False) n ∧
    ¬ (fun _ => False : Bool → Prop) n ∧ RemoteFromAll (fun _ _ => False) n ∧
    pairSignature.IsGod n ∧
    NineClassicalAttributes (IsSimple (fun _ => False)) (IsPerfect pairQ3Profile.InAct)
      (IsSupremelyGood pairQ3Profile.InAct (fun _ _ => True) pairQ3Profile.CausesIn
        pairQ3Profile.esse) (IsTheOneGod pairSignature.IsGod)
      (fun _ => True) (IsImmutable (fun (_ : Bool) (_ : Unit) => False)) (fun _ => True) (fun _ => True)
      (fun _ => True) n ∧
    pairSignature.HasClassicalAttributes n

/-- The q.3 a.4 profile of the restored-relation control: as `pairQ3Profile`,
except that `CausesIn` runs only from `true` to `false`. -/
def restoredQ3Profile : PrimaPars.Question3.Article4.Profile Bool Unit Unit where
  InAct := fun _ _ => True
  CausesIn := fun a b _ => a = true ∧ b = false
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  essentialPrinciplesAloneSufficeForEsse := fun _ => True
  esse := ()

/-- The more-than relation of the restored control: `true` is more than `false`
in every respect (here the one respect, esse), and nothing else. -/
def restoredMoreIn : Unit → Bool → Bool → Prop := fun _ a b => a = true ∧ b = false

/-- Simple priority of the restored control: `true` is simply prior to `false`,
and nothing else. -/
def restoredPriorSimply : Bool → Bool → Prop := fun a b => a = true ∧ b = false

/-- Potency, composition and matter/form of the restored control: only `false`
is in potency (in the one respect), composite and composed of matter and form. -/
def restoredInPotency : Bool → Unit → Prop := fun b _ => b = false
def restoredComposite : Bool → Prop := fun b => b = false
def restoredMatterForm : Bool → Prop := fun b => b = false

/-- The classical-God root on the same two-point signature and Profile, with
restored, non-empty relations: `MoreIn`, `PriorSimply`, `CausesIn`,
`InPotency`, `Composite` and `MatterForm` as above, `ComponentOf` still empty,
and `GoodIn`, `Infinite`, `Eternal`, `HasIntellect`, `HasWill` everywhere true. -/
def RestoredClassicalRoot : Prop :=
  NecessaryClassicalGodRootAt pairSignature pairProfile () restoredQ3Profile
    (fun _ _ => True) restoredInPotency restoredMoreIn restoredPriorSimply
    (fun _ _ => False) restoredComposite restoredMatterForm (fun _ => True) (fun _ => True)
    (fun _ => True) (fun _ => True)

/-- Every conjunct of the body of `RestoredClassicalRoot` at `n`, except the
selected-root uniqueness conjunct of `PerfectRootAt`. -/
def RestoredBodyExceptRootUniqueness (n : Bool) : Prop :=
  ActualRoot pairProfile () n ∧ NecessaryAt pairProfile.ontic () n ∧
    IsMaximumIn restoredQ3Profile.InAct restoredMoreIn restoredQ3Profile.esse n ∧
    IsPerfect restoredQ3Profile.InAct n ∧
    restoredQ3Profile.esseOf n = restoredQ3Profile.essenceOf n ∧
    IsFirstBeing restoredPriorSimply n ∧
    ¬ restoredMatterForm n ∧ RemoteFromAll (fun _ _ => False) n ∧
    pairSignature.IsGod n ∧
    NineClassicalAttributes (IsSimple restoredComposite) (IsPerfect restoredQ3Profile.InAct)
      (IsSupremelyGood restoredQ3Profile.InAct (fun _ _ => True) restoredQ3Profile.CausesIn
        restoredQ3Profile.esse) (IsTheOneGod pairSignature.IsGod)
      (fun _ => True) (IsImmutable restoredInPotency) (fun _ => True) (fun _ => True)
      (fun _ => True) n ∧
    pairSignature.HasClassicalAttributes n

/-- Strictness control of the projection (formal interpretation only), on a
two-point model where both beings are actual roots (concrete, existing at the
one self-accessing world, grounded by nothing) and only `true` is GOD_4:

1. the box K node holds (witness `true`: it box-exists, is an actual root, is
   GOD_4, is the one GOD_4 and has the classical-attributes field);
2. the classical-God root fails;
3. the classical root's body is exactly "the body without selected-root
   uniqueness, plus selected-root uniqueness" on this model;
4. the body without selected-root uniqueness holds at `true`;
5. `false` is a second actual root that is not GOD_4.

So the failure comes from one conjunct only: selected-root uniqueness
(`∀ x, ActualRoot m w x → x = n`, inside `PerfectRootAt`), which no witness
meets because there are two actual roots. The box K node asks only that its
witness be the one GOD_4 (`IsTheOneGod`), which does not exclude a second,
non-God actual root. No supplied predicate is emptied so that an attribute
fails. In the main model six supplied relations are empty (`InPotency`,
`MoreIn`, `PriorSimply`, `ComponentOf`, `Composite`, `MatterForm`), so
immutability, maximum, firstness, remoteness, simplicity and matter/form
exclusion hold vacuously at both beings, and `CausesIn` is total.

6. The restored-relation control (`RestoredClassicalRoot`, same signature and
   Profile, so the box K node of item 1 still holds) makes all of these
   relations non-empty except `ComponentOf`: `true` is more in esse than
   `false` and simply prior to it, `CausesIn` runs only from `true` to `false`,
   and only `false` is in potency, composite and composed of matter and form.
   The root still fails, it is again exactly "body without uniqueness, plus
   uniqueness", that body holds at `true`, and maximum and firstness fail at
   `false`. So the separation does not rest on the vacuous clauses; only
   remoteness stays vacuous there.

The other content the classical root adds over the box K node (maximum,
perfection, firstness, esse/essence identity, matter/form exclusion,
remoteness and eight of the nine case predicates other than `IsTheOneGod`) is
a syntactic difference between the two definitions; neither model separates
the nodes on any of it. -/
def Separator : Prop :=
  NecessaryRootBoxK pairSignature pairProfile () (fun _ _ => False) ∧
    ¬ PairClassicalRoot ∧
    (PairClassicalRoot ↔ ∃ n, PairBodyExceptRootUniqueness n ∧
      ∀ x, ActualRoot pairProfile () x → x = n) ∧
    PairBodyExceptRootUniqueness true ∧
    ActualRoot pairProfile () false ∧ ¬ pairSignature.IsGod false ∧
    ¬ RestoredClassicalRoot ∧
    (RestoredClassicalRoot ↔ ∃ n, RestoredBodyExceptRootUniqueness n ∧
      ∀ x, ActualRoot pairProfile () x → x = n) ∧
    RestoredBodyExceptRootUniqueness true ∧
    ¬ IsMaximumIn restoredQ3Profile.InAct restoredMoreIn restoredQ3Profile.esse false ∧
    ¬ IsFirstBeing restoredPriorSimply false

end Separation
end TruthCore.Causality.NecessaryClassicalGodRootBoxK
