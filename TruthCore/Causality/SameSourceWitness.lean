module

public import TruthCore.Latin.Aquinas.DeEnte.RootInterface
public import TruthCore.Causality.NecessaryConcreteUnderived
public import TruthCore.Causality.NecessaryClassicalGodRoot

/-!
# One witness: the De ente source, the underived concretum and the classical root (#1731)

Pointwise bodies of three existing existential endpoints, so that a theorem
can state that ONE being satisfies two of them. Each `…At` body below is the
body of the existing existential definition named in its comment; the
`…_iff` lemmas check that by `Iff.rfl`, so no meaning is changed.

All endpoints share ONE carrier `B` (`σ.Being` for the classical root), one
grounding profile `m`, world `w` and one q.3 a.4 profile `p`. Nothing here
equates `Ontic.Causes`, an unrelated profile exemplar, or the q.3 causal
relation with `m.grounds`; the De ente bridges that relate them stay the
explicit inputs of `RootInterface.deEnteFirstSourceIsActualRoot`.
-/

@[expose] public section

namespace TruthCore.Causality.SameSourceWitness

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.DirectEsseRootPerfectionGoodness (PerfectRootAt)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause DeEnteFirstSourceIsActualRootAt)
open TruthCore.Causality.NecessaryConcreteUnderived (NecessaryConcreteUnderivedAt)
open TruthCore.Causality.NecessaryClassicalGodRoot (NecessaryClassicalGodRootAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- Body of `DeEnteFirstSourceIsActualRootAt` at `n`: an actual concrete root
of the selected grounding at `w`, in act, esse equal to essence, with no
distinct actual cause of its esse and a finite actual esse-cause path to every
other being in act. -/
def DeEnteSourceAt {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R) (n : B) : Prop :=
  ActualRoot m w n ∧ p.InAct n p.esse ∧ p.esseOf n = p.essenceOf n ∧
    (∀ c, ¬ ActualEsseCause p c n) ∧
    ∀ x, p.InAct x p.esse → x ≠ n → Relation.TransGen (ActualEsseCause p) n x

theorem deEnteFirstSource_iff {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R) :
    DeEnteFirstSourceIsActualRootAt m w p ↔ ∃ n, DeEnteSourceAt m w p n := Iff.rfl

/-- Body of `NecessaryConcreteUnderivedAt` at `b`: concrete, existing at `w`,
existing at every accessible world, and with no selected ground from an
existing concrete candidate at ANY world. -/
def UnderivedConcreteAt {W B : Type} (m : Profile W B) (w : W) (b : B) : Prop :=
  m.concrete b ∧ m.ontic.ExistsAt w b ∧ NecessaryAt m.ontic w b ∧
    ∀ v a, m.concrete a → m.ontic.ExistsAt v a → ¬ m.grounds v a b

theorem underived_iff {W B : Type} (m : Profile W B) (w : W) :
    NecessaryConcreteUnderivedAt m w ↔ ∃ b, UnderivedConcreteAt m w b := Iff.rfl

/-- Body of `NecessaryClassicalGodRootAt` at `n`: the selected perfect actual
root with the classical companions, GOD_4 naming, the nine case predicates and
the primitive signature field. -/
def ClassicalGodRootWitnessAt {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (n : σ.Being) : Prop :=
  PerfectRootAt m w p.InAct MoreIn p.esse n ∧
    p.esseOf n = p.essenceOf n ∧ IsFirstBeing PriorSimply n ∧
    ¬ MatterForm n ∧ RemoteFromAll ComponentOf n ∧ σ.IsGod n ∧
    NineClassicalAttributes (IsSimple Composite) (IsPerfect p.InAct)
      (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill n ∧
    σ.HasClassicalAttributes n

theorem classicalGodRoot_iff {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop) :
    NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
        Composite MatterForm Infinite Eternal HasIntellect HasWill ↔
      ∃ n, ClassicalGodRootWitnessAt σ m w p GoodIn InPotency MoreIn PriorSimply
        ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill n := Iff.rfl

/-- ONE being is both the De ente first source (actual root at `w`) and a
necessary concrete underived candidate of the same `m`, `w`. -/
def DeEnteSourceIsUnderivedAt {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R) : Prop :=
  ∃ n, DeEnteSourceAt m w p n ∧ UnderivedConcreteAt m w n

/-- ONE being is both the De ente first source and the classical God root of
the same carrier, `m`, `w` and `p`. GOD_4 naming, not historical identity. -/
def DeEnteSourceIsClassicalGodRootAt {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop) : Prop :=
  ∃ n, DeEnteSourceAt m w p n ∧
    ClassicalGodRootWitnessAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill n

/-- ONE being is the De ente first source (actual root at `w` of `m`), is a
first being in the `PriorSimply` order, and is GOD_4 under the supplied
naming predicate `IsGod`. No necessity, uniqueness of all necessary
individuals or classical attribute is asserted. -/
def DeEnteSourceIsGodAt {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply : B → B → Prop) (IsGod : B → Prop) : Prop :=
  ∃ n, DeEnteSourceAt m w p n ∧ IsFirstBeing PriorSimply n ∧ IsGod n

end TruthCore.Causality.SameSourceWitness
