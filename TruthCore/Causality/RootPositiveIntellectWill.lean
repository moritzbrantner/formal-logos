module

public import TruthCore.Causality.DirectEsseRootPerfectionGoodness
public import TruthCore.Causality.ActualCommonRoot
public import TruthCore.Causality.RootIntellectWill
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause

/-! Same selected root, positive and structural attributes. This packages
conditional consequences without a God name, all-necessary-individual uniqueness,
moral perfection, cognitive adequacy or a full-nine-attribute claim. -/

@[expose] public section

namespace TruthCore.Causality.RootPositiveIntellectWill
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- ONE witness retains the existing perfect-root body and causal supreme
goodness, represented esse/essence identity, noncomposition, firstness,
matter/form exclusion, remoteness, intellect and will. Dictionary applicability
and formal-or-eminent/cognitive/causal interpretation remain OPEN. -/
def NecessaryPositiveRootIntellectWillAt {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R) (GoodIn : B → R → Prop)
    (MoreIn : R → B → B → Prop)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill : B → Prop) : Prop :=
  ∃ n, PerfectRootAt m w p.InAct MoreIn p.esse n ∧
    IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse n ∧
    p.esseOf n = p.essenceOf n ∧ IsSimple Composite n ∧
    IsFirstBeing PriorSimply n ∧ ¬ MatterForm n ∧ RemoteFromAll ComponentOf n ∧
    HasIntellect n ∧ HasWill n

/-- Existence of a root of ONE selected actual concrete grounding relation.
This is weaker than a common root, perfect root or necessary root. It makes
the witness supplied to an attribute route an explicit separate premise. -/
def ActualRootExistsAt {W B : Type} (m : Profile W B) (w : W) : Prop :=
  ∃ n, TruthCore.Causality.NecessaryRootFork.ActualRoot m w n

/-- One and the SAME selected actual concrete root is a GOD_4-named being with
intellectual CAPACITY (HAS_INTELLECT_1), and directly grounds every other
actual concretum in this relation. Neither occurring thought, modal necessity,
nor the truth of any God-naming or teleological application is built in. -/
def IntellectualGodCommonRootAt {W B : Type} (m : Profile W B) (w : W)
    (IsGod HasIntellect : B → Prop) : Prop :=
  ∃ n, TruthCore.Causality.NecessaryRootFork.ActualRoot m w n ∧
    (∀ x, TruthCore.Causality.NecessaryRootFork.ActualConcrete m w x →
      x = n ∨ TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround m w n x) ∧
    IsGod n ∧ HasIntellect n
end TruthCore.Causality.RootPositiveIntellectWill
