module

public import TruthCore.Causality.SameSourceWitness
public import TruthCore.Results.Causality.MaximalFromEsseSource.Solution

/-!
# The De ente first source is GOD_4, keeping its witness (#1731)

`MaximalFromEsseSource.sameWitnessGodAtBeing` names SOME actual root, obtained
from population and whole-roster nontrapping. Its proof works for any actual
root. Here the root is the De ente first source itself, so the GOD_4 witness
is that source, with its esse/essence identity, uncaused esse and finite
actual esse-cause paths retained. Population and whole-roster nontrapping are
not inputs: the source's own roothood supplies the root.

* `deEnteSourceIsGod`: De ente source root and the ten other inputs of the
  twelve-input existence-only consumer (all but population and whole-roster)
  give ONE being that is the source, first, and GOD_4.
* `godExistsOfDeEnteSourceIsGod`: projection to `GodExists`.

Nothing here proves an input or supplies necessity, uniqueness of necessary
individuals, or any classical attribute.
-/

@[expose] public section

namespace TruthCore.Results.Causality.DeEnteSourceGod

open TruthCore.Causality.SameSourceWitness
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.DirectEsseRootRoute
open TruthCore.Latin.Aquinas.DeEnte (DeEnteFirstSourceIsActualRootAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic (ExcludedMiddle)

/-- The De ente source n is an actual root. No actual concrete ground of n is
simply prior to it (firstness). A maximum exists (grades at `w`); any maximum
other than n would cause n's esse, hence ground n, so every maximum is n.
Then the naming chain of `sameWitnessGodAtBeing` names this SAME n GOD_4. -/
theorem deEnteSourceIsGod {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (MoreIn : R → B → B → Prop) (PriorSimply ComponentOf : B → B → Prop)
    (IsGod : B → Prop)
    (hSource : DeEnteFirstSourceIsActualRootAt m w p)
    (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hApproach : GradesByApproachToAMaximumReading p.InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse
      ComponentOf IsGod) :
    DeEnteSourceIsGodAt m w p PriorSimply IsGod := by
  obtain ⟨n, hn⟩ := hSource
  have hr : ActualRoot m w n := hn.1
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 y (hPrior y n hNe hy)).elim
  have hIdent : ∀ y, IsMaximumIn p.InAct MoreIn p.esse y → y = n := by
    intro y hy
    rcases hEM (y = n) with heq | hne
    · exact heq
    · exact (hr.2 y (hEsse y n hne hr.1
        (hGenus y hy n (fun h => hne h.symm) (hExisting n hr.1.2)))).elim
  obtain ⟨y, hy⟩ := maximumExistsOfExistingRoot m w p.InAct MoreIn p.esse n hr
    hExisting hApproach hEM
  have hnMax : IsMaximumIn p.InAct MoreIn p.esse n := (hIdent y hy) ▸ hy
  have hFirstMax : MaximumInBeingIsFirstBeing p.InAct MoreIn p.esse PriorSimply := by
    intro z hz
    exact (hIdent z hz) ▸ hFirst
  have hNaming :=
    TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.reducedDescription
      p.InAct MoreIn p.CausesIn p.esse ComponentOf PriorSimply IsGod
      hBeing hTransfer hNoComponent hFirstMax hFull
  exact ⟨n, hn, hFirst, hNaming n hnMax (hGenus n hnMax) hIdent⟩

/-- Projection: the named source is a GOD_4 witness. -/
theorem godExistsOfDeEnteSourceIsGod {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply : B → B → Prop) (IsGod : B → Prop)
    (h : DeEnteSourceIsGodAt m w p PriorSimply IsGod) : GodExists IsGod := by
  obtain ⟨n, _, _, hGod⟩ := h
  exact ⟨n, hGod⟩

end TruthCore.Results.Causality.DeEnteSourceGod
