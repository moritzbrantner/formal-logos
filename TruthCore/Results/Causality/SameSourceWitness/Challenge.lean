import TruthCore.Causality.SameSourceWitness
import TruthCore.Results.Causality.PerfectRootIntellectFromGovernor.Solution
import TruthCore.Results.Causality.LocalTeleologyGodIntellect.Solution

/-!
# Same-source witness identities and the local-teleology intellect join (#1731)

* `deEnteSourceIsUnderived`: the De ente first source n and a necessary
  concrete underived candidate u of the SAME `m`, `w` are both actual roots;
  with `UniqueActualRootAt m w`, u = n.
* `deEnteSourceIsClassicalGodRoot`: the classical God root g contains
  `PerfectRootAt`, whose own uniqueness clause covers every actual root; so
  g = n from De ente root existence alone. No separate uniqueness package.
* `localTeleologyPerfectRoot`: the witness-local Fifth Way and first-mover /
  maximum identity give intellect to the supplied perfect root's SAME witness,
  through the existing GOD_4 consumer (instantiated at maxima) and the existing
  governor derivation (whose global direction clause is instantiated vacuously).

Nothing here proves an input, all-world underivedness from roothood, GOD_4
naming or any source reading; every bridge stays an explicit premise.
-/

namespace TruthCore.Results.Causality.SameSourceWitness

open TruthCore.Causality.SameSourceWitness
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)
open TruthCore.Causality.NecessaryConcreteUnderived (NecessaryConcreteUnderivedAt)
open TruthCore.Causality.NecessaryClassicalGodRoot (NecessaryClassicalGodRootAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Causality.RootPositiveIntellectWill
open TruthCore.Causality.WitnessLocalTeleology (Bundle)
open TruthCore.Latin.Aquinas.DeEnte (DeEnteFirstSourceIsActualRootAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic (ExcludedMiddle)

/-- The underived candidate has no existing concrete ground at any world, so
in particular none at `w`: it is an actual root. Unique roothood at `w` then
identifies it with the De ente source. All-world underivedness is a premise,
not derived from the source's roothood at `w`. -/
theorem deEnteSourceIsUnderived {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (hSource : DeEnteFirstSourceIsActualRootAt m w p)
    (hUnderived : NecessaryConcreteUnderivedAt m w)
    (hUnique : UniqueActualRootAt m w) :
    DeEnteSourceIsUnderivedAt m w p := by
  sorry

/-- The classical root's `PerfectRootAt` makes it the only actual root of the
SAME `m`, `w`; the De ente source is an actual root, hence that same being. -/
theorem deEnteSourceIsClassicalGodRoot {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hSource : DeEnteFirstSourceIsActualRootAt m w p)
    (hGod : NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply
      ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill) :
    DeEnteSourceIsClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply
      ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill := by
  sorry

/-- Local-teleology support option for the positive-root tuple. The local
bundle yields an intellectual first unmoved mover f; first-mover/maximum
identity makes every esse maximum have intellect (the existing GOD_4 consumer
with the maximum predicate in the GOD_4 slot, so its naming converse holds by
definition and no GOD_4 premise enters). The supplied perfect root n is such a
maximum, so `HasIntellect n`. The existing governor derivation then gives the
tuple; its "every natural body is directed" clause is instantiated with an
empty natural-body predicate, because that derivation uses only an intelligent
maximum. No global governor, immateriality bridge or GOD_4 naming premise. -/
theorem localTeleologyPerfectRoot {W B P R E : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (GoodIn : B → R → Prop) (MoreIn : R → B → B → Prop)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill : B → Prop)
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body Cog : B → Prop) (Reg Best Chance Tends : B → E → Prop) (Dir : B → B → E → Prop)
    (hPerfect : NecessaryPerfectRootAt m w p.InAct MoreIn p.esse)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn p.InAct)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite p.CausesIn p.esse)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hLocal : Bundle Moved Moves Body Cog HasIntellect Reg Best Chance Tends Dir)
    (hIdentity : FirstUnmovedMoverIsMaximeEns Moved Moves p.InAct MoreIn p.esse)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill) :
    NecessaryPositiveRootIntellectWillAt m w p GoodIn MoreIn PriorSimply ComponentOf
      Composite MatterForm HasIntellect HasWill := by
  sorry

end TruthCore.Results.Causality.SameSourceWitness
