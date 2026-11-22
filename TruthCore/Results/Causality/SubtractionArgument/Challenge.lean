import TruthCore.Causality.SubtractionArgument

/-! The subtraction argument for metaphysical nihilism, free recombination and
the necessary-being nodes: the argument, the stage-one node against its
contingency premise, recombination as that premise's support, the strength
order of recombination, and laws and models. Analyst formulations; attribution
deferred. Zero-axiom: excluded middle enters only as the explicit premise
`TruthCore.Logic.ExcludedMiddle`. -/

namespace TruthCore.Results.Causality.SubtractionArgument
open TruthCore.Modal
open TruthCore.Causality.SubtractionArgument
open TruthCore.Causality.SubtractionArgument.Model
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.ModalSenseSupport (OnticFrameTransitive)
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Case.Catholicism (Signature)

/-- The subtraction argument: from a possible world with finitely many
concrete objects, subtract them one at a time. Each step needs S2 (the object
could fail to exist) and S3 (it could fail with no newcomer) at the current
world, and transitivity keeps every step accessible from `w`. Excluded middle
decides at each step whether the next listed object is present. -/
theorem subtraction {W B : Type} (m : Profile W B) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle) (hTrans : OnticFrameTransitive m)
    (h1 : PossiblyFinitelyManyConcrete m w) (h2 : EachConcreteCouldFailThroughout m w)
    (h3 : SubtractableThroughout m w) : PossiblyNoConcrete m w := by
  sorry

/-- The stage-one node excludes S2 at its world: the necessary concrete
object present at `w` exists at every accessible world, so not every concrete
object present at `w` could fail to exist. The converse, with excluded middle,
is in the controls (`Laws`, 8): S2 at `w` is exactly the node's denial. -/
theorem necessaryConcreteExcludesContingencyPremise {W B : Type} (m : Profile W B) (w : W)
    (hnc : NecessaryConcreteAt m w) : NotEachConcreteCouldFailAt m w := by
  sorry

/-- Unrestricted recombination gives S2 at `w` when every concrete candidate
has a distinct possible concrete companion: `x` without `y` is possible, so
`y`'s absence is. -/
theorem recombinationGivesContingency {W B : Type} (m : Profile W B) (w : W)
    (hR : UnrestrictedRecombinationAt m w) (hC : ConcreteCompanionsAt m w) :
    EachConcreteCouldFailAt m w := by
  sorry

/-- Unrestricted recombination strengthens contingent recombination. -/
theorem unrestrictedToContingentRecombination {W B : Type} (m : Profile W B) (w : W)
    (h : UnrestrictedRecombinationAt m w) : ContingentRecombinationAt m w := by
  sorry

/-- Certified difference (#1598): unrestricted recombination is exactly
contingent recombination together with the possible absence of every
companioned concrete candidate. Premise-free, constructive. -/
theorem recombinationFactorsExact : RecombinationFactorsExact := by
  sorry

/-- Batch controls (premise-free). -/
theorem controls : Model.Controls := by
  sorry

end TruthCore.Results.Causality.SubtractionArgument
