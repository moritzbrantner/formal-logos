import TruthCore.Causality.RootClosure
import TruthCore.Results.Causality.RootPerfectionExclusion.Solution

namespace TruthCore.Results.Causality.RootClosure

open TruthCore.Causality.RootClosure
open TruthCore.Causality.RootClosure.Control
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPerfectionExclusion
  (ActualProfile UnexplainedAbsence NoUnexplainedAbsenceAtRoots)
open TruthCore.Causality.RootPerfectionIntellect (AdmissibleIsExclusionFree PureRequiresNoPureLack)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Causality.SourceIntellectControls (HasCompatibleExtension)

/-! ## A. E from essence-grounded modality with positive essences -/

/-- E from N, EM and EP. Fix an actual root `r` at `w` and a determination `d`
that `r` lacks while some admissible `q` contains all of `r`'s determinations
and `d` (case iii). EP makes every essential condition on `r`'s profile hold of
`q`, so EM gives an accessible world at which `r` has every member of `q`, in
particular `d`. N then gives `r` the determination `d` at `w`, a contradiction.
No case analysis and no axioms. -/
theorem noUnexplainedAbsenceFromPositiveEssence {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (hN : RootAbsencesNecessary m w HasAt)
    (hEM : EssenceGroundedRootProfileModality m w Ess HasAt)
    (hEP : RootEssentialConditionsPositive m w Admissible Ess HasAt) :
    NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w) := by
  sorry

/-- EP from LE and the necessity direction of member grounding (`89c988d9`).
For an admissible extension `q` of an actual root's profile, the necessity
direction makes `q` exclusion-free: no member of `q`, and so no determination of
the root, requires the lack of a subset of `q`. LE then gives every essential
condition at `q`. No axioms. -/
theorem positiveEssenceFromCarriage {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hLE : RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack)
    (hMG : AdmissibleIsExclusionFree Admissible RequiresLack) :
    RootEssentialConditionsPositive m w Admissible Ess HasAt := by
  sorry

/-- EP gives LE: the strength order of the two (EP drops LE's hypothesis). -/
theorem carriedOfPositive {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hEP : RootEssentialConditionsPositive m w Admissible Ess HasAt) :
    RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack := by
  sorry

/-! ## Lean-only diagnostics -/

open TruthCore.Explanation.PSRStrength (Arena Access)
open TruthCore.Explanation.TruthmakerTheories (Making Sound MakerNecessitation NeedsMakerAt)

/-! ## Finite controls -/

local notation "pureSet" => TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
open TruthCore.Causality.SourceIntellectControls.ProfileControls hiding pure
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Results.Causality.RootPerfectionExclusion (rootIff memPure)

/-- Comparator companion of `noUnexplainedAbsenceFromPositiveEssence`. On one
carrier (open family, the source the only actual root), each row lists N, EM,
EP and E:
1. positive witness: the source has every pure determination at both worlds,
   its nature imposes only admissibility; all four hold;
2. N fails: the source lacks `noesis` actually and has it at the other world
   (a contingent lack); EM and EP hold, E fails;
3. EM fails: the source lacks `noesis` at both worlds and its nature imposes
   only admissibility (a necessary lack that no nature grounds: modal
   primitivism or brutalism); N and EP hold, E fails;
4. EP fails: the same profile, and its nature also contains the negative clause
   "lacks `noesis`" (the rival's negative essence); N and EM hold, E fails. -/
theorem essenceControls :
    (cN pureSet pureSet ∧ cEM essOpen pureSet pureSet ∧ cEP essOpen pureSet pureSet ∧
      cE pureSet pureSet) ∧
    (¬ cN positive pureSet ∧ cEM essOpen positive pureSet ∧ cEP essOpen positive pureSet ∧
      ¬ cE positive pureSet) ∧
    (cN positive positive ∧ ¬ cEM essOpen positive positive ∧
      cEP essOpen positive positive ∧ ¬ cE positive positive) ∧
    (cN positive positive ∧ cEM essNeg positive positive ∧
      ¬ cEP essNeg positive positive ∧ ¬ cE positive positive) := by
  sorry

/-- Comparator companion of `positiveEssenceFromCarriage` and
`carriedOfPositive`. Same carrier, the source lacking `noesis` at both worlds
except in row 1. Each row lists LE, the necessity direction of member
grounding, and EP:
1. positive witness: only admissibility is essential and nothing requires a
   lack; all three hold (source with every pure determination);
2. LE fails: the negative clause "lacks `noesis`" is carried by no determination
   (nothing requires a lack); the necessity direction holds, EP fails. This is
   the rival's non-determinative closure;
3. the necessity direction fails: the clause is carried by the pure `a`, which
   requires the lack of `noesis`, but the family still admits `pure`; LE holds
   and EP fails (so EP is strictly stronger than LE). Here `a`, a pure
   determination, requires the lack of the pure `noesis`, so the purity of
   requirements (`0c8631bd`) fails too: a carried closure of a pure
   determination is what that premise excludes. N and EM hold in this row and
   E fails, so carriage with N and EM, without the necessity direction, does
   not give E. -/
theorem carriageControls :
    (cLE essOpen pureSet pureSet noReq ∧ AdmissibleIsExclusionFree openProfile noReq ∧
      cEP essOpen pureSet pureSet) ∧
    (¬ cLE essNeg positive positive noReq ∧ AdmissibleIsExclusionFree openProfile noReq ∧
      ¬ cEP essNeg positive positive) ∧
    (cLE essNeg positive positive aExcludesNoesis ∧
      ¬ AdmissibleIsExclusionFree openProfile aExcludesNoesis ∧
      ¬ cEP essNeg positive positive ∧
      ¬ PureRequiresNoPureLack aExcludesNoesis
        TruthCore.Causality.RootPerfectionExclusion.Control.isPure ∧
      cN positive positive ∧ cEM essNeg positive positive ∧ ¬ cE positive positive) := by
  sorry

/-- Strictness certificate for "positive root essences strengthen carriage":
row 3 of `carriageControls`. -/
theorem carriedClosureSeparates : CarriedClosureSeparates := by
  sorry

end TruthCore.Results.Causality.RootClosure
