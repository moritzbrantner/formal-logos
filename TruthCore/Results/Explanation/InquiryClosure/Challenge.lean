import TruthCore.Explanation.InquiryClosure
import TruthCore.Results.Causality.RootClosure.Solution

namespace TruthCore.Results.Explanation.InquiryClosure

open TruthCore.Explanation.InquiryClosure
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.PSRSelfApplication
open TruthCore.Explanation.StoppingPoints (NecessaryFact WorkIndependent)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPerfectionExclusion
  (ActualProfile UnexplainedAbsence NoUnexplainedAbsenceAtRoots)
open TruthCore.Causality.RootPerfectionIntellect (AdmissibleIsExclusionFree)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Causality.RootClosure (RootAbsencesNecessary
  EssenceGroundedRootProfileModality RootEssentialConditionsPositive
  RootEssentialConditionsCarried)
open TruthCore.Causality.SourceIntellectControls (HasCompatibleExtension)
open TruthCore.Results.Causality.RootClosure (carriedClosureNotUnexplained
  positiveEssenceFromCarriage unexplainedAbsenceIsContingent)
open TruthCore.Logic (ExcludedMiddle)

/-! ## Registered derivations -/

/-- The unrestricted fact PSR at `w` gives the PSR for root lack facts at `w`:
a lack fact of an actual root is a fact. -/
theorem rootLackPSROfFactPSR {W B F D : Type} (m : Profile W B) (w : W)
    (A : Arena W B F) (lack : B → D → F) (hF : FactPSR A w) :
    RootLackPSR m w A lack := by
  sorry

/-- E from the PSR for root lack facts and the sense bridge. Fix an actual root
`r` and a determination `d` it lacks while some admissible profile contains its
determinations and `d`. The lack fact holds (lack facts represented), so it has
an admitted reason (PSR for root lack facts), so it is positively fixed (sense
bridge). Either no admissible profile adds `d` to the root's determinations,
against the hypothesis, or a determination of the root requires the lack of a
set within that profile, which the necessity direction of member grounding
forbids (`carriedClosureNotUnexplained`). -/
theorem noUnexplainedAbsenceFromPositiveLackReasons {W B F D : Type}
    (m : Profile W B) (w : W) (A : Arena W B F) (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F)
    (hPSR : RootLackPSR m w A lack) (hFacts : RootLackFactsAt m w A HasAt lack)
    (hBridge : RootLackReasonsPositive m w A Admissible RequiresLack HasAt lack)
    (hMG : AdmissibleIsExclusionFree Admissible RequiresLack) :
    NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w) := by
  sorry

/-- The relocation converse: E alone gives the sense bridge, for any arena,
lack facts and requirement relation. An absence that is not unexplained is
fixed at the admissibility level, whatever reasons it has. -/
theorem positiveLackReasonsOfNoUnexplainedAbsence {W B F D : Type}
    (m : Profile W B) (w : W) (A : Arena W B F) (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F)
    (hE : NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w)) :
    RootLackReasonsPositive m w A Admissible RequiresLack HasAt lack := by
  sorry

/-- Strength order: essential exclusion of every root lack gives the
conditional form (drop the reason hypothesis). -/
theorem lackReasonsEssentialOfExcluded {W B F D : Type}
    (m : Profile W B) (w : W) (A : Arena W B F)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F)
    (hX : RootLacksEssentiallyExcluded m w Ess HasAt) :
    RootLackReasonsEssential m w A Ess HasAt lack := by
  sorry

/-- E from essential exclusion of root lacks, carriage (LE) and the necessity
direction of member grounding, without N or EM. Fix an actual root `r` lacking
`d` while an admissible `q` contains its determinations and `d`. Some ESSENCE_6
condition `C` on `r`'s profile fails at every such profile, so at `q`. The
necessity direction makes `q` exclusion-free, and carriage then gives `C` at
`q` (`positiveEssenceFromCarriage`), a contradiction. -/
theorem noUnexplainedAbsenceFromEssentialExclusion {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hX : RootLacksEssentiallyExcluded m w Ess HasAt)
    (hLE : RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack)
    (hMG : AdmissibleIsExclusionFree Admissible RequiresLack) :
    NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w) := by
  sorry

/-! ## General lemmas for the certificate -/

/-- E from the PSR for root lack facts, the lack facts, the thesis that a root
lack's admitted reasons require a nature excluding it, carriage (LE) and the
necessity direction of member grounding. The last three give the sense bridge
(`factorization`): an absence with an admitted reason is excluded by an
ESSENCE_6 condition, carriage puts that condition at every admissible
extension, so no admissible extension adds the missing determination. The
first two supply the admitted reason, and
`noUnexplainedAbsenceFromPositiveLackReasons` concludes. No N and no EM. -/
theorem noUnexplainedAbsenceFromEssentialLackReasons {W B F D : Type}
    (m : Profile W B) (w : W) (A : Arena W B F) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (RequiresLack : D → Set D → Prop)
    (HasAt : W → B → D → Prop) (lack : B → D → F)
    (hPSR : RootLackPSR m w A lack) (hFacts : RootLackFactsAt m w A HasAt lack)
    (hRE : RootLackReasonsEssential m w A Ess HasAt lack)
    (hLE : RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack)
    (hMG : AdmissibleIsExclusionFree Admissible RequiresLack) :
    NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w) := by
  sorry

/-! ## Finite controls -/

local notation "pureSet" => TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
open TruthCore.Causality.SourceIntellectControls.ProfileControls hiding pure
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootClosure.Control
  (hasAt essOpen essNeg noReq aExcludesNoesis noNoesis hasSel SelDet cE cLE)
open TruthCore.Results.Causality.RootPerfectionExclusion (rootIff memPure)
open TruthCore.Results.Causality.RootClosure (pureOpen' positiveSubPure noesisPure
  noesisNotPositive' nOf leOpen notLENeg leCarried mgNoReq notMGCarried eOf notEPositive
  classicalSelectionControl)
open TruthCore.Explanation.InquiryClosure.Control

/-- Comparator companion of `noUnexplainedAbsenceFromPositiveLackReasons` and
`positiveLackReasonsOfNoUnexplainedAbsence`. On the #2153 carrier (open family,
the source the only actual root), each row lists the PSR for root lack facts,
the lack facts, the sense bridge, the necessity direction of member grounding
and E:
1. positive witness: the source has every pure determination, the extended
   arena (every necessary truth a reason for every necessary truth); all hold;
2. the bridge fails: profile `{esse, a, b}`, extended arena; the source's
   lack of `noesis` has an admitted reason and is not positively fixed. This
   is the rival with the unrestricted fact PSR;
3. the PSR fails: the same profile, the base arena (no lack has a reason); the
   bridge holds vacuously;
4. the lack facts fail: the same profile, no lack fact true anywhere;
5. the necessity direction fails: the pure `a` requires the lack of `noesis`
   in a family that admits every pure profile; the bridge holds by carriage.
In rows 2–5, E fails. -/
theorem lackReasonControls :
    (RootLackPSR rootProfile true (extended pureSet) lackOf ∧
      RootLackFactsAt rootProfile true (extended pureSet) (hasAt pureSet pureSet) lackOf ∧
      RootLackReasonsPositive rootProfile true (extended pureSet) openProfile noReq
        (hasAt pureSet pureSet) lackOf ∧
      AdmissibleIsExclusionFree openProfile noReq ∧ cE pureSet pureSet) ∧
    (RootLackPSR rootProfile true (extended positive) lackOf ∧
      RootLackFactsAt rootProfile true (extended positive) (hasAt positive positive) lackOf ∧
      ¬ RootLackReasonsPositive rootProfile true (extended positive) openProfile noReq
        (hasAt positive positive) lackOf ∧
      AdmissibleIsExclusionFree openProfile noReq ∧ ¬ cE positive positive) ∧
    (¬ RootLackPSR rootProfile true (base positive) lackOf ∧
      RootLackFactsAt rootProfile true (base positive) (hasAt positive positive) lackOf ∧
      RootLackReasonsPositive rootProfile true (base positive) openProfile noReq
        (hasAt positive positive) lackOf ∧
      AdmissibleIsExclusionFree openProfile noReq ∧ ¬ cE positive positive) ∧
    (RootLackPSR rootProfile true (unrepresented positive) lackOf ∧
      ¬ RootLackFactsAt rootProfile true (unrepresented positive) (hasAt positive positive)
        lackOf ∧
      RootLackReasonsPositive rootProfile true (unrepresented positive) openProfile noReq
        (hasAt positive positive) lackOf ∧
      AdmissibleIsExclusionFree openProfile noReq ∧ ¬ cE positive positive) ∧
    (RootLackPSR rootProfile true (extended positive) lackOf ∧
      RootLackFactsAt rootProfile true (extended positive) (hasAt positive positive) lackOf ∧
      RootLackReasonsPositive rootProfile true (extended positive) openProfile aExcludesNoesis
        (hasAt positive positive) lackOf ∧
      ¬ AdmissibleIsExclusionFree openProfile aExcludesNoesis ∧ ¬ cE positive positive) := by
  sorry

/-! ### Essential exclusion -/

/-- Comparator companion of `noUnexplainedAbsenceFromEssentialExclusion`. Each
row lists essential exclusion of root lacks, carriage (LE), the necessity
direction of member grounding and E:
1. positive witness: every pure determination, only admissibility essential;
2. essential exclusion fails: profile `{esse, a, b}`, only admissibility
   essential (the lack of `noesis` is excluded by no nature);
3. LE fails: the same profile, the nature also contains the bare clause
   "lacks `noesis`" (it excludes `noesis`, so essential exclusion holds);
4. the necessity direction fails: the clause carried by the pure `a`;
5. the classical selection carrier: every pure determination, a selection
   read as a real intrinsic determination that varies across worlds, each
   selection requiring the lack of the other. Essential exclusion, LE, the
   necessity direction and E hold while N fails: on this route the classical
   root's non-selection of the other outcome is a case (ii) absence carried by
   its selection, and its contingency costs nothing. -/
theorem essentialExclusionControls :
    (cXN essOpen pureSet ∧ cLE essOpen pureSet pureSet noReq ∧
      AdmissibleIsExclusionFree openProfile noReq ∧ cE pureSet pureSet) ∧
    (¬ cXN essOpen positive ∧ cLE essOpen positive positive noReq ∧
      AdmissibleIsExclusionFree openProfile noReq ∧ ¬ cE positive positive) ∧
    (cXN essNeg positive ∧ ¬ cLE essNeg positive positive noReq ∧
      AdmissibleIsExclusionFree openProfile noReq ∧ ¬ cE positive positive) ∧
    (cXN essNeg positive ∧ cLE essNeg positive positive aExcludesNoesis ∧
      ¬ AdmissibleIsExclusionFree openProfile aExcludesNoesis ∧ ¬ cE positive positive) ∧
    (RootLacksEssentiallyExcluded rootProfile true essSel hasSel ∧
      RootEssentialConditionsCarried rootProfile true selAdmissible essSel hasSel selReq ∧
      AdmissibleIsExclusionFree selAdmissible selReq ∧
      NoUnexplainedAbsenceAtRoots rootProfile true selAdmissible (hasSel true) ∧
      ¬ RootAbsencesNecessary rootProfile true hasSel ∧
      ¬ hasSel true true (.inr false) ∧ hasSel false true (.inr false)) := by
  sorry

/-- Comparator companion of `noUnexplainedAbsenceFromEssentialLackReasons` and
`lackReasonsEssentialOfExcluded`. Each row lists the PSR for root lack facts,
the lack facts, the thesis that a root lack's admitted reasons require an
essential exclusion, carriage (LE), the necessity direction of member grounding
and E:
1. positive witness: every pure determination, the extended arena, only
   admissibility essential; all hold;
2. the PSR fails: profile `{esse, a, b}`, the base arena (no lack has a
   reason), only admissibility essential. Here the reason thesis holds
   vacuously while essential exclusion of root lacks fails, so the order
   `lackReasonsEssentialOfExcluded` is strict;
3. the reason thesis fails: the same profile, the extended arena (the lack of
   `noesis` has the necessary truths as admitted reasons, and no nature
   excludes `noesis`);
4. the lack facts fail: no lack fact true;
5. LE fails: the extended arena, the bare clause "lacks `noesis`" in the
   source's nature (it excludes `noesis`, so the reason thesis holds). This is
   the rival: the PSR, the lack facts and the reason thesis all hold;
6. the necessity direction fails: the clause carried by the pure `a`.
In rows 2–6, E fails. -/
theorem lackReasonEssenceControls :
    (RootLackPSR rootProfile true (extended pureSet) lackOf ∧
      RootLackFactsAt rootProfile true (extended pureSet) (hasAt pureSet pureSet) lackOf ∧
      RootLackReasonsEssential rootProfile true (extended pureSet) essOpen
        (hasAt pureSet pureSet) lackOf ∧
      cLE essOpen pureSet pureSet noReq ∧ AdmissibleIsExclusionFree openProfile noReq ∧
      cE pureSet pureSet) ∧
    (¬ RootLackPSR rootProfile true (base positive) lackOf ∧
      RootLackFactsAt rootProfile true (base positive) (hasAt positive positive) lackOf ∧
      RootLackReasonsEssential rootProfile true (base positive) essOpen
        (hasAt positive positive) lackOf ∧
      cLE essOpen positive positive noReq ∧ AdmissibleIsExclusionFree openProfile noReq ∧
      ¬ cE positive positive ∧ ¬ cXN essOpen positive) ∧
    (RootLackPSR rootProfile true (extended positive) lackOf ∧
      RootLackFactsAt rootProfile true (extended positive) (hasAt positive positive) lackOf ∧
      ¬ RootLackReasonsEssential rootProfile true (extended positive) essOpen
        (hasAt positive positive) lackOf ∧
      cLE essOpen positive positive noReq ∧ AdmissibleIsExclusionFree openProfile noReq ∧
      ¬ cE positive positive) ∧
    (RootLackPSR rootProfile true (unrepresented positive) lackOf ∧
      ¬ RootLackFactsAt rootProfile true (unrepresented positive) (hasAt positive positive)
        lackOf ∧
      RootLackReasonsEssential rootProfile true (unrepresented positive) essOpen
        (hasAt positive positive) lackOf ∧
      cLE essOpen positive positive noReq ∧ AdmissibleIsExclusionFree openProfile noReq ∧
      ¬ cE positive positive) ∧
    (RootLackPSR rootProfile true (extended positive) lackOf ∧
      RootLackFactsAt rootProfile true (extended positive) (hasAt positive positive) lackOf ∧
      RootLackReasonsEssential rootProfile true (extended positive) essNeg
        (hasAt positive positive) lackOf ∧
      ¬ cLE essNeg positive positive noReq ∧ AdmissibleIsExclusionFree openProfile noReq ∧
      ¬ cE positive positive) ∧
    (RootLackPSR rootProfile true (extended positive) lackOf ∧
      RootLackFactsAt rootProfile true (extended positive) (hasAt positive positive) lackOf ∧
      RootLackReasonsEssential rootProfile true (extended positive) essNeg
        (hasAt positive positive) lackOf ∧
      cLE essNeg positive positive aExcludesNoesis ∧
      ¬ AdmissibleIsExclusionFree openProfile aExcludesNoesis ∧ ¬ cE positive positive) := by
  sorry

/-! ### The rival with the full inquiry stance -/

/-! ## The certificate -/

/-- **What the inquiry family reaches at a root, and what would carry it to E**
(`InquiryScopeMap`). -/
theorem inquiryScopeMap : InquiryScopeMap := by
  sorry

end TruthCore.Results.Explanation.InquiryClosure
