module

public import TruthCore.Explanation.InquiryClosure
public import TruthCore.Results.Causality.RootClosure.Solution

@[expose] public section

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
    RootLackPSR m w A lack :=
  fun _ _ _ h => hF _ h

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
  rintro r hr d ⟨hLack, hExt⟩
  rcases hBridge r hr d hLack (hPSR r hr d ((hFacts r hr d).2 hLack)) with
    hNo | ⟨t, S, ht, -, hS, hReq⟩
  · exact hNo hExt
  · exact carriedClosureNotUnexplained Admissible RequiresLack (HasAt w) r d t S hMG ht hS
      hReq ⟨hLack, hExt⟩

/-- The relocation converse: E alone gives the sense bridge, for any arena,
lack facts and requirement relation. An absence that is not unexplained is
fixed at the admissibility level, whatever reasons it has. -/
theorem positiveLackReasonsOfNoUnexplainedAbsence {W B F D : Type}
    (m : Profile W B) (w : W) (A : Arena W B F) (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F)
    (hE : NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w)) :
    RootLackReasonsPositive m w A Admissible RequiresLack HasAt lack :=
  fun r hr d hLack _ => Or.inl fun hExt => hE r hr d ⟨hLack, hExt⟩

/-- Strength order: essential exclusion of every root lack gives the
conditional form (drop the reason hypothesis). -/
theorem lackReasonsEssentialOfExcluded {W B F D : Type}
    (m : Profile W B) (w : W) (A : Arena W B F)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F)
    (hX : RootLacksEssentiallyExcluded m w Ess HasAt) :
    RootLackReasonsEssential m w A Ess HasAt lack :=
  fun r hr d hLack _ => hX r hr d hLack

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
  rintro r hr d ⟨hLack, q, hq, hsub, hd⟩
  obtain ⟨y, C, hC, hEx⟩ := hX r hr d hLack
  exact hEx q hsub hd
    (positiveEssenceFromCarriage m w Admissible Ess HasAt RequiresLack hLE hMG r hr y C hC q hq
      hsub)

/-! ## General lemmas for the certificate -/

section General

variable {W B F : Type}

theorem explainedIff {A : Arena W B F} {e : W → F → F → Prop} (h : AgreeOnContingent A e)
    {v : W} {f : F} (hc : Contingent A v f) :
    Explained A v f ↔ Explained (withReasons A e) v f :=
  ⟨fun ⟨r, hr⟩ => ⟨r, (h v r f hc).1 hr⟩, fun ⟨r, hr⟩ => ⟨r, (h v r f hc).2 hr⟩⟩

theorem bruteIff {A : Arena W B F} {e : W → F → F → Prop} (h : AgreeOnContingent A e)
    (v : W) (f : F) : BruteAt A v f ↔ BruteAt (withReasons A e) v f :=
  ⟨fun ⟨hc, hn⟩ => ⟨hc, fun hx => hn ((explainedIff h hc).2 hx)⟩,
    fun ⟨hc, hn⟩ => ⟨hc, fun hx => hn ((explainedIff h hc).1 hx)⟩⟩

theorem blindness (A : Arena W B F) (I : Inquiry W F) (e : W → F → F → Prop)
    (h : AgreeOnContingent A e) :
    (∀ w, (ContingentPSR A w ↔ ContingentPSR (withReasons A e) w) ∧
        (NoBrute A w ↔ NoBrute (withReasons A e) w) ∧
        (TrackingBridge A I w ↔ TrackingBridge (withReasons A e) I w) ∧
        (SupportCoverage A I w ↔ SupportCoverage (withReasons A e) I w) ∧
        (EvidenceBridge A I w ↔ EvidenceBridge (withReasons A e) I w) ∧
        (GlobalDefeat A I w ↔ GlobalDefeat (withReasons A e) I w) ∧
        (NoBruteEvidenceAlternative A I w ↔
          NoBruteEvidenceAlternative (withReasons A e) I w)) ∧
      (ReasonIndependent A ↔ ReasonIndependent (withReasons A e)) ∧
      (IrreflexiveContingent A ↔ IrreflexiveContingent (withReasons A e)) := by
  refine ⟨fun w => ⟨?_, ?_, ?_, Iff.rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact ⟨fun hP f hc => (explainedIff h hc).1 (hP f hc),
      fun hP f hc => (explainedIff h hc).2 (hP f hc)⟩
  · exact ⟨fun hN ⟨f, hb⟩ => hN ⟨f, (bruteIff h w f).2 hb⟩,
      fun hN ⟨f, hb⟩ => hN ⟨f, (bruteIff h w f).1 hb⟩⟩
  · exact ⟨fun hT f hc hs => (explainedIff h hc).1 (hT f hc hs),
      fun hT f hc hs => (explainedIff h hc).2 (hT f hc hs)⟩
  · exact ⟨fun hE e' p hs hc => (explainedIff h hc).1 (hE e' p hs hc),
      fun hE e' p hs hc => (explainedIff h hc).2 (hE e' p hs hc)⟩
  · exact ⟨fun hG ⟨v, f, hv, hb⟩ => hG ⟨v, f, hv, (bruteIff h v f).2 hb⟩,
      fun hG ⟨v, f, hv, hb⟩ => hG ⟨v, f, hv, (bruteIff h v f).1 hb⟩⟩
  · exact ⟨fun hN e' p hs ⟨v, hv, hb, hp⟩ => hN e' p hs ⟨v, hv, (bruteIff h v e').2 hb, hp⟩,
      fun hN e' p hs ⟨v, hv, hb, hp⟩ => hN e' p hs ⟨v, hv, (bruteIff h v e').1 hb, hp⟩⟩
  · exact ⟨fun hR w r f hx hc => hR w r f ((h w r f hc).2 hx) hc,
      fun hR w r f hx hc => hR w r f ((h w r f hc).1 hx) hc⟩
  · exact ⟨fun hI w r hc hx => hI w r hc ((h w r r hc).2 hx),
      fun hI w r hc hx => hI w r hc ((h w r r hc).1 hx)⟩

theorem factPSRNotInvariant :
    AgreeOnContingent allNecessary (fun _ _ _ => False) ∧ FactPSR allNecessary false ∧
      ¬ FactPSR (withReasons allNecessary (fun _ _ _ => False)) false :=
  ⟨fun _ _ _ ⟨_, _, _, hv⟩ => absurd trivial hv, fun _ _ => ⟨false, rfl⟩,
    fun h => (h true trivial).elim fun _ hr => hr⟩

theorem necessaryNoBruteAlternative (A : Arena W B F) (w : W) (e p : F)
    (hp : NecessaryFact A w p) : ¬ BruteEvidenceAlternative A w e p :=
  fun ⟨v, hv, _, hn⟩ => hn (hp v hv)

theorem noBruteAlternativeOfPSR (A : Arena W B F) (I : Inquiry W F) (w : W)
    (hP : ∀ v, Access A w v → ContingentPSR A v) : NoBruteEvidenceAlternative A I w :=
  fun e _ _ ⟨v, hv, ⟨hc, hn⟩, _⟩ => hn (hP v hv e hc)

/-- Under excluded middle, a fact that is not necessary at `w` and true there
is contingent there. -/
theorem contingentOfNotNecessary (hEM : ExcludedMiddle) (A : Arena W B F) (w : W) (f : F)
    (hw : A.holds w f) (hn : ¬ NecessaryFact A w f) : Contingent A w f := by
  refine ⟨hw, ?_⟩
  rcases hEM (∃ v, Access A w v ∧ ¬ A.holds v f) with h | h
  · exact h
  · exact absurd (fun v hv => (hEM (A.holds v f)).resolve_right fun hf => h ⟨v, hv, hf⟩) hn

theorem notNecessaryOfContingent {A : Arena W B F} {w : W} {f : F} (hc : Contingent A w f) :
    ¬ NecessaryFact A w f :=
  fun hn => hc.2.elim fun v ⟨hv, hf⟩ => hf (hn v hv)

theorem cheapExtension (A : Arena W B F) (I : Inquiry W F) (w : W) :
    AgreeOnContingent A (necessaryReasons A) ∧
    (ExcludedMiddle → ContingentPSR A w → FactPSR (withReasons A (necessaryReasons A)) w) ∧
    (ExcludedMiddle → GlobalDefeat A I w →
      GlobalDefeatUnreasoned (withReasons A (necessaryReasons A)) I w) ∧
    (Factive A → Factive (withReasons A (necessaryReasons A))) ∧
    (Necessitating A → Necessitating (withReasons A (necessaryReasons A))) ∧
    (ConjunctSound A → Distribution A → Distribution (withReasons A (necessaryReasons A))) ∧
    (IrreflexiveContingent A →
      IrreflexiveContingent (withReasons A (necessaryReasons A))) ∧
    (ReasonIndependent A → ReasonIndependent (withReasons A (necessaryReasons A))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v r f hc
    refine ⟨Or.inl, fun hx => hx.resolve_right fun ⟨_, _, _, hn⟩ => notNecessaryOfContingent hc hn⟩
  · intro hEM hC f hf
    rcases hEM (NecessaryFact A w f) with hn | hn
    · exact ⟨f, Or.inr ⟨hf, hn, hf, hn⟩⟩
    · obtain ⟨r, hr⟩ := hC f (contingentOfNotNecessary hEM A w f hf hn)
      exact ⟨r, Or.inl hr⟩
  · rintro hEM hG ⟨v, f, hv, hf, hx⟩
    have hn : ¬ NecessaryFact A v f := fun hn => hx ⟨f, Or.inr ⟨hf, hn, hf, hn⟩⟩
    exact hG ⟨v, f, hv, contingentOfNotNecessary hEM A v f hf hn,
      fun ⟨r, hr⟩ => hx ⟨r, Or.inl hr⟩⟩
  · rintro hF w' r f (hx | ⟨hr, _, hf, _⟩)
    · exact hF w' r f hx
    · exact ⟨hr, hf⟩
  · rintro hN w' r f (hx | ⟨_, _, _, hf⟩) v hv hrv
    · exact hN w' r f hx v hv hrv
    · exact hf v hv
  · rintro hS hD w' r f g (hx | ⟨hr, hrn, hf, hfn⟩) hg
    · exact Or.inl (hD w' r f g hx hg)
    · exact Or.inr ⟨hr, hrn, hS g f w' hg hf, fun v hv => hS g f v hg (hfn v hv)⟩
  · rintro hI w' r hc (hx | ⟨_, hn, _, _⟩)
    · exact hI w' r hc hx
    · exact notNecessaryOfContingent hc hn
  · rintro hR w' r f (hx | ⟨_, _, _, hn⟩) hc
    · exact hR w' r f hx hc
    · exact absurd hn (notNecessaryOfContingent hc)

theorem independentReasonContingent (A : Arena W B F) (w : W) (r f : F)
    (hEM : ExcludedMiddle) (hF : Factive A) (hI : ∀ s, WorkIndependent A w s)
    (hx : A.explains w r f) (hn : NecessaryFact A w f) : Contingent A w r := by
  refine contingentOfNotNecessary hEM A w r (hF w r f hx).1 fun hr => ?_
  exact hI r f hx fun v hv => ⟨fun _ => hn v hv, fun _ => hr v hv⟩

theorem independentFactPSRContingency (A : Arena W B F) (w : W) (f : F)
    (hEM : ExcludedMiddle) (hP : FactPSR A w) (hF : Factive A)
    (hI : ∀ s, WorkIndependent A w s) (hf : A.holds w f) (hno : ∀ g, ¬ Contingent A w g) :
    False := by
  have hn : NecessaryFact A w f := by
    rcases hEM (NecessaryFact A w f) with h | h
    · exact h
    · exact absurd (contingentOfNotNecessary hEM A w f hf h) (hno f)
  obtain ⟨r, hr⟩ := hP f hf
  exact hno r (independentReasonContingent A w r f hEM hF hI hr hn)

end General

section Roots

variable {W B F D : Type}

theorem rootLacksNecessary (m : Profile W B) (A : Arena W B F) (w : W)
    (HasAt : W → B → D → Prop) (lack : B → D → F) (hO : A.ontic = m.ontic)
    (hRep : LackFactsRepresent A HasAt lack) (hN : RootAbsencesNecessary m w HasAt)
    (r : B) (hr : ActualRoot m w r) (d : D) (hLack : ¬ HasAt w r d) :
    A.holds w (lack r d) ∧ NecessaryFact A w (lack r d) ∧ ¬ Contingent A w (lack r d) := by
  have hNec : NecessaryFact A w (lack r d) := fun v hv =>
    (hRep v r d).2 fun hd => hLack (hN r hr v (by
      have : A.ontic.frame.access w v := hv
      rwa [hO] at this) d hd)
  exact ⟨(hRep w r d).2 hLack, hNec, fun hc => notNecessaryOfContingent hc hNec⟩

theorem contingentBranch (m : Profile W B) (A : Arena W B F) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (lack : B → D → F) (hO : A.ontic = m.ontic)
    (hRep : LackFactsRepresent A HasAt lack)
    (hEM : EssenceGroundedRootProfileModality m w Ess HasAt)
    (hEP : RootEssentialConditionsPositive m w Admissible Ess HasAt) (hC : ContingentPSR A w)
    (r : B) (hr : ActualRoot m w r) (d : D)
    (hU : UnexplainedAbsence Admissible (HasAt w) r d) :
    Contingent A w (lack r d) ∧ Explained A w (lack r d) := by
  obtain ⟨v, hv, hd⟩ := unexplainedAbsenceIsContingent m w Admissible Ess HasAt hEM hEP r hr d hU
  have hc : Contingent A w (lack r d) :=
    ⟨(hRep w r d).2 hU.1, v, (by show A.ontic.frame.access w v; rw [hO]; exact hv),
      fun h => (hRep v r d).1 h hd⟩
  exact ⟨hc, hC _ hc⟩

theorem factorization (m : Profile W B) (A : Arena W B F) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (RequiresLack : D → Set D → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F)
    (hRE : RootLackReasonsEssential m w A Ess HasAt lack)
    (hLE : RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack)
    (hMG : AdmissibleIsExclusionFree Admissible RequiresLack) :
    RootLackReasonsPositive m w A Admissible RequiresLack HasAt lack := by
  intro r hr d hLack hx
  refine Or.inl ?_
  rintro ⟨q, hq, hsub, hd⟩
  obtain ⟨y, C, hC, hEx⟩ := hRE r hr d hLack hx
  exact hEx q hsub hd
    (positiveEssenceFromCarriage m w Admissible Ess HasAt RequiresLack hLE hMG r hr y C hC q hq
      hsub)

theorem epistemicReading (m : Profile W B) (I : Inquiry W F) (w : W)
    (Admissible : Set D → Prop) (HasAt : W → B → D → Prop) (lack : B → D → F)
    (hS : ProfileSoundLackSupport m w I Admissible HasAt lack) :
    (∀ r, ActualRoot m w r → ∀ d, UnexplainedAbsence Admissible (HasAt w) r d →
        ¬ Supported I w (lack r d)) ∧
      (RootLacksKnown m w I HasAt lack → NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w)) :=
  ⟨fun r hr d hU hs => hS r hr d hs hU.2,
    fun hK r hr d hU => hS r hr d (hK r hr d hU.1) hU.2⟩

theorem referenceClass {W B D : Type} (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (HasAt : W → B → D → Prop) (Pure : D → Prop)
    (hImp : CarriersImpure RequiresLack Pure)
    (hPure : ActualRootDeterminationsArePure m w (HasAt w) Pure)
    (r : B) (hr : ActualRoot m w r) (d : D)
    (hP : PositivelyFixedAbsence Admissible RequiresLack (HasAt w) r d) :
    ¬ HasCompatibleExtension Admissible (ActualProfile (HasAt w) r) d := by
  rcases hP with h | ⟨t, S, ht, -, -, hReq⟩
  · exact h
  · exact absurd (hPure r hr t ht) (hImp t S hReq)

end Roots

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
    NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w) :=
  noUnexplainedAbsenceFromPositiveLackReasons m w A Admissible RequiresLack HasAt lack hPSR
    hFacts (factorization m A w Admissible Ess RequiresLack HasAt lack hRE hLE hMG) hMG

/-! ## Finite controls -/

section Controls

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

theorem classicalEM : ExcludedMiddle := fun p => Classical.em p

theorem hasAtWorld (s : Set Determination) (v u x : Bool) (d : Determination) :
    hasAt s s v x d ↔ hasAt s s u x d := by
  cases v <;> cases u <;> cases x <;> exact Iff.rfl

theorem baseContingent {src : Set Determination} {w : Bool} {f : CFact}
    (h : Contingent (base src) w f) : w = true ∧ f = .event := by
  obtain ⟨hw, v, -, hv⟩ := h
  cases f with
  | lack x d =>
    exact absurd (show (base src).holds v (.lack x d) from
      fun h' => (show ¬ hasAt src src w x d from hw) ((hasAtWorld src v w x d).1 h')) hv
  | event => exact ⟨hw, rfl⟩

theorem eventContingent (src : Set Determination) : Contingent (base src) true .event :=
  ⟨rfl, false, trivial, fun h => Bool.noConfusion h⟩

theorem baseContingentPSR (src : Set Determination) (w : Bool) : ContingentPSR (base src) w := by
  intro f hc
  obtain ⟨rfl, rfl⟩ := baseContingent hc
  exact ⟨.lack true .limiter, rfl, rfl, rfl⟩

theorem extendedFactPSR (src : Set Determination) (w : Bool) : FactPSR (extended src) w :=
  (cheapExtension (base src) inquiry w).2.1 classicalEM (baseContingentPSR src w)

theorem baseFactive (src : Set Determination) (hlim : Determination.limiter ∉ src) :
    Factive (base src) := by
  rintro w r f ⟨rfl, rfl, rfl⟩
  exact ⟨hlim, rfl⟩

theorem baseConjunctSound (src : Set Determination) : ConjunctSound (base src) :=
  fun _ _ _ h hf => h ▸ hf

theorem baseDistribution (src : Set Determination) : Distribution (base src) := by
  rintro w r f g hx rfl
  exact hx

theorem baseIrreflexive (src : Set Determination) : IrreflexiveContingent (base src) := by
  rintro w r - ⟨-, rfl, h⟩
  exact nomatch h

theorem baseIndependent (src : Set Determination) (hlim : Determination.limiter ∉ src) :
    ReasonIndependent (base src) := by
  rintro w r f ⟨rfl, rfl, rfl⟩ - hall
  exact Bool.noConfusion ((hall false trivial).1 hlim)

theorem limiterNotPure : Determination.limiter ∉ pureSet := fun h => (memPure _).1 h rfl

theorem limiterNotPositive :
    Determination.limiter ∉ TruthCore.Causality.SourceIntellectControls.ProfileControls.positive :=
  by simp [TruthCore.Causality.SourceIntellectControls.ProfileControls.positive]

theorem noesisExplained :
    Explained (extended positive) true (lackOf true Determination.noesis) :=
  extendedFactPSR positive true _ noesisNotPositive'

theorem baseLacksUnexplained (src : Set Determination) (x : Bool) (d : Determination) :
    ¬ Explained (base src) true (lackOf x d) :=
  fun ⟨_, hs⟩ => nomatch hs.2.2

theorem notBridgeRival :
    ¬ RootLackReasonsPositive rootProfile true (extended positive) openProfile noReq
      (hasAt positive positive) lackOf := by
  intro h
  rcases h true ((rootIff true).2 rfl) .noesis noesisNotPositive' noesisExplained with
    h | ⟨_, _, _, _, _, hq⟩
  · exact h ⟨pureSet, pureOpen', positiveSubPure, noesisPure⟩
  · exact hq

theorem rootLackPSRExtended (src : Set Determination) :
    RootLackPSR rootProfile true (extended src) lackOf :=
  rootLackPSROfFactPSR _ _ _ _ (extendedFactPSR src true)

theorem notRootLackPSRBase : ¬ RootLackPSR rootProfile true (base positive) lackOf :=
  fun h => baseLacksUnexplained positive true .noesis
    (h true ((rootIff true).2 rfl) .noesis noesisNotPositive')

theorem bridgeBase (A : Set Determination → Prop) (R : Determination → Set Determination → Prop) :
    RootLackReasonsPositive rootProfile true (base positive) A R (hasAt positive positive)
      lackOf :=
  fun _ _ d _ hx => absurd hx (baseLacksUnexplained positive _ d)

theorem rootLackPSRUnrep : RootLackPSR rootProfile true (unrepresented positive) lackOf :=
  fun _ _ _ h => nomatch h

theorem notFactsUnrep :
    ¬ RootLackFactsAt rootProfile true (unrepresented positive) (hasAt positive positive)
      lackOf :=
  fun h => (h true ((rootIff true).2 rfl) .noesis).2 noesisNotPositive'

theorem bridgeUnrep (A : Set Determination → Prop) (R : Determination → Set Determination → Prop) :
    RootLackReasonsPositive rootProfile true (unrepresented positive) A R
      (hasAt positive positive) lackOf :=
  fun _ _ _ _ ⟨_, hs⟩ => nomatch hs.2.2

theorem bridgeCarried :
    RootLackReasonsPositive rootProfile true (extended positive) openProfile aExcludesNoesis
      (hasAt positive positive) lackOf := by
  intro r hr d hLack _
  rw [rootIff] at hr
  subst hr
  cases d with
  | noesis =>
    exact Or.inr ⟨.a, {.noesis}, by simp [hasAt, positive], Set.mem_singleton _,
      Set.singleton_subset_iff.mpr (Set.mem_insert _ _), rfl, rfl⟩
  | limiter =>
    exact Or.inl fun ⟨q, hq, _, hl⟩ => hq.2 hl
  | esse => exact absurd (by simp [hasAt, positive]) hLack
  | a => exact absurd (by simp [hasAt, positive]) hLack
  | b => exact absurd (by simp [hasAt, positive]) hLack

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
      ¬ AdmissibleIsExclusionFree openProfile aExcludesNoesis ∧ ¬ cE positive positive) :=
  ⟨⟨rootLackPSRExtended _, fun _ _ _ => Iff.rfl,
      positiveLackReasonsOfNoUnexplainedAbsence _ _ _ _ _ _ _ (eOf _ _ subset_rfl), mgNoReq,
      eOf _ _ subset_rfl⟩,
    ⟨rootLackPSRExtended _, fun _ _ _ => Iff.rfl, notBridgeRival, mgNoReq, notEPositive _⟩,
    ⟨notRootLackPSRBase, fun _ _ _ => Iff.rfl, bridgeBase _ _, mgNoReq, notEPositive _⟩,
    ⟨rootLackPSRUnrep, notFactsUnrep, bridgeUnrep _ _, mgNoReq, notEPositive _⟩,
    ⟨rootLackPSRExtended _, fun _ _ _ => Iff.rfl, bridgeCarried, notMGCarried,
      notEPositive _⟩⟩

/-! ### Essential exclusion -/

theorem xnPureOpen : cXN essOpen pureSet := by
  intro r hr d hd
  rw [rootIff] at hr
  subst hr
  have hl : d = Determination.limiter := by
    by_contra h
    exact hd ((memPure d).2 h)
  subst hl
  exact ⟨true, openProfile, ⟨rfl, rfl, rfl⟩, fun _ _ hl hq => hq.2 hl⟩

theorem notXNPositiveOpen : ¬ cXN essOpen positive := by
  intro h
  obtain ⟨y, C, ⟨-, -, rfl⟩, hEx⟩ := h true ((rootIff true).2 rfl) .noesis noesisNotPositive'
  exact hEx pureSet positiveSubPure noesisPure pureOpen'

theorem xnPositiveNeg : cXN essNeg positive := by
  intro r hr d hd
  rw [rootIff] at hr
  subst hr
  cases d with
  | noesis => exact ⟨true, noNoesis, ⟨rfl, rfl, Or.inr rfl⟩, fun _ _ hn hq => hq hn⟩
  | limiter => exact ⟨true, openProfile, ⟨rfl, rfl, Or.inl rfl⟩, fun _ _ hl hq => hq.2 hl⟩
  | esse => exact absurd (by simp [hasAt, positive]) hd
  | a => exact absurd (by simp [hasAt, positive]) hd
  | b => exact absurd (by simp [hasAt, positive]) hd

theorem xnSel : RootLacksEssentiallyExcluded rootProfile true essSel hasSel := by
  intro r hr d hd
  rw [rootIff] at hr
  subst hr
  refine ⟨true, selAdmissible, ⟨rfl, rfl, rfl⟩, fun q hsub hdq hq => ?_⟩
  cases d with
  | inl d' =>
    have hl : d' = Determination.limiter := by
      by_contra h
      exact hd ((memPure d').2 h)
    subst hl
    exact hq.2.1 hdq
  | inr b =>
    cases b with
    | true => exact hd rfl
    | false => exact hq.2.2 ⟨@hsub (Sum.inr true) rfl, hdq⟩

theorem leSel :
    RootEssentialConditionsCarried rootProfile true selAdmissible essSel hasSel selReq := by
  rintro r - y C ⟨-, -, rfl⟩ q hq - -
  exact hq

theorem mgSel : AdmissibleIsExclusionFree selAdmissible selReq := by
  rintro q hq t ht S hS ⟨b, rfl, rfl⟩
  cases b with
  | false => exact hq.2.2 ⟨hS (Set.mem_singleton _), ht⟩
  | true => exact hq.2.2 ⟨ht, hS (Set.mem_singleton _)⟩

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
      ¬ hasSel true true (.inr false) ∧ hasSel false true (.inr false)) :=
  ⟨⟨xnPureOpen, leOpen _ _ _, mgNoReq, eOf _ _ subset_rfl⟩,
    ⟨notXNPositiveOpen, leOpen _ _ _, mgNoReq, notEPositive _⟩,
    ⟨xnPositiveNeg, notLENeg, mgNoReq, notEPositive _⟩,
    ⟨xnPositiveNeg, leCarried, notMGCarried, notEPositive _⟩,
    ⟨xnSel, leSel, mgSel,
      noUnexplainedAbsenceFromEssentialExclusion _ _ _ _ _ _ xnSel leSel mgSel,
      classicalSelectionControl.2, fun h => Bool.noConfusion h, rfl⟩⟩

theorem reBase : RootLackReasonsEssential rootProfile true (base positive) essOpen
    (hasAt positive positive) lackOf :=
  fun _ _ d _ hx => absurd hx (baseLacksUnexplained positive _ d)

theorem notREExtendedOpen : ¬ RootLackReasonsEssential rootProfile true (extended positive)
    essOpen (hasAt positive positive) lackOf := by
  intro h
  obtain ⟨y, C, ⟨-, -, rfl⟩, hEx⟩ :=
    h true ((rootIff true).2 rfl) .noesis noesisNotPositive' noesisExplained
  exact hEx pureSet positiveSubPure noesisPure pureOpen'

theorem reUnrep : RootLackReasonsEssential rootProfile true (unrepresented positive) essOpen
    (hasAt positive positive) lackOf :=
  fun _ _ _ _ ⟨_, hs⟩ => nomatch hs.2.2

theorem reExtendedPure : RootLackReasonsEssential rootProfile true (extended pureSet) essOpen
    (hasAt pureSet pureSet) lackOf :=
  lackReasonsEssentialOfExcluded _ _ _ _ _ _ xnPureOpen

theorem reExtendedNeg : RootLackReasonsEssential rootProfile true (extended positive) essNeg
    (hasAt positive positive) lackOf :=
  lackReasonsEssentialOfExcluded _ _ _ _ _ _ xnPositiveNeg

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
      ¬ AdmissibleIsExclusionFree openProfile aExcludesNoesis ∧ ¬ cE positive positive) :=
  ⟨⟨rootLackPSRExtended _, fun _ _ _ => Iff.rfl, reExtendedPure, leOpen _ _ _, mgNoReq,
      eOf _ _ subset_rfl⟩,
    ⟨notRootLackPSRBase, fun _ _ _ => Iff.rfl, reBase, leOpen _ _ _, mgNoReq, notEPositive _,
      notXNPositiveOpen⟩,
    ⟨rootLackPSRExtended _, fun _ _ _ => Iff.rfl, notREExtendedOpen, leOpen _ _ _, mgNoReq,
      notEPositive _⟩,
    ⟨rootLackPSRUnrep, notFactsUnrep, reUnrep, leOpen _ _ _, mgNoReq, notEPositive _⟩,
    ⟨rootLackPSRExtended _, fun _ _ _ => Iff.rfl, reExtendedNeg, notLENeg, mgNoReq,
      notEPositive _⟩,
    ⟨rootLackPSRExtended _, fun _ _ _ => Iff.rfl, reExtendedNeg, leCarried, notMGCarried,
      notEPositive _⟩⟩

/-! ### The rival with the full inquiry stance -/

theorem rivalRow :
    (extended positive).ontic = rootProfile.ontic ∧
    LackFactsRepresent (extended positive) (hasAt positive positive) lackOf ∧
    RootAbsencesNecessary rootProfile true (hasAt positive positive) ∧
    RootLackFactsAt rootProfile true (extended positive) (hasAt positive positive) lackOf ∧
    RootLackPSR rootProfile true (extended positive) lackOf ∧
    FactPSR (extended positive) true ∧ FactPSR (extended positive) false ∧
    Factive (extended positive) ∧ Distribution (extended positive) ∧
    IrreflexiveContingent (extended positive) ∧ ReasonIndependent (extended positive) ∧
    ContingentPSR (extended positive) true ∧ NoBrute (extended positive) true ∧
    TrackingBridge (extended positive) inquiry true ∧
    SupportCoverage (extended positive) inquiry true ∧
    EvidenceBridge (extended positive) inquiry true ∧
    GlobalDefeat (extended positive) inquiry true ∧
    GlobalDefeatUnreasoned (extended positive) inquiry true ∧
    NoBruteEvidenceAlternative (extended positive) inquiry true ∧
    Contingent (extended positive) true CFact.event ∧
    Supported inquiry true (lackOf true Determination.noesis) ∧
    Explained (extended positive) true (lackOf true Determination.noesis) ∧
    AdmissibleIsExclusionFree openProfile noReq ∧
    ¬ NoUnexplainedAbsenceAtRoots rootProfile true openProfile (hasAt positive positive true) ∧
    ¬ RootLackReasonsPositive rootProfile true (extended positive) openProfile noReq
      (hasAt positive positive) lackOf := by
  have hExt := cheapExtension (base positive) inquiry true
  have hF : ∀ v, FactPSR (extended positive) v := extendedFactPSR positive
  have hC : ContingentPSR (extended positive) true := fun f hc => hF true f hc.1
  refine ⟨rfl, fun _ _ _ => Iff.rfl, nOf _ _ subset_rfl, fun _ _ _ => Iff.rfl,
    rootLackPSRExtended _, hF true, hF false,
    hExt.2.2.2.1 (baseFactive _ limiterNotPositive),
    hExt.2.2.2.2.2.1 (baseConjunctSound _) (baseDistribution _),
    hExt.2.2.2.2.2.2.1 (baseIrreflexive _),
    hExt.2.2.2.2.2.2.2 (baseIndependent _ limiterNotPositive),
    hC, fun ⟨f, hc, hn⟩ => hn (hC f hc), fun f hc _ => hC f hc, ?_,
    fun _ _ _ hc => hC _ hc, ?_, ?_,
    noBruteAlternativeOfPSR _ _ _ fun v _ f hc => hF v f hc.1,
    eventContingent positive, ⟨.event, rfl, rfl, Or.inr rfl⟩, noesisExplained, mgNoReq,
    notEPositive _, notBridgeRival⟩
  · intro f hc
    obtain ⟨-, rfl⟩ := baseContingent (src := positive) hc
    exact ⟨.event, rfl, rfl, Or.inl rfl⟩
  · rintro ⟨v, f, -, hc, hn⟩
    exact absurd (hF v f hc.1) hn
  · rintro ⟨v, f, -, hf, hn⟩
    exact absurd (hF v f hf) hn

theorem baseRow :
    ContingentPSR (base positive) true ∧ NoBrute (base positive) true ∧
    TrackingBridge (base positive) inquiry true ∧ SupportCoverage (base positive) inquiry true ∧
    EvidenceBridge (base positive) inquiry true ∧ GlobalDefeat (base positive) inquiry true ∧
    NoBruteEvidenceAlternative (base positive) inquiry true ∧
    ReasonIndependent (base positive) ∧ IrreflexiveContingent (base positive) ∧
    ¬ RootLackPSR rootProfile true (base positive) lackOf ∧ ¬ FactPSR (base positive) true := by
  obtain ⟨hB, hRI, hIC⟩ :=
    blindness (base positive) inquiry _ (cheapExtension (base positive) inquiry true).1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB true
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hRI', hC, hN, hT, hS, hE, hG, -, hNB, -⟩ := rivalRow
  exact ⟨h1.2 hC, h2.2 hN, h3.2 hT, h4.2 hS, h5.2 hE, h6.2 hG, h7.2 hNB,
    baseIndependent _ limiterNotPositive, baseIrreflexive _, notRootLackPSRBase,
    fun h => notRootLackPSRBase (rootLackPSROfFactPSR _ _ _ _ h)⟩

end Controls

/-! ## The certificate -/

/-- **What the inquiry family reaches at a root, and what would carry it to E**
(`InquiryScopeMap`). -/
theorem inquiryScopeMap : InquiryScopeMap :=
  ⟨fun _ _ _ A I e h => blindness A I e h, factPSRNotInvariant,
    fun _ _ _ A w e p hp => necessaryNoBruteAlternative A w e p hp,
    fun _ _ _ A I w hP => noBruteAlternativeOfPSR A I w hP,
    fun _ _ _ A I w => cheapExtension A I w,
    fun _ _ _ A w r f hEM hF hI hx hn => independentReasonContingent A w r f hEM hF hI hx hn,
    fun _ _ _ A w f hEM hP hF hI hf hno => independentFactPSRContingency A w f hEM hP hF hI hf hno,
    fun _ _ _ _ m A w HasAt lack hO hRep hN r hr d hLack =>
      rootLacksNecessary m A w HasAt lack hO hRep hN r hr d hLack,
    fun _ _ _ _ m A w Adm Ess HasAt lack hO hRep hEM hEP hC r hr d hU =>
      contingentBranch m A w Adm Ess HasAt lack hO hRep hEM hEP hC r hr d hU,
    fun _ _ _ _ m A w Adm Ess R HasAt lack hRE hLE hMG =>
      factorization m A w Adm Ess R HasAt lack hRE hLE hMG,
    fun _ _ _ _ m I w Adm HasAt lack hS => epistemicReading m I w Adm HasAt lack hS,
    fun _ _ _ m w Adm R HasAt Pure hImp hPure r hr d hP =>
      referenceClass m w Adm R HasAt Pure hImp hPure r hr d hP,
    rivalRow, baseRow⟩

end TruthCore.Results.Explanation.InquiryClosure
