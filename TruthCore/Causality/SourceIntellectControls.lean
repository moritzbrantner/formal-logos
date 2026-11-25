module

public import Mathlib.Order.WellFounded
public import TruthCore.Causality.ParticipatedEsseScale
public import TruthCore.Results.Causality.IntentionalExemplarExtension.Solution

/-!
# Structural controls for source-level understanding

Analyst comparisons from #1970. The selected rule, admitted profiles and
knowledge edges are interpreted as indicated below. The controls give logical
consequences of those interpretations and leave their applicability to an
unreceived source open.
-/

@[expose] public section

namespace TruthCore.Causality.SourceIntellectControls

namespace ContentSelection

open WholePowerPerfection.WisdomSelfUnderstanding (IntrinsicSelfKnowledge)
open IntentionalExemplarExtension.ObjectiveEminence
  (IntrinsicExemplarEminence ProducesActualKnower)
open IntentionalExemplarExtension.Control (frame rootProfile about correct)
open TruthCore.Results.Causality.IntentionalExemplarExtension.ImmanentSelfPresence.Control
  (own ownForm primarySelf)
open TruthCore.Results.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control
  (hasOwnForm)
open NecessaryRootFork (ActualRoot ActualConcrete)

/-- A content identifies its subject matter and one of two truths about it.
Only the first component enters the inherited truth and aboutness tests. -/
abbrev Content := Bool × Bool

def apprehends (mode rule : Bool) (owned enabled noesis : Prop)
    (bearer : Bool) (c : Content) : Prop :=
  if bearer then noesis ∧ c = (true, false)
  else enabled ∧ c.1 = false ∧ (owned → c.2 = mode) ∧ (¬ owned → c.2 = rule)

/-- At the stipulated recipient, an owned specification selects the own mode.
In its absence, the separately supplied rule selects the content. -/
theorem recipientContent {mode rule : Bool} {owned enabled noesis : Prop}
    [Decidable owned] (c : Content) :
    apprehends mode rule owned enabled noesis false c ↔
      enabled ∧ c = (false, if owned then mode else rule) := by
  by_cases h : owned <;> simp [apprehends, h, Prod.ext_iff]

/-- From the all-false selector baseline, changing the own mode reaches the
second truth exactly in the owned branch; changing the separate rule reaches
it in the other branch. With exercise withheld, the recipient grasps neither.
“Changing” identifies a contrast between descriptions of the dependency. -/
theorem recipientDependence (owned noesis : Prop) [Decidable owned] :
    apprehends false false owned True noesis false (false, false) ∧
    (apprehends true false owned True noesis false (false, true) ↔ owned) ∧
    (apprehends false true owned True noesis false (false, true) ↔ ¬ owned) ∧
    (∀ mode rule c, ¬ apprehends mode rule owned False noesis false c) := by
  by_cases h : owned <;> simp [recipientContent, h]

/-- Root mode and recipient enabling do not fix actual source uptake. -/
theorem sourceContent {mode rule : Bool} {owned enabled noesis : Prop}
    (c : Content) :
    apprehends mode rule owned enabled noesis true c ↔ noesis ∧ c = (true, false) := by
  simp [apprehends]

/-- This objective norm uses the very mode that selects the recipient's
content. It is separate from the source's own truth-grasping operation. -/
def norms (mode : Bool) (owned : Prop) (g form x : Bool) (c : Content) : Prop :=
  own g ∧ form = ownForm g ∧ x = false ∧ c = (false, mode) ∧ owned

/-- Every selected output passes the stipulated aboutness/truth tests. Each
bearer's successful uptake is assigned its own cognitive grounding, as in
the original diagnostic. These assignments explain neither truth nor basing. -/
theorem selectedContentProfiles (mode rule : Bool) (owned enabled noesis : Prop)
    [Decidable owned] :
    let uptake := apprehends mode rule owned enabled noesis
    let cause := fun g x => frame.CausesIn g x frame.esse
    let aboutContent := fun c : Content => about c.1
    let correctContent := fun c : Content => correct c.1
    let knows := IntrinsicSelfKnowledge aboutContent correctContent uptake uptake
    (ActualRoot rootProfile true true ∧ ActualConcrete rootProfile true false ∧
      (true : Bool) ≠ false) ∧ cause true false ∧
    (∀ x c, uptake x c → aboutContent c x ∧ correctContent c x) ∧
    (knows false ↔ enabled) ∧ (knows true ↔ noesis) ∧
    (ProducesActualKnower cause aboutContent correctContent uptake uptake true ↔ enabled) ∧
    (IntrinsicExemplarEminence own ownForm hasOwnForm primarySelf
      (norms mode owned) cause aboutContent correctContent uptake uptake true ↔
        enabled ∧ owned) := by
  simp only
  have hRecipient := @recipientContent mode rule owned enabled noesis _
  have hSource := @sourceContent mode rule owned enabled noesis
  simp [IntrinsicExemplarEminence, ProducesActualKnower, IntrinsicSelfKnowledge,
    hRecipient, hSource, ActualRoot, ActualConcrete,
    TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround,
    frame, rootProfile, about, correct, own, ownForm, hasOwnForm, primarySelf, norms,
    TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.causesIn,
    Bool.forall_bool]
  by_cases h : owned <;> cases mode <;> cases rule <;> simp_all

/-- In the two-slot inventory, each bearer has esse, and its only further
selected pure-candidate determination is its own grounded understanding.
With actual recipient cognition, inclusion is equivalent to source uptake. -/
theorem selectedInclusionIffSourceUptake (mode rule : Bool) (owned noesis : Prop)
    [Decidable owned] :
    let uptake := apprehends mode rule owned True noesis
    let knows := IntrinsicSelfKnowledge (fun c : Content => about c.1)
      (fun c : Content => correct c.1) uptake uptake
    let has := fun bearer knowledgeSlot : Bool => knowledgeSlot = false ∨ knows bearer
    (∀ d, has false d → has true d) ↔ noesis := by
  have hProfiles := selectedContentProfiles mode rule owned True noesis
  simp only at hProfiles ⊢
  simp [Bool.forall_bool, hProfiles.2.2.2.1, hProfiles.2.2.2.2.1]


end ContentSelection

/-- The epistemic content is realized by the same bearer that has the
determination. The preservation premise requires the same positive content,
without identifying the two apprehended truths, acts or subjects. -/
theorem subjectGroundedApprehensionPreserved
    {B P R D C : Type} (q : EsseCauseEfficiency.EfficiencyProfile B P R)
    (Participated : B → Prop) (Total : B → B → R → Prop)
    (Pure : D → Prop) (Has : B → D → Prop) (k : D)
    (Correct : C → B → Prop) (Apprehends Grounded : B → C → Prop)
    (hRealization : ∀ b, Has b k ↔ ∃ c, Correct c b ∧ Apprehends b c ∧ Grounded b c)
    (hPreserve : ParticipatedEsseScale.GivingPreservesDeterminations
      q Participated Total Pure Has)
    {g x : B} (hActual : q.InAct x q.esse) (hParticipated : Participated x)
    (hGives : q.EfficientlyCausesEsse g x) (hTotal : Total g x q.esse)
    (hPure : Pure k) (hUptake : ∃ c, Correct c x ∧ Apprehends x c ∧ Grounded x c) :
    ∃ c, Correct c g ∧ Apprehends g c ∧ Grounded g c :=
  (hRealization g).mp
    (hPreserve g x hActual hParticipated hGives hTotal k hPure ((hRealization x).mpr hUptake))


section Profiles

variable {Determination : Type}

/-- A compatible completion retains every positive requirement and has the
listed determination. The family specifies the scope of compatibility. -/
def HasCompatibleExtension (admitted : Set Determination → Prop)
    (positive : Set Determination) (target : Determination) : Prop :=
  ∃ profile, admitted profile ∧ positive ⊆ profile ∧ target ∈ profile

theorem exclusionIffNoCompatibleExtension (admitted : Set Determination → Prop)
    (positive : Set Determination) (target : Determination) :
    (∀ profile, admitted profile → positive ⊆ profile → target ∉ profile) ↔
      ¬ HasCompatibleExtension admitted positive target := by
  constructor
  · rintro h ⟨profile, hp, hContains, hTarget⟩
    exact h profile hp hContains hTarget
  · intro h profile hp hContains hTarget
    exact h ⟨profile, hp, hContains, hTarget⟩

/-- The narrower conditional fullness step: if an omission must be fixed
by the compared requirements, one compatible completion rules it out. -/
theorem possessedIfCompatibleAndOmissionFixed
    (admitted : Set Determination → Prop) (positive : Set Determination)
    (target : Determination) (hCompatible : HasCompatibleExtension admitted positive target)
    (hOmission : target ∉ positive →
      ∀ profile, admitted profile → positive ⊆ profile → target ∉ profile) :
    target ∈ positive := by
  by_contra h
  exact (exclusionIffNoCompatibleExtension admitted positive target).mp
    (hOmission h) hCompatible

end Profiles

namespace ProfileControls

inductive Determination
  | esse | a | b | noesis | limiter
  deriving DecidableEq

open Determination

def pure : Set Determination := {esse, a, b, noesis}
def positive : Set Determination := {esse, a, b}
def effect : Set Determination := {esse, noesis}

def openProfile (p : Set Determination) : Prop :=
  esse ∈ p ∧ limiter ∉ p

def finiteMode (p : Set Determination) : Prop :=
  esse ∈ p ∧ ¬ (limiter ∈ p ∧ noesis ∈ p)

def jointConflict (p : Set Determination) : Prop :=
  openProfile p ∧ ¬ (a ∈ p ∧ b ∈ p ∧ noesis ∈ p)

def exactClosure (p : Set Determination) : Prop := p = positive

/-- Each pure pair can use its own witness; this does not provide a
simultaneous witness for all the source requirements and noesis. -/
def PairwiseAdmitted (admitted : Set Determination → Prop) : Prop :=
  ∀ x ∈ pure, ∀ y ∈ pure, ∃ p, admitted p ∧ x ∈ p ∧ y ∈ p

theorem jointConflictPairwise : PairwiseAdmitted jointConflict := by
  intro x hx y hy
  refine ⟨{esse, x, y}, ?_, by simp, by simp⟩
  cases x <;> cases y <;> simp_all [jointConflict, openProfile, pure]

/-- The four original comparisons, with one fixed actual role assignment
understood throughout. The profile constraints are imposed on the source's
selected features and do not define causal or epistemic sufficiency. -/
theorem profileComparisons :
    effect ⊆ pure ∧ noesis ∉ positive ∧
    (openProfile positive ∧ positive ⊆ pure ∧ PairwiseAdmitted openProfile ∧
      HasCompatibleExtension openProfile positive noesis) ∧
    (finiteMode (insert limiter positive) ∧ ¬ (insert limiter positive ⊆ pure) ∧
      PairwiseAdmitted finiteMode ∧
      ¬ HasCompatibleExtension finiteMode (insert limiter positive) noesis) ∧
    (jointConflict positive ∧ positive ⊆ pure ∧ PairwiseAdmitted jointConflict ∧
      ¬ HasCompatibleExtension jointConflict positive noesis) ∧
    (exactClosure positive ∧ positive ⊆ pure ∧ ¬ PairwiseAdmitted exactClosure ∧
      ¬ HasCompatibleExtension exactClosure positive noesis) := by
  have hPure : positive ⊆ pure := by
    intro d hd
    cases d <;> simp_all [positive, pure]
  have hEffect : effect ⊆ pure := by
    intro d hd
    cases d <;> simp_all [effect, pure]
  have hPair : ∀ admitted : Set Determination → Prop,
      (∀ p, jointConflict p → admitted p) → PairwiseAdmitted admitted := by
    intro admitted h x hx y hy
    obtain ⟨p, hp, hxp, hyp⟩ := jointConflictPairwise x hx y hy
    exact ⟨p, h p hp, hxp, hyp⟩
  refine ⟨hEffect, by simp [positive],
    ⟨by simp [openProfile, positive], hPure, hPair _ (fun _ h => h.1),
      ⟨pure, by simp [openProfile, pure], hPure, by simp [pure]⟩⟩,
    ⟨by simp [finiteMode, positive], ?_, hPair _ (fun _ h =>
        ⟨h.1.1, fun hi => h.1.2 hi.1⟩), ?_⟩,
    ⟨by simp [jointConflict, openProfile, positive], hPure, jointConflictPairwise, ?_⟩,
    ⟨rfl, hPure, ?_, ?_⟩⟩
  · intro h
    have := h (show limiter ∈ insert limiter positive by simp)
    simp [pure] at this
  · rintro ⟨p, hp, hContains, hNoesis⟩
    exact hp.2 ⟨hContains (by simp), hNoesis⟩
  · rintro ⟨p, hp, hContains, hNoesis⟩
    exact hp.2 ⟨hContains (by simp [positive]), hContains (by simp [positive]), hNoesis⟩
  · intro hPairwise
    obtain ⟨_, rfl, _, h⟩ :=
      hPairwise esse (by simp [pure]) noesis (by simp [pure])
    simp [positive] at h
  · rintro ⟨_, rfl, _, h⟩
    simp [positive] at h

end ProfileControls

section ActMediation

variable {Act : Type}

/-- Both role arrows lift to a single strict relation on the real tokens
exactly when neither prior role denotes the act itself. No distinctness of
the subject and object from each other is required. -/
theorem roleLiftIff (subject act object : Act) :
    (∃ prior : Act → Act → Prop, (∀ x, ¬ prior x x) ∧
      (∀ x y z, prior x y → prior y z → prior x z) ∧
      prior subject act ∧ prior object act) ↔
    subject ≠ act ∧ object ≠ act := by
  constructor
  · rintro ⟨prior, hIrrefl, _, hSubject, hObject⟩
    exact ⟨fun eq => hIrrefl act (eq ▸ hSubject), fun eq => hIrrefl act (eq ▸ hObject)⟩
  · rintro ⟨hSubject, hObject⟩
    let prior : Act → Act → Prop := fun x y => (x = subject ∨ x = object) ∧ y = act
    have irrefl (x : Act) : ¬ prior x x := by
      rintro ⟨hx, rfl⟩
      exact hx.elim (fun h => hSubject h.symm) (fun h => hObject h.symm)
    refine ⟨prior, irrefl, ?_, ⟨Or.inl rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩⟩
    intro x y z hxy hyz
    exact ⟨hxy.1, hyz.2⟩

/-- Complete coverage supplies an actual apprehending act for every act in
the selected roster. Its factivity and cognitive grounding are intended
conditions on the input relation, not consequences of graph structure. -/
def CompleteActCoverage (knows : Act → Act → Prop) : Prop :=
  ∀ a, ∃ b, knows a b

theorem coverageExcludesMediationAtMaximal (knows prior : Act → Act → Prop)
    (hCoverage : CompleteActCoverage knows) (maximal : Act)
    (hMaximal : ∀ b, ¬ prior maximal b) :
    ¬ (∀ a b, knows a b → prior a b) := by
  intro hMediation
  obtain ⟨b, hb⟩ := hCoverage maximal
  exact hMaximal b (hMediation maximal b hb)

/-- Absence of infinite ascending priority is enough. The reversal of
priority is essential: predecessor well-foundedness gives no such result. -/
theorem coverageExcludesAscendingWellFoundedMediation [Nonempty Act]
    (knows prior : Act → Act → Prop) (hCoverage : CompleteActCoverage knows)
    (hWF : WellFounded (fun a b => prior b a)) :
    ¬ (∀ a b, knows a b → prior a b) := by
  intro hMediation
  obtain ⟨initial⟩ := ‹Nonempty Act›
  induction hWF.apply initial with
  | intro a _ ih =>
    obtain ⟨b, hb⟩ := hCoverage a
    exact ih b (hMediation a b hb)

theorem coverageExcludesFiniteStrictMediation [Finite Act] [Nonempty Act]
    (knows prior : Act → Act → Prop) (hCoverage : CompleteActCoverage knows)
    (hIrrefl : ∀ a, ¬ prior a a)
    (hTrans : ∀ a b c, prior a b → prior b c → prior a c) :
    ¬ (∀ a b, knows a b → prior a b) := by
  let reverse : Act → Act → Prop := fun a b => prior b a
  let : Std.Irrefl reverse := ⟨hIrrefl⟩
  let : IsTrans Act reverse := ⟨fun a b c hab hbc => hTrans c b a hbc hab⟩
  exact coverageExcludesAscendingWellFoundedMediation knows prior hCoverage
    (Finite.wellFounded_of_trans_of_irrefl reverse)

/-- Every finite nonempty coverage graph contains a cycle, regardless of
whether anyone interprets its edges as strict ontic priority. -/
theorem completeFiniteCoverageHasCycle [Finite Act] [Nonempty Act]
    (knows : Act → Act → Prop) (hCoverage : CompleteActCoverage knows) :
    ∃ a, Relation.TransGen knows a a := by
  by_contra h
  have hirr (a : Act) : ¬ Relation.TransGen knows a a := fun ha => h ⟨a, ha⟩
  exact coverageExcludesFiniteStrictMediation knows (Relation.TransGen knows)
    hCoverage hirr (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ => Relation.TransGen.single)

theorem soleActApprehendsItself [Subsingleton Act] (knows : Act → Act → Prop)
    (hCoverage : CompleteActCoverage knows) (act : Act) : knows act act := by
  obtain ⟨b, hb⟩ := hCoverage act
  exact Subsingleton.elim b act ▸ hb

/-- One act can cover itself with empty strict priority; a two-act monitor
can have strict priority and omit itself; two acts can give cyclic coverage.
These are assignments of the selected relations, with grounded cognition
understood in each selected knowledge edge. -/
theorem finiteMediationControls :
    (CompleteActCoverage (fun _ _ : Unit => True) ∧
      ¬ (∀ _ _ : Unit, True → False)) ∧
    ((∃ a b : Bool, a = false ∧ b = true) ∧
      ¬ CompleteActCoverage (fun a b : Bool => a = false ∧ b = true)) ∧
    (CompleteActCoverage (fun a b : Bool => a ≠ b) ∧
      Relation.TransGen (fun a b : Bool => a ≠ b) false false) := by
  refine ⟨⟨fun _ => ⟨(), trivial⟩, fun h => h () () trivial⟩,
    ⟨⟨false, true, rfl, rfl⟩, ?_⟩, ⟨fun a => ⟨!a, by cases a <;> decide⟩, ?_⟩⟩
  · intro h
    obtain ⟨_, ha, _⟩ := h true
    cases ha
  · exact (Relation.TransGen.single (b := true) (by decide)).tail (by decide)

/-- An infinite roster supports strict mediation on every edge, even with
well-foundedness in the ordinary predecessor direction. -/
theorem infiniteMediationControl :
    CompleteActCoverage (fun a b : Nat => a < b) ∧
      WellFounded (fun a b : Nat => a < b) :=
  ⟨fun a => ⟨a + 1, Nat.lt_succ_self a⟩, Nat.lt_wfRel.wf⟩

end ActMediation

end TruthCore.Causality.SourceIntellectControls
