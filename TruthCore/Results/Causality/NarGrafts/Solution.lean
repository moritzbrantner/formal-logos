module

public import TruthCore.Causality.NarGrafts
public import TruthCore.Causality.NecessaryRootUniqueness

/-! Two grafts onto the NAR/WN route of #1947 (#1926 orphan grafts). (G1) The
optimizing-creator rival to WN (a root that gives by total optimal output with a
unique optimum) is refuted by the premises of #1947's law 2 together with
#1737's `OptimalChoiceCertificate`: a unique optimum makes the root fixed toward
every being it gives, while law 2 makes it two-way toward a contingent one.
(G2) Necessary roots (`d164f730`) from the unique necessary actual root
(`91b085c4`). Analyst reconstructions; attribution deferred. -/

@[expose] public section

namespace TruthCore.Results.Causality.NarGrafts
open TruthCore.Causality.NarGrafts
open TruthCore.Causality.NarGrafts.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)
open TruthCore.Causality.NecessaryRootUniqueness (UniqueNecessaryActualRootAt)
open TruthCore.Causality.NarDerivation (FixedTowardAt TwoWayTowardAt
  ActualRootsGiveGroundedHere ActualRootsNecessary RationalFixedGivingIsRequired
  ActualRootsEndRequiresNoOther)
open TruthCore.Causality.WillVersusChance (AgencyFrame)
open TruthCore.Modal.ModalGrounding (SomeContingentConcreteAt)
open TruthCore.Modal.PrussPowerPremises (GivesTo GivenExists)
open TruthCore.Modal.PrussPowerPremises.Model (Bg Bg.forall_iff Bg.exists_iff gFrame allC uni)
open TruthCore.Causality.HolderRootIdentification.Model (gGroundsOthers dThereEx)
open TruthCore.Causality.WillVersusChance.Model (onlyG)
open TruthCore.Modal.SelectedEffectBridge (OutputProfile StableActOutput)
open TruthCore.Modal.OptimalCreationChoice (Optimal OptimalOutputs OptimalChoiceCertificate)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)

/-- Law 1: under the adapter, stability is fixity toward every given being. -/
theorem stable_iff_fixed {W B T R : Type} (F : CausalityFrame W B T R) (w : W) (y : B) :
    StableActOutput (givingProfile F y) w () ↔ ∀ x, GivesTo F w y x → FixedTowardAt F w y x := by
  constructor
  · intro h x hx
    exact ⟨hx, fun v hv hyv => h x hx v hv hyv⟩
  · intro h x hx v hv hyv
    exact (h x hx).2 v hv hyv

/-- A unique optimum makes an actual root fixed toward every being it gives at
`w`, using the first conjunct of #1737's certificate. -/
theorem fixed_of_uniqueOptimum {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W) (V : Type) [PartialOrder V]
    (feasible : Set B) (quality : B → V) (hCert : OptimalChoiceCertificate)
    (hOpt : ActualRootsGiveUniqueOptimum F concrete G w V feasible quality)
    (n : B) (hn : ActualRoot (groundProfile F concrete G) w n) :
    ∀ x, GivesTo F w n x → FixedTowardAt F w n x := by
  obtain ⟨hOut, hUniq⟩ := hOpt n hn
  have hStable : StableActOutput (givingProfile F n) w () :=
    hCert.1 W B Unit V (givingProfile F n) w () feasible quality hOut hUniq
  exact (stable_iff_fixed F w n).1 hStable

/-- Argument G1: the optimizing-creator rival is refuted by the premises of
#1947's law 2 (taken from #1947's certificate `b8ee1a50`) and #1737's
certificate. The common GOD_4 root of `0c27f65a` (only
its root and reach clauses are used) is an actual root; by law 2 it is two-way
toward some concrete contingent `c`: it gives `c` being at `w` and not at some
accessible `v` where it exists. A unique optimum with total optimal output makes
it fixed toward `c`, so it gives `c` being at `v`: contradiction.
Constructive. -/
theorem optimalRivalRefuted {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop) (w : W)
    (V : Type) [PartialOrder V] (feasible : Set B) (quality : B → V)
    (hB : ActualRootsGiveGroundedHere F concrete G w) (hGE : GivenExists F)
    (hIG : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (hNec : ActualRootsNecessary F concrete G w) (hSome : SomeContingentConcreteAt F concrete w)
    (hCert : OptimalChoiceCertificate)
    (hNar : TruthCore.Causality.NarDerivation.Model.Controls) :
    NotEveryActualRootGivesUniqueOptimum F concrete G w V feasible quality := by
  intro hOpt
  have hCommon := TruthCore.Results.Causality.NarDerivation.commonRoot_of_intellectual _ w
    IsGod HasIntellect hIG
  obtain ⟨n, hn, _⟩ := id hCommon
  obtain ⟨c, _, _, _, hgc, v, hv, hnv, hng⟩ :=
    hNar.1.2.1 W B T R F concrete G w hB hGE hCommon hNec hSome n hn
  exact hng ((fixed_of_uniqueOptimum F concrete G w V feasible quality hCert hOpt n hn c hgc).2
    v hv hnv)

/-- Argument G2: necessary roots (`d164f730`) from the unique necessary actual
root (`91b085c4`): every actual root is that root, which is NECESSARY_2.
Constructive. -/
theorem necessaryRootsFromUniqueNecessaryRoot {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hU : UniqueNecessaryActualRootAt (groundProfile F concrete G) w) :
    ActualRootsNecessary F concrete G w := by
  intro m hm
  obtain ⟨n, _, hnec, huniq⟩ := hU
  rw [huniq m hm]
  exact hnec

theorem laws : Laws := by
  refine ⟨?_, ?_, ?_⟩
  · intro W B T R F w y
    exact stable_iff_fixed F w y
  · intro W B T R F concrete G w V _ feasible quality hOpt n hn
    have hFix := fixed_of_uniqueOptimum F concrete G w V feasible quality
      TruthCore.Results.Modal.OptimalCreationChoice.checks hOpt n hn
    refine ⟨hFix, fun x hx => ?_⟩
    obtain ⟨_, hgx, v, hv, hnv, hng⟩ := hx
    exact hng ((hFix x hgx).2 v hv hnv)
  · intro W B T R S P F A concrete G EndRequires w V _ feasible quality hOpt hSS hEx hWN
    obtain ⟨n, p, x, hn, hxn, hp, hr, hex, hgx⟩ := hEx
    have hFix := fixed_of_uniqueOptimum F concrete G w V feasible quality
      TruthCore.Results.Modal.OptimalCreationChoice.checks hOpt n hn
    exact hSS n x hn hxn (hWN n p x hp hr hex (hFix x hgx))

theorem tiedOptimal_c : Optimal tiedFeasible tiedQuality .c := by
  refine ⟨Or.inl rfl, ⟨⟨.c, Or.inl rfl, rfl⟩, ?_⟩⟩
  rintro _ ⟨y, _, rfl⟩
  exact Nat.le_refl 0

theorem tiedOptimal_d : Optimal tiedFeasible tiedQuality .d := by
  refine ⟨Or.inr rfl, ⟨⟨.d, Or.inr rfl, rfl⟩, ?_⟩⟩
  rintro _ ⟨y, _, rfl⟩
  exact Nat.le_refl 0

theorem tiedOptimum : TiedOptimum := by
  unfold TiedOptimum
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, tiedOptimal_c, tiedOptimal_d, ?_, ?_⟩
  · simp [ActualRootsGiveGroundedHere, ActualRoot, ActualConcrete, ActualConcreteGround,
      groundProfile, GivesTo, tiedG, gFrame, tiedGives, dThereEx, gGroundsOthers, allC,
      Bg.forall_iff]
  · simp [GivenExists, GivesTo, tiedG, gFrame, tiedGives, dThereEx, Bg.forall_iff]
  · simp [IntellectualGodCommonRootAt, ActualRoot, ActualConcrete, ActualConcreteGround,
      groundProfile, tiedG, gFrame, dThereEx, gGroundsOthers, allC, onlyG]
  · simp [ActualRootsNecessary, ActualRoot, ActualConcrete, ActualConcreteGround, NecessaryAt,
      groundProfile, tiedG, gFrame, dThereEx, gGroundsOthers, allC, uni,
      Bool.forall_bool]
  · simp [SomeContingentConcreteAt, ContingentAt, tiedG, gFrame, dThereEx, allC, uni,
      Bool.exists_bool]
  · intro v _
    refine ⟨fun hv => ?_, fun x hx => ?_⟩
    · cases v
      · exact ⟨.c, (), rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨.d, (), rfl, Or.inr ⟨rfl, rfl⟩⟩
    · obtain ⟨_, _, hx⟩ := hx
      rcases hx with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact tiedOptimal_c
      · exact tiedOptimal_d
  · simp [TwoWayTowardAt, GivesTo, tiedG, gFrame, tiedGives, dThereEx, uni]
  · intro h
    have hRoot : ActualRoot (groundProfile tiedG allC gGroundsOthers) false .g := by
      simp [ActualRoot, ActualConcrete, ActualConcreteGround, groundProfile, tiedG, gFrame,
        dThereEx, gGroundsOthers, allC]
    exact absurd ((h .g hRoot).2 .c .d tiedOptimal_c tiedOptimal_d) (by decide)

/-- Argument G3, the certificate of laws and the tied-optimum model.
Premise-free. -/
theorem narGraftControls : Controls := ⟨laws, tiedOptimum⟩

end TruthCore.Results.Causality.NarGrafts
