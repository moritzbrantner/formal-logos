module

public import TruthCore.Latin.Aquinas.DeEnte.IdentitySupplierSingleton
public import TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Solution

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.IdentitySourceCycle

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
open TruthCore.Latin.Aquinas.DeEnte.IdentitySupplierSingleton
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile DistinctEsseAt)
open TruthCore.Logic (ExcludedMiddle)

variable {B P R : Type}

/-- The ordinary uniqueness premise bounds each recipient's identity ancestors
even when the recipient has infinitely many other ancestors. -/
theorem finiteIdentityAncestorsOfUniqueness (p : Profile B P R)
    (one : AtMostOneEsseIsEssence p) : ActualIdentityAncestorSetsFinite p := by
  intro x _
  apply Set.Subsingleton.finite
  intro a ha b hb
  exact one a b ha.1 hb.1 ha.2.1 hb.2.1

/-- Select an identity bearer from one actual bearer, then identify every
incoming supplier as a point on a forbidden return path. -/
theorem commonSourceOfNoIdentityReturn (p : Profile B P R)
    (ancestry : EveryDistinctEsseHasEsseIsEssenceSource p)
    (one : AtMostOneEsseIsEssence p) (population : ActualEssePopulation p)
    (noReturn : ActualIdentityAncestryAcyclic p) (em : ExcludedMiddle) :
    CommonEsseIsEssenceSource p := by
  obtain ⟨x, actual⟩ := population
  have candidate : ∃ n, p.InAct n p.esse ∧ p.esseOf n = p.essenceOf n := by
    rcases em (p.esseOf x = p.essenceOf x) with identity | distinct
    · exact ⟨x, actual, identity⟩
    · obtain ⟨n, hn, hi, _⟩ := ancestry x ⟨actual, distinct⟩
      exact ⟨n, hn, hi⟩
  obtain ⟨n, hn, identity⟩ := candidate
  have reaches : ∀ y, p.InAct y p.esse → y ≠ n → Relation.TransGen (ActualEsseCause p) n y := by
    intro y hy different
    have distinct : DistinctEsseAt p y := ⟨hy, fun eq => different (one y n hy hn eq identity)⟩
    obtain ⟨a, ha, hi, path⟩ := ancestry y distinct
    exact one a n ha hn hi identity ▸ path
  refine ⟨n, hn, identity, ?_, reaches⟩
  intro c edge
  exact noReturn n hn identity ((reaches c edge.2.1 edge.1).tail edge)

/-- Under uniqueness, every return would end in a supplier edge into the very
bearer whose incoming supply the common-source conclusion excludes. -/
theorem noIdentityReturnOfCommonSource (p : Profile B P R)
    (one : AtMostOneEsseIsEssence p) (source : CommonEsseIsEssenceSource p) :
    ActualIdentityAncestryAcyclic p := by
  obtain ⟨n, hn, identity, first, _⟩ := source
  intro r hr hi loop
  obtain rfl := one r n hr hn hi identity
  rcases loop with last | ⟨_, last⟩ <;> exact first _ last

/-- The existing rooted infinite profile satisfies all the application
premises while failing unrestricted well-foundedness. -/
theorem commonSourceWithEndlessBranch (em : ExcludedMiddle) :
    ∃ p : Profile (Option Nat) Bool Unit, EveryDistinctEsseHasEsseIsEssenceSource p ∧
      AtMostOneEsseIsEssence p ∧ ActualEssePopulation p ∧ ActualIdentityAncestryAcyclic p ∧
      CommonEsseIsEssenceSource p ∧ ¬ NoInfiniteActualEsseCauseRegress p := by
  obtain ⟨p, closed, other, one, two, source, endless⟩ :=
    TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Control.rootedInfinite
  exact ⟨p, TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.distinctSourceOfClosed p closed other em,
    one, TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.populationOfTwo p two,
    noIdentityReturnOfCommonSource p one source, source, endless⟩

/-- One value of represented essence and one successor law are compatible
with infinitely many actual identity ancestors of the same distinct
recipient, with incoming supply at each identity and no root. -/
theorem identitySupplierSingletonCountermodel : SingletonEssenceValueWithInfiniteIdentitySuppliers := by
  let p : Profile Nat Bool Unit :=
    { TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource.tailAtState (fun _ => True) with
      essenceOf := fun
        | 0 => false
        | _ + 1 => true }
  have actual (x : Nat) : p.InAct x p.esse := trivial
  have distinct : DistinctEsseAt p 0 := ⟨actual 0, Bool.noConfusion⟩
  have law (c x : Nat) : ActualEsseCause p c x ↔ c = x + 1 := by
    refine ⟨fun edge => edge.2.2.2, ?_⟩
    rintro rfl
    exact ⟨Nat.succ_ne_self x, actual (x + 1), actual x, rfl⟩
  have step (x : Nat) : ActualEsseCause p (x + 1) x := (law _ _).mpr rfl
  have identity (x : Nat) : p.esseOf (x + 1) = p.essenceOf (x + 1) := rfl
  have onlyZero (x : Nat) (h : DistinctEsseAt p x) : x = 0 := by
    cases x with
    | zero => rfl
    | succ n => exact False.elim (h.2 (identity n))
  refine ⟨p, actual, distinct, law, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨true, Set.ext fun v => ?_⟩
    constructor
    · rintro ⟨x, _, hx, rfl⟩
      exact hx.symm
    · intro hv
      have equal : v = true := hv
      subst v
      exact ⟨1, actual 1, identity 0, rfl⟩
  · have reachesZero (x : Nat) : Relation.ReflTransGen (ActualEsseCause p) x 0 := by
      induction x with
      | zero => exact .refl
      | succ n ih => exact ih.head (step n)
    exact Set.infinite_of_injective_forall_mem Nat.succ_injective
      (fun n => ⟨actual (n + 1), identity n, reachesZero (n + 1)⟩)
  · intro r _ _ loop
    have decreases : ActualEsseCause p ≤ (fun (c x : Nat) => x < c) := by
      intro c x edge
      rw [(law c x).mp edge]
      exact Nat.lt_succ_self x
    exact Nat.lt_irrefl r (Relation.transGen_minimal decreases r r loop)
  · intro x hx
    obtain rfl := onlyZero x hx
    exact ⟨1, actual 1, identity 0, .single (step 0)⟩
  · intro audited
    obtain ⟨r, _, auditedNodes, _, knows⟩ := audited 0 (actual 0)
    have ancestor := knows (ActualEsseCause p)
      (TruthCore.Causality.SupplierAudit.auditFrameReflexive id auditedNodes (ActualEsseCause p))
    exact ancestor.2 (r + 1) (step r)
  · rintro ⟨r, _, _, root, _⟩
    exact root (r + 1) (step r)

end TruthCore.Results.Aquinas.DeEnte.IdentitySourceCycle
