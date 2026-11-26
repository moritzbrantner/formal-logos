module

public import TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
public import TruthCore.Results.Aquinas.DeEnte.FiniteEsseRootAudit.Solution

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.ReceivedOrUnderived

open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Causality.EsseReception (NothingInReceptivePotencyToItself)
open TruthCore.Causality.FirstMoverNecessity (IdentityScopedEsseReception)
open TruthCore.Latin.Aquinas.DeEnte
  (ActualEsseCause EveryDistinctEsseHasEsseIsEssenceSource ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource (ClosedActualEsseCollectionsRooted sourceFreeFiniteCircle)
open TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit (EveryActualEsseBearerHasFiniteRootAudit)
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Results.Aquinas.DeEnte.FiniteEsseRootAudit (closedOfFiniteRootAudits)
open TruthCore.Results.Causality.SupplierAuditCertificates (positiveCertificate)

variable {B P R : Type}

/-- Causal origination would give internal reception. At identity, the
receiver would then stand in potency to the very same principle. -/
theorem identityEsseUnderivedOfReception (p : Profile B P R)
    (Received : B → P → Prop) (Potency : P → P → Prop)
    (caused : CausedEsseIsReceived p.CausesIn p.esse Received)
    (own : IdentityScopedEsseReception p.essenceOf p.esseOf Received)
    (receives : ReceiverInPotencyToReceivedEsseReading p.esseOf Received Potency)
    (irreflexive : NothingInReceptivePotencyToItself Potency) :
    ActualIdentityEsseHasNoSupplier p := by
  intro x _ identity c edge
  obtain ⟨z, receipt⟩ := caused c x edge.1 edge.2.2.2
  have self := receives x z receipt
  rw [own x z identity receipt, identity] at self
  exact irreflexive _ self

/-- Audit the identity bearer itself, or an actual identity ancestor and the
finite path named by the distinct-esse premise. -/
theorem auditsOfIdentityAncestry (p : Profile B P R)
    (underived : ActualIdentityEsseHasNoSupplier p)
    (ancestry : EveryDistinctEsseHasEsseIsEssenceSource p)
    (em : ExcludedMiddle) :
    EveryActualEsseBearerHasFiniteRootAudit p := by
  intro x actual
  rcases em (p.esseOf x = p.essenceOf x) with identity | distinct
  · exact ⟨x, actual, (positiveCertificate (ActualEsseCause p) x x).mp
      ⟨.refl, underived x actual identity⟩⟩
  · obtain ⟨r, actualRoot, identity, path⟩ := ancestry x ⟨actual, distinct⟩
    exact ⟨r, actualRoot, (positiveCertificate (ActualEsseCause p) r x).mp
      ⟨path.to_reflTransGen, underived r actualRoot identity⟩⟩

/-- A minimal identity ancestor has no incoming supplier. Any supplier is
itself an identity bearer or has an identity ancestor strictly before the
chosen one. -/
theorem auditsOfFiniteAcyclicIdentityAncestry (p : Profile B P R)
    (finite : ActualIdentityAncestorSetsFinite p)
    (acyclic : ActualIdentityAncestryAcyclic p)
    (ancestry : EveryDistinctEsseHasEsseIsEssenceSource p)
    (em : ExcludedMiddle) :
    EveryActualEsseBearerHasFiniteRootAudit p := by
  intro x actual
  have identityAncestor (y : B) (active : p.InAct y p.esse) :
      (actualIdentityAncestors p y).Nonempty := by
    rcases em (p.esseOf y = p.essenceOf y) with identity | distinct
    · exact ⟨y, active, identity, .refl⟩
    · obtain ⟨a, activeAncestor, identity, path⟩ := ancestry y ⟨active, distinct⟩
      exact ⟨a, activeAncestor, identity, path.to_reflTransGen⟩
  let Ancestors := actualIdentityAncestors p x
  let upstream (a b : Ancestors) := Relation.TransGen (ActualEsseCause p) a.val b.val
  let : Finite Ancestors := finite x actual
  let : IsTrans Ancestors upstream := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  let : Std.Irrefl upstream := ⟨fun a => acyclic a.val a.property.1 a.property.2.1⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl upstream
  obtain ⟨a, belongs⟩ := identityAncestor x actual
  obtain ⟨r, _, minimal⟩ := wf.has_min Set.univ ⟨⟨a, belongs⟩, Set.mem_univ _⟩
  have underived (c : B) (edge : ActualEsseCause p c r.val) : False := by
    obtain ⟨b, active, identity, path⟩ := identityAncestor c edge.2.1
    have before : Relation.TransGen (ActualEsseCause p) b r.val :=
      Relation.TransGen.trans_right path (.single edge)
    let ancestor : Ancestors := ⟨b, active, identity,
      before.to_reflTransGen.trans r.property.2.2⟩
    exact minimal ancestor (Set.mem_univ _) before
  exact ⟨r.val, r.property.1, (positiveCertificate (ActualEsseCause p) r.val x).mp
    ⟨r.property.2.2, underived⟩⟩

/-- The certificates yield closed-collection rootedness on the same profile. -/
theorem closedOfFiniteAcyclicIdentityAncestry (p : Profile B P R)
    (finite : ActualIdentityAncestorSetsFinite p)
    (acyclic : ActualIdentityAncestryAcyclic p)
    (ancestry : EveryDistinctEsseHasEsseIsEssenceSource p)
    (em : ExcludedMiddle) :
    ClosedActualEsseCollectionsRooted p := by
  exact closedOfFiniteRootAudits p (auditsOfFiniteAcyclicIdentityAncestry p finite acyclic ancestry em)

private def chain : Profile (Fin 3) Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => c.val + 1 = x.val
  essenceOf := fun _ => false
  esseOf := fun x => x == 2
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

private theorem chainIncreasing {a b : Fin 3}
    (path : Relation.TransGen (ActualEsseCause chain) a b) : a.val < b.val := by
  induction path with
  | single edge =>
    have step : _ + 1 = _ := edge.2.2.2
    exact step ▸ Nat.lt_succ_self _
  | tail _ edge ih =>
    have step : _ + 1 = _ := edge.2.2.2
    exact ih.trans (step ▸ Nat.lt_succ_self _)

/-- In the three-bearer chain, an actual identity supplies the distinct
recipient and is itself supplied by the underived actual identity. -/
theorem finiteAcyclicIdentityAncestryAllowsSupply :
    FiniteAcyclicIdentityAncestryAllowsSupply := by
  have rootToMiddle : ActualEsseCause chain 0 1 := ⟨by decide, trivial, trivial, rfl⟩
  have middleToEnd : ActualEsseCause chain 1 2 := ⟨by decide, trivial, trivial, rfl⟩
  have finite : ActualIdentityAncestorSetsFinite chain := fun _ _ => Set.toFinite _
  have acyclic : ActualIdentityAncestryAcyclic chain :=
    fun _ _ _ path => (Nat.lt_irrefl _) (chainIncreasing path)
  have ancestry : EveryDistinctEsseHasEsseIsEssenceSource chain := by
    intro x distinct
    fin_cases x
    · exact (distinct.2 rfl).elim
    · exact (distinct.2 rfl).elim
    · exact ⟨1, trivial, rfl, .single middleToEnd⟩
  refine ⟨chain, 0, 1, 2, rfl, ?_, rfl, rootToMiddle, by decide, middleToEnd,
    finite, acyclic, ancestry, auditsOfFiniteAcyclicIdentityAncestry chain finite acyclic ancestry
      Classical.em, ?_⟩
  · intro c edge
    exact (Nat.not_lt_zero c.val) (chainIncreasing (.single edge))
  · exact fun underived => underived 1 trivial rfl 0 rootToMiddle

private def cycle : Profile Bool Bool Unit :=
  { sourceFreeFiniteCircle with esseOf := Bool.not }

private def received (x z : Bool) : Prop := x = false ∧ z = false
private def potency (z act : Bool) : Prop := z = false ∧ act = true

private theorem cycleEdge {c x : Bool} (different : c ≠ x) :
    ActualEsseCause cycle c x :=
  ⟨different, trivial, trivial, different⟩

/-- The distinct bearer receives internally and has the identity bearer as
an actual cause. It also supplies the identity bearer, whose esse is never
received internally. Every bearer therefore has an incoming supplier. -/
theorem externalSupplyWithoutIdentityReceipt : ExternalSupplyWithoutIdentityReceipt := by
  have incoming : ActualEsseCause cycle false true := cycleEdge Bool.false_ne_true
  have outgoing : ActualEsseCause cycle true false := cycleEdge Bool.false_ne_true.symm
  have noReceipt : ∀ z, ¬ received true z := fun _ receipt => Bool.false_ne_true.symm receipt.1
  have notClosed : ¬ ClosedActualEsseCollectionsRooted cycle := by
    intro closed
    apply closed (fun _ => True) ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ _ _ => trivial⟩
      (fun x _ root => root.2 (!x)
        (by cases x
            · exact ⟨trivial, trivial, outgoing⟩
            · exact ⟨trivial, trivial, incoming⟩))
      true trivial
  refine ⟨cycle, received, potency, trivial, rfl, incoming, noReceipt, ⟨rfl, rfl⟩, outgoing,
    ?_, ?_, ?_, ?_, ?_, ?_, notClosed, fun audits => notClosed (closedOfFiniteRootAudits cycle audits)⟩
  · exact fun _ _ _ receipt => receipt.2
  · intro x z receipt
    obtain ⟨rfl, rfl⟩ := receipt
    exact ⟨rfl, rfl⟩
  · intro z self
    exact Bool.false_ne_true (self.1.symm.trans self.2)
  · intro x distinct
    cases x
    · exact ⟨true, trivial, rfl, .single outgoing⟩
    · exact (distinct.2 rfl).elim
  · intro caused
    obtain ⟨z, receipt⟩ := caused false true incoming.1 incoming.2.2.2
    exact noReceipt z receipt
  · exact fun underived => underived true trivial rfl false incoming

end TruthCore.Results.Aquinas.DeEnte.ReceivedOrUnderived
