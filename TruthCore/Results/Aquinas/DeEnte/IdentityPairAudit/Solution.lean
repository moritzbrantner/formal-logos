module

public import TruthCore.Latin.Aquinas.DeEnte.IdentityPairAudit
public import TruthCore.Results.Causality.SupplierPairAudit.Solution
public import TruthCore.Latin.Aquinas.DeEnte.UnobservedGiver

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.IdentityPairAudit

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.IdentityPairAudit
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived (ActualIdentityEsseHasNoSupplier)
open TruthCore.Latin.Aquinas.DeEnte.UnobservedGiver (rankedProfile FinitePairGiverControl)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.SupplierPairAudit (AdmissibleRelation CertifiesRoot)
open TruthCore.Results.Causality.SupplierPairAudit (finiteCertificate)
open TruthCore.Logic (ExcludedMiddle)

variable {B P R : Type}

theorem finiteIdentityQueries (p : Profile B P R)
    (ancestry : EveryDistinctEsseHasEsseIsEssenceSource p)
    (underived : ActualIdentityEsseHasNoSupplier p) (em : ExcludedMiddle) :
    FiniteIdentityPairAudits p := by
  have valid (y x : B) (edge : ActualEsseCause p y x) : eligible p y x :=
    ⟨edge.1, edge.2.1, edge.2.2.1, fun identity => underived x edge.2.2.1 identity y edge⟩
  let actual : AdmissibleRelation (eligible p) := ⟨ActualEsseCause p, valid⟩
  refine ⟨valid, ?_⟩
  intro x hx
  have certify (s : B) (hs : p.InAct s p.esse) (id : p.esseOf s = p.essenceOf s)
      (path : Relation.ReflTransGen (ActualEsseCause p) s x) :
      ∃ tested : Set (B × B), tested.Finite ∧ CertifiesRoot actual s x tested := by
    apply (finiteCertificate actual s x).mpr
    refine ⟨⟨path, underived s hs id⟩, Set.finite_empty.subset ?_⟩
    exact fun _ h => (h.2.2.2 id).elim
  rcases em (p.esseOf x = p.essenceOf x) with id | distinct
  · exact ⟨x, hx, id, certify x hx id .refl⟩
  · obtain ⟨s, hs, id, path⟩ := ancestry x ⟨hx, distinct⟩
    exact ⟨s, hs, id, certify s hs id path.to_reflTransGen⟩

theorem listAuditsOfIdentityPairs (p : Profile B P R) (audits : FiniteIdentityPairAudits p) :
    FiniteEsseRootAudit.EveryActualEsseBearerHasFiniteRootAudit p := by
  obtain ⟨valid, each⟩ := audits
  intro x hx
  obtain ⟨s, hs, _, _, _, cert⟩ := each x hx
  exact ⟨s, hs, TruthCore.Results.Causality.SupplierPairAudit.completeListAuditOfPairCertificate
    ⟨ActualEsseCause p, valid⟩ cert⟩

/-- Keeping the represented equality at the baseline giver does not keep the
underived-identity principle when a different bearer gives that giver esse. -/
theorem hiddenGiverAtIdentity (control : FinitePairGiverControl)
    (tested : Set (Option Nat × Option Nat)) (finite : tested.Finite) :
    ∃ h : Option Nat, h ≠ none ∧
      (∀ c x, (c, x) ∈ tested →
        (ActualEsseCause (rankedProfile none) c x ↔ ActualEsseCause (rankedProfile h) c x)) ∧
      (rankedProfile h).esseOf none = (rankedProfile h).essenceOf none ∧
      ActualEsseCause (rankedProfile h) h none ∧ ¬ ActualIdentityEsseHasNoSupplier (rankedProfile h) := by
  obtain ⟨h, fresh, agrees, gives, _⟩ := control.2 tested finite
  exact ⟨h, fresh, fun c x q => (agrees c x q).2.2, rfl, gives,
    fun underived => underived none trivial rfl h gives⟩

end TruthCore.Results.Aquinas.DeEnte.IdentityPairAudit
