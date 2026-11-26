module

public import TruthCore.Latin.Aquinas.DeEnte.IdentityPairAudit
public import TruthCore.Latin.Aquinas.DeEnte.UnobservedGiver

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.IdentityPairAudit

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.IdentityPairAudit
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived (ActualIdentityEsseHasNoSupplier)
open TruthCore.Latin.Aquinas.DeEnte.UnobservedGiver (rankedProfile FinitePairGiverControl)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.SupplierPairAudit (AdmissibleRelation CertifiesRoot)
open TruthCore.Logic (ExcludedMiddle)

variable {B P R : Type}

theorem finiteIdentityQueries (p : Profile B P R)
    (ancestry : EveryDistinctEsseHasEsseIsEssenceSource p)
    (underived : ActualIdentityEsseHasNoSupplier p) (em : ExcludedMiddle) :
    FiniteIdentityPairAudits p := by
  sorry

theorem listAuditsOfIdentityPairs (p : Profile B P R) (audits : FiniteIdentityPairAudits p) :
    FiniteEsseRootAudit.EveryActualEsseBearerHasFiniteRootAudit p := by
  sorry

/-- Keeping the represented equality at the baseline giver does not keep the
underived-identity principle when a different bearer gives that giver esse. -/
theorem hiddenGiverAtIdentity (control : FinitePairGiverControl)
    (tested : Set (Option Nat × Option Nat)) (finite : tested.Finite) :
    ∃ h : Option Nat, h ≠ none ∧
      (∀ c x, (c, x) ∈ tested →
        (ActualEsseCause (rankedProfile none) c x ↔ ActualEsseCause (rankedProfile h) c x)) ∧
      (rankedProfile h).esseOf none = (rankedProfile h).essenceOf none ∧
      ActualEsseCause (rankedProfile h) h none ∧ ¬ ActualIdentityEsseHasNoSupplier (rankedProfile h) := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.IdentityPairAudit
