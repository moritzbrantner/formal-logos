module

public import TruthCore.Latin.Aquinas.DeEnte.RankedGiverAudit
public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.RankedGiverAudit

open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Causality.SupplierPairAudit (AdmissibleRelation CertifiesRoot)
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit (EveryActualEsseBearerHasFiniteRootAudit)
open TruthCore.Latin.Aquinas.DeEnte.RankedGiverAudit
open TruthCore.Latin.Aquinas.SummaTheologiae
open PrimaPars.Question3.Article4 (Profile)

variable {B P R : Type}

theorem rankedCertificates (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (giver : MaximeEnsCausesBeingOfAllReading p.InAct MoreIn p.CausesIn p.esse)
    (ascent : CauseOfBeingIsMoreInBeing p.CausesIn MoreIn p.esse) :
    RankedGiverCertificates p MoreIn := by
  sorry

/-- Factivity identifies a particular root in the actual relation. The
existing complete-list theorem constructs its row certificate on that relation. -/
theorem rowAuditsOfRankedCertificates (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (certificates : RankedGiverCertificates p MoreIn) : EveryActualEsseBearerHasFiniteRootAudit p := by
  sorry

/-- Even when the ranking and maximality are fixed, the empty relation is
an admissible completion of the empty report. It has no path to a distinct
recipient. The actual universal-giving premise is not imposed on alternatives. -/
theorem emptyReportAtMaximum (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (actual : AdmissibleRelation (eligible p MoreIn)) {s x : B}
    (hs : IsMaximumIn p.InAct MoreIn p.esse s) :
    CertifiesRoot actual s x ∅ ↔ s = x := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.RankedGiverAudit
