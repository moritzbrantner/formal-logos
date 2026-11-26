module

public import TruthCore.Latin.Aquinas.DeEnte.RankedGiverAudit
public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
public import TruthCore.Results.Causality.SupplierPairAudit.Solution

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.RankedGiverAudit

open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Causality.SupplierPairAudit (AdmissibleRelation CertifiesRoot)
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.FiniteEsseRootAudit (EveryActualEsseBearerHasFiniteRootAudit)
open TruthCore.Latin.Aquinas.DeEnte.RankedGiverAudit
open TruthCore.Latin.Aquinas.SummaTheologiae
open PrimaPars.Question3.Article4 (Profile)
open TruthCore.Results.Causality.SupplierPairAudit (certificateAt)

variable {B P R : Type}

theorem rankedCertificates (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (giver : MaximeEnsCausesBeingOfAllReading p.InAct MoreIn p.CausesIn p.esse)
    (ascent : CauseOfBeingIsMoreInBeing p.CausesIn MoreIn p.esse) :
    RankedGiverCertificates p MoreIn := by
  have valid (y x : B) (edge : ActualEsseCause p y x) : eligible p MoreIn y x :=
    ⟨edge.1, edge.2.1, edge.2.2.1, ascent y x edge.1 edge.2.2.2⟩
  obtain ⟨s, greatest, gives⟩ := giver
  refine ⟨valid, s, greatest, ?_⟩
  intro x hx
  apply (certificateAt _ _ _ _).mpr
  refine ⟨fun y h => (greatest.2 y h.2.2.2).elim, fun y h => greatest.2 y (valid y s h).2.2.2, ?_⟩
  by_cases same : s = x
  · subst x
    exact .refl
  · exact .single ⟨⟨same, greatest.1, hx, gives x (Ne.symm same) hx⟩, rfl, same⟩

/-- Factivity identifies a particular root in the actual relation. The
existing complete-list theorem constructs its row certificate on that relation. -/
theorem rowAuditsOfRankedCertificates (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (certificates : RankedGiverCertificates p MoreIn) : EveryActualEsseBearerHasFiniteRootAudit p := by
  obtain ⟨valid, s, greatest, cert⟩ := certificates
  intro x hx
  exact ⟨s, greatest.1, TruthCore.Results.Causality.SupplierPairAudit.completeListAuditOfPairCertificate
    ⟨ActualEsseCause p, valid⟩ (cert x hx)⟩

/-- Even when the ranking and maximality are fixed, the empty relation is
an admissible completion of the empty report. It has no path to a distinct
recipient. The actual universal-giving premise is not imposed on alternatives. -/
theorem emptyReportAtMaximum (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (actual : AdmissibleRelation (eligible p MoreIn)) {s x : B}
    (hs : IsMaximumIn p.InAct MoreIn p.esse s) :
    CertifiesRoot actual s x ∅ ↔ s = x := by
  constructor
  · intro cert
    let empty : AdmissibleRelation (eligible p MoreIn) := ⟨fun _ _ => False, fun _ _ h => h.elim⟩
    obtain ⟨path, _⟩ := cert empty (fun _ _ h => h.elim)
    change Relation.ReflTransGen (fun _ _ => False) s x at path
    cases path with
    | refl => rfl
    | tail _ edge => exact edge.elim
  · intro same
    subst x
    exact (certificateAt actual _ _ _).mpr
      ⟨fun y e => (hs.2 y e.2.2.2).elim, fun y e => hs.2 y (actual.property y s e).2.2.2, .refl⟩

end TruthCore.Results.Aquinas.DeEnte.RankedGiverAudit
