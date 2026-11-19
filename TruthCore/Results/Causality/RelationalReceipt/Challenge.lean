import TruthCore.Causality.RelationalReceipt

namespace TruthCore.Results.Causality.RelationalReceipt

open TruthCore.Causality.RelationalReceipt
open TruthCore.Causality.PresentReceipt
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.SustainingDependence (ReceivedOnsetIsGiven)
open TruthCore.Modal.TemporalHistory (History BeginsAt)

/-- Accompaniment and giving by the term give weak concurrent actualization
`40a97664`: a received-esse thing present at `t` bears the origin relation to
something at `t`, and that term gives it being at `t`. -/
theorem concurrentOfTermGiving {W B T P : Type} (h : History W B T)
    (G : BeingGiving W B T) (O : OriginRelation W B T) (EsseReceivedIn : B → P → Prop)
    (hAccompanies : RelationAccompaniesEsse h O EsseReceivedIn)
    (hGives : TermGives G O) :
    ConcurrentlyActualized h G EsseReceivedIn := by
  sorry

/-- On the relational sense the present-tense reading is accompaniment. -/
theorem relationalPresentIsAccompaniment : RelationalPresentIsAccompaniment := by
  sorry

/-- On the relational sense, given accompaniment, correlativity is weak
concurrent actualization. -/
theorem relationalReadingIsTheCrux : RelationalReadingIsTheCrux := by
  sorry

/-- Some founded, accompanying origin relation whose term gives exists iff weak
concurrent actualization holds: forward by `concurrentOfTermGiving`, backward
with the relation to whatever is giving being at the moment. -/
theorem someRelationCarriesTheCrux : SomeRelationCarriesTheCrux := by
  sorry

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control
open TruthCore.Causality.RelationalReceipt.Control

/-- Controls (`Control.Certificate`). -/
theorem controls : TruthCore.Causality.RelationalReceipt.Control.Certificate := by
  sorry

/-- Foundation, irreflexivity, non-mutuality, accompaniment, coexistence of the
term and received onset given
do not entail weak concurrent actualization: `Control` part 1 is a
counterexample. -/
theorem coexistentTermDoesNotCarryTheCrux : CoexistentTermDoesNotCarryTheCrux := by
  sorry

end TruthCore.Results.Causality.RelationalReceipt
