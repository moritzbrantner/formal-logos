import TruthCore.Causality.AncestorIndividuation

namespace TruthCore.Results.Causality.AncestorIndividuation
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.Regress (Graph)
open TruthCore.Causality.SourceForest (WellFoundedEdges)
open TruthCore.Causality.AncestorIndividuation

theorem comparability {B : Type} (G : Graph B)
    (hEM : ExcludedMiddle) (hWF : WellFoundedEdges G)
    (hIdentity : IdentityByAncestors G) : ComparableByAncestry G := by sorry

theorem siblings : SiblingControl := by sorry

theorem atMostOneSource {B : Type} (G : Graph B) (hIdentity : IdentityByAncestors G) :
    TruthCore.Causality.SourceForest.AtMostOneSource G := by sorry

end TruthCore.Results.Causality.AncestorIndividuation
