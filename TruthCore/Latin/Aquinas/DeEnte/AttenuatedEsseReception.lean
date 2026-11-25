module

public import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.AttenuatedEsseReception

open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource (esseCauseGraph)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.ClosedGroundingRoots (AttenuatedEsseReception)

/-- OPEN quantitative reception premise on the exact actual esse-cause graph.
Positive reception uses actual esse causes, and positive input of one's own
requires absence of every actual esse cause of that bearer. The singleton index
adds no world-relative causal commitment. -/
def AttenuatedActualEsseReception {B P R : Type} (p : Profile B P R) : Prop :=
  AttenuatedEsseReception (esseCauseGraph p) ()

end TruthCore.Latin.Aquinas.DeEnte.AttenuatedEsseReception
