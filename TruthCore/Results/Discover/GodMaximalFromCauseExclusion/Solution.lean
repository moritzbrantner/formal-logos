module

public import TruthCore.Case.Catholicism.MaximalBeingCauseExclusion
public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Causality.GodMaximalCausal
public import TruthCore.Causality.TermSenseForks3
public import Duper

/-!
# God maximality from maximal existence and distinct-cause exclusion

Analyst registration of the conditional bundle already reported in #1850/#1860
and attempt `3bd2aeb2-7a0a-4c04-b1f9-32eaba83991e`. The Solution uses a proof
emitted by `truth discover` for the exact three-premise bundle at 100000
heartbeats on 2026-11-24, after review of the existing carrier sense tags. Its legacy
parameters and Duper proof are retained; no new vocabulary is introduced.

Given a maximal being `m`, any `g` satisfying `IsGod` must be identical to `m`:
otherwise `g` would cause `m`'s being, contrary to the exclusion premise.
This supplies conditional support for the existing maximality statement. It
does not establish the premises or assert that any being satisfies `IsGod`.
-/

@[expose] public section

namespace TruthCore.Results.Discover.GodMaximalFromCauseExclusion

set_option maxHeartbeats 100000 in
/-- Every GOD_4 is maximal in being, under the three stated premises. -/
theorem godMaximalFromCauseExclusion {Being : Type} {Respect : Type}
    (IsGod : Being → Prop) (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (CausesIn : Being → Being → Respect → Prop)
    (h0 : TruthCore.Case.Catholicism.MaximumHasNoDistinctEsseCause
      InAct MoreIn CausesIn esse)
    (h1 : TruthCore.Causality.TermSenseForks.SomeBeingMaximalInBeing InAct MoreIn esse)
    (h2 : TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers
      IsGod CausesIn esse) :
    TruthCore.Case.Catholicism.GodIsMaximalInBeing IsGod InAct MoreIn esse := by
  delta TruthCore.Case.Catholicism.GodIsMaximalInBeing
    TruthCore.Case.Catholicism.MaximumHasNoDistinctEsseCause
    TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers
    TruthCore.Causality.TermSenseForks.SomeBeingMaximalInBeing
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn at *
  duper [*]

end TruthCore.Results.Discover.GodMaximalFromCauseExclusion
