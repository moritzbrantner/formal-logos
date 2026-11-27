module

public import TruthCore.Results.Causality.ActualAncestralSource.Solution
public import TruthCore.Results.Causality.RootIntellectWillPureActPlurality.Solution

@[expose] public section

namespace TruthCore.Results.Causality.PureActRootImmutability
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.PartFreePlurality
open TruthCore.Causality.RootIntellectWillPureAct
open TruthCore.Causality.RootIntellectWillPureActPlurality (model hasIntellect hasWill)
open TruthCore.Case.Catholicism (GodIsImmutable IsImmutable)
open TruthCore.Logic (ExcludedMiddle)

theorem immutableOfReach {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill IsGod : B → Prop)
    (InPotency : B → R → Prop)
    (hRoot : NecessaryRootIntellectWillPureActAt m w p
      PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill InPotency)
    (hReach : GodReachesActualConcreta m w IsGod) :
    GodIsImmutable IsGod (IsImmutable InPotency) := by
  obtain ⟨n, hn, _, _, _, _, _, _, _, _, hPure⟩ := hRoot
  intro g hg
  have hEq :=
    TruthCore.Results.Causality.ActualAncestralSource.namedRootOfReach m w IsGod hReach g n hg hn
  exact hEq.symm ▸ hPure

theorem reachOmission (_hEM : ExcludedMiddle) :
    let names := fun g : Being => g = .instrument
    NecessaryRootIntellectWillPureActAt model false esseProfile
      prior component composite matterForm hasIntellect hasWill moved ∧
    ¬ GodReachesActualConcreta model false names ∧
    ¬ GodIsImmutable names (IsImmutable moved) := by
  rcases TruthCore.Results.Causality.RootIntellectWillPureActPlurality.checks _hEM with
    ⟨_, _, _, _, _, hBundle, _, hInstrument, _, _, _⟩
  have hNotImmutable : ¬ GodIsImmutable (fun g : Being => g = .instrument) (IsImmutable moved) :=
    fun h => h .instrument rfl .drive hInstrument
  exact ⟨hBundle, fun hReach => hNotImmutable
    (immutableOfReach model false esseProfile prior component composite matterForm
      hasIntellect hasWill _ moved hBundle hReach), hNotImmutable⟩

end TruthCore.Results.Causality.PureActRootImmutability
