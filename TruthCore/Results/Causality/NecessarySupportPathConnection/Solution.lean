module

public import TruthCore.Causality.NecessarySupportPathConnection
public import TruthCore.Results.Causality.NecessarySupportCoverage.Solution
public import TruthCore.Results.Causality.NecessarySupportActualScope.Solution

@[expose] public section
namespace TruthCore.Results.Causality.NecessarySupportPathConnection
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportActualScope
open TruthCore.Causality.NecessarySupportPathConnection
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

variable {W B : Type}

theorem restrictPaths (m : Profile W B) (w : W)
    (h : ConcreteSupportActualPaths m w) : NecessarySupportActualPaths m w := by
  intro v a b _ hb ha hab
  exact h v a b hb ha hab

theorem pathsOfPresence (m : Profile W B) (w : W)
    (h : TruthCore.Causality.UnderivedRootRoute.NecessarySupportIsPresent m w) :
    ConcreteSupportActualPaths m w := by
  intro v a b hb ha hab
  exact .single (h v a.1 b.1 hb ha hab)

theorem coverageOfPaths (m : Profile W B) (w : W)
    (h : ConcreteSupportActualPaths m w) : NecessarySupportActuallyCovered m w := by
  intro v a b ha hb hn hav hab
  have path := h v ⟨a, ha⟩ ⟨b, hb⟩ hn hav hab
  obtain ⟨c, _, hc⟩ := Relation.TransGen.tail'_iff.mp path
  exact ⟨c.1, c.2, hc.1, hc.2⟩

/-- Only the necessary-source path scope is needed. Actual WF is used to make
its actual guarded support graph and its NONEMPTY transitive closure WF. -/
theorem unionOfNecessaryPaths (m : Profile W B) (w : W)
    (hWF : TruthCore.Causality.NecessaryRootFork.ActualGroundingWF m w)
    (hPath : NecessarySupportActualPaths m w) : ConcreteNecessaryUnionWF m w := by
  have hActual := TruthCore.Results.Causality.NecessarySupportCoverage.presentSupportWF m w hWF
  apply Subrelation.wf (r := Relation.TransGen
    (PresentEsseSupport (concreteOntic m) (concreteSupport m) w)) _ hActual.transGen
  intro a b hUnion
  obtain ⟨ha, hb, v, hav, hab⟩ := hUnion
  exact hPath v a b ha hb hav hab

/-- J1 upgrades the restricted path scope. No frame or population premise. -/
theorem upgradePaths (m : Profile W B) (w : W)
    (hNoCont : NoContingentConcreteSupport m w)
    (hPath : NecessarySupportActualPaths m w) : ConcreteSupportActualPaths m w := by
  intro v a b hb ha hab
  exact hPath v a b (hNoCont v a b ha hb hab) hb ha hab

/-- The actual-world J1 instance propagates backwards along each actual path;
the strong transport scope therefore recovers full all-admitted-world J1. -/
theorem noContingentOfActualPaths (m : Profile W B) (w : W)
    (hActual : ActualNoContingentConcreteSupport m w)
    (hPath : ConcreteSupportActualPaths m w) : NoContingentConcreteSupport m w := by
  have walk : ∀ a b : {x // m.concrete x},
      Relation.TransGen (PresentEsseSupport (concreteOntic m) (concreteSupport m) w) a b →
      NecessaryAt (concreteOntic m) w b → NecessaryAt (concreteOntic m) w a := by
    intro a b path
    induction path with
    | single hab =>
      intro hb
      exact hActual _ _ hab.1 hb hab.2
    | tail _ hbc ih =>
      intro hc
      exact ih (hActual _ _ hbc.1 hc hbc.2)
  intro v a b ha hb hab
  exact walk a b (hPath v a b hb ha hab) hb

theorem shortcutControl : Control.ShortcutControl := by
  open Control in
  have hPaths : ConcreteSupportActualPaths Control.shortcut false := by
    intro v ⟨a, ha⟩ ⟨b, hb⟩ _ _ hEdge
    rcases hEdge with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, rfl, rfl⟩
    · exact .single ⟨trivial, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact .single ⟨trivial, Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    · have h01 : PresentEsseSupport (concreteOntic shortcut) (concreteSupport shortcut) false
          ⟨.t0, trivial⟩ ⟨.t1, trivial⟩ :=
        ⟨trivial, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      have h12 : PresentEsseSupport (concreteOntic shortcut) (concreteSupport shortcut) false
          ⟨.t1, trivial⟩ ⟨.t2, trivial⟩ :=
        ⟨trivial, Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
      exact (Relation.TransGen.single h01).tail h12
  have hRank : ∀ a b, Control.shortcut.grounds false a b →
      TruthCore.Results.Causality.NecessarySupportCoverage.pairRank false a <
        TruthCore.Results.Causality.NecessarySupportCoverage.pairRank false b := by
    intro a b h
    rcases h with ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨h, _⟩
    · decide
    · decide
    · cases h
  have hWF : TruthCore.Causality.NecessaryRootFork.ActualGroundingWF Control.shortcut false :=
    TruthCore.Results.Causality.NecessarySupportCoverage.wf_of_rank _
      (fun x => TruthCore.Results.Causality.NecessarySupportCoverage.pairRank false x.1)
      (fun a b h => hRank a.1 b.1 h)
  have hWeak := restrictPaths Control.shortcut false hPaths
  refine ⟨hPaths, hWeak, hWF, ?_, ?_, coverageOfPaths _ _ hPaths,
    unionOfNecessaryPaths _ _ hWF hWeak, ?_, ?_, trivial, (fun _ _ => trivial),
    Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, trivial, (fun _ _ => trivial), ?_⟩
  · intro _ _ _ _ _ _ _
    trivial
  · intro _ _ _ _ _ _ _ _
    trivial
  · intro h
    have hEdge := (h true .t0 .t2 (fun _ _ => trivial) trivial
      (Or.inr ⟨rfl, rfl, rfl⟩)).2
    simp [Control.shortcut] at hEdge
  · exact ⟨.t2, trivial, trivial, fun _ _ => trivial⟩
  · intro v a _ h
    simp [Control.shortcut] at h

theorem scopeControls : Control.ScopeControls := by
  have hOld := TruthCore.Results.Causality.NecessarySupportActualScope.offWorldContingentControl
  obtain ⟨hAct, hNotJ1, _, _, _, _, _, _, hUnion, hCov, _, hUnderived⟩ := hOld
  have hWeak : NecessarySupportActualPaths
      TruthCore.Causality.NecessarySupportActualScope.Control.offWorldContingent false := by
    intro v ⟨a, ha⟩ ⟨b, hb⟩ hna _ _ hEdge
    rcases hEdge with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact .single ⟨(fun h => nomatch h), Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact (TruthCore.Results.Causality.NecessarySupportActualScope.t2_absent
        (hna false trivial)).elim
  have hNotStrong : ¬ ConcreteSupportActualPaths
      TruthCore.Causality.NecessarySupportActualScope.Control.offWorldContingent false := by
    intro h
    have path := h true ⟨.t2, trivial⟩ ⟨.t1, trivial⟩ (fun _ _ h => nomatch h)
      (fun _ => rfl) (Or.inr ⟨rfl, rfl, rfl⟩)
    obtain ⟨_, hFirst, _⟩ := Relation.TransGen.head'_iff.mp path
    exact TruthCore.Results.Causality.NecessarySupportActualScope.t2_absent hFirst.1
  have hPair := TruthCore.Results.Causality.NecessarySupportCoverage.rootedPairCompatible
  obtain ⟨_, _, _, hPairWF, _, _, hPairJ1, hPairCov, _, hPairNotUnion, _, _, hPairUnderived⟩ := hPair
  exact ⟨⟨hWeak, hNotStrong, hAct, hNotJ1, hCov, hUnion, hUnderived⟩,
    hPairCov, hPairWF, hPairJ1,
    (fun h => hPairNotUnion (unionOfNecessaryPaths _ _ hPairWF h)), hPairUnderived⟩

end TruthCore.Results.Causality.NecessarySupportPathConnection
