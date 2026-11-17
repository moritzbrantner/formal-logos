module

public import Mathlib.Logic.Relation
public import TruthCore.Causality.NecessarySupportActualScope

/-! Analyst comparison of standing, mediate support accounts. A path is the
nonempty Mathlib transitive closure of the SAME actual guarded grounding edges
on the concrete subtype. It is not an edge, a world transition or an adequate
explanation. No target population, modal reflexivity or necessary source is
asserted by either conditional transport property. Attribution deferred. -/
@[expose] public section
namespace TruthCore.Causality.NecessarySupportPathConnection
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportActualScope
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

variable {W B : Type}

/-- OPEN stronger transport: any existing concrete source of a necessary concrete
target at any admitted world has a NONEMPTY actual grounding path to that same
target. Intermediate nodes are concrete, and each edge's source actually exists.
The source need not be necessary. The final target's actual existence is not
built in, so the original actual-source supply remains a separate input. -/
def ConcreteSupportActualPaths (m : Profile W B) (w : W) : Prop :=
  ∀ v (a b : {x // m.concrete x}), NecessaryAt (concreteOntic m) w b →
    (concreteOntic m).ExistsAt v a → concreteSupport m v a b →
      Relation.TransGen (PresentEsseSupport (concreteOntic m) (concreteSupport m) w) a b

/-- OPEN weaker transport: the same nonempty actual-path requirement only when
BOTH the source and target are necessary from the selected world. Off-world
contingent supporters are unconstrained. No transitivity of grounds is assumed. -/
def NecessarySupportActualPaths (m : Profile W B) (w : W) : Prop :=
  ∀ v (a b : {x // m.concrete x}), NecessaryAt (concreteOntic m) w a →
    NecessaryAt (concreteOntic m) w b → (concreteOntic m).ExistsAt v a →
    concreteSupport m v a b →
      Relation.TransGen (PresentEsseSupport (concreteOntic m) (concreteSupport m) w) a b

namespace Control
open TruthCore.Causality.NecessarySupportCoverage.Control (Tri)

/-- Actual chain t0→t1→t2; alternative direct shortcut t0→t2. All candidates
exist at both worlds. Direct support changes while actual ancestry persists. -/
def shortcut : Profile Bool Tri where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun _ => True -- category-constant: intended (all-concrete support-path comparison)
  grounds := fun v a b =>
    (v = false ∧ ((a = .t0 ∧ b = .t1) ∨ (a = .t1 ∧ b = .t2))) ∨
    (v = true ∧ a = .t0 ∧ b = .t2)

/-- Full application witness: both path scopes, actual WF, both J1 scopes,
coverage and union WF; direct presence fails. The supplied necessary t2 is
supported, while the different necessary t0 is underived at every world. -/
def ShortcutControl : Prop :=
  ConcreteSupportActualPaths shortcut false ∧ NecessarySupportActualPaths shortcut false ∧
    ActualGroundingWF shortcut false ∧ ActualNoContingentConcreteSupport shortcut false ∧
    NoContingentConcreteSupport shortcut false ∧ NecessarySupportActuallyCovered shortcut false ∧
    ConcreteNecessaryUnionWF shortcut false ∧
    ¬ TruthCore.Causality.UnderivedRootRoute.NecessarySupportIsPresent shortcut false ∧
    NecessaryConcreteAt shortcut false ∧
    shortcut.ontic.ExistsAt false .t2 ∧ NecessaryAt shortcut.ontic false .t2 ∧
    shortcut.grounds false .t1 .t2 ∧
    (shortcut.ontic.ExistsAt false .t0 ∧ NecessaryAt shortcut.ontic false .t0 ∧
      ∀ v a, shortcut.ontic.ExistsAt v a → ¬ shortcut.grounds v a .t0)

/-- Existing contingent replacement interpretation strictly separates the path
scopes; existing rooted-pair interpretation separates coverage from necessary
path transport despite actual WF and J1. Their old certificates are reused. -/
def ScopeControls : Prop :=
  (let m := TruthCore.Causality.NecessarySupportActualScope.Control.offWorldContingent
   NecessarySupportActualPaths m false ∧ ¬ ConcreteSupportActualPaths m false ∧
     ActualNoContingentConcreteSupport m false ∧ ¬ NoContingentConcreteSupport m false ∧
     NecessarySupportActuallyCovered m false ∧ ConcreteNecessaryUnionWF m false ∧
     NecessaryConcreteUnderivedAt m false) ∧
  (let m := TruthCore.Causality.NecessarySupportCoverage.Control.rootedPair
   NecessarySupportActuallyCovered m false ∧ ActualGroundingWF m false ∧
     NoContingentConcreteSupport m false ∧ ¬ NecessarySupportActualPaths m false ∧
     NecessaryConcreteUnderivedAt m false)

end Control
end TruthCore.Causality.NecessarySupportPathConnection
