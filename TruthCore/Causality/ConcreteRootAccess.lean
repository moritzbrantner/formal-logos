module
public import TruthCore.Causality.ClosedGroundingRoots

/-! Finite access at one fixed profile/world/relation. Analyst definitions;
attribution deferred. These decompose CCR and supply no independent warrant. -/
@[expose] public section
namespace TruthCore.Causality.ConcreteRootAccess
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.ClosedGroundingRoots
variable {W B : Type}

/-- Finite supplier-to-recipient path, starting at an actual concrete root.
Every endpoint is actual concrete; the zero-edge root path is admitted. -/
inductive RootAccess (m : Profile W B) (w : W) : B → Prop
  | root {x} : ActualRoot m w x → RootAccess m w x
  | step {y x} : RootAccess m w y → ActualConcrete m w x →
      ActualConcreteGround m w y x → RootAccess m w x

def UniversalRootAccess (m : Profile W B) (w : W) : Prop :=
  ∀ x, ActualConcrete m w x → RootAccess m w x

/-- Root access is demanded only for concrete recipients with an actual
nonconcrete supplier. This permits actual nonconcrete suppliers of concrete
recipients; it reads the edge neither as a partial co-ground
(`PartialCoGround`) nor as a sufficient supplier (`SufficientSupply`). -/
def LocalizedBridge (m : Profile W B) (w : W) : Prop :=
  ∀ x y, ActualConcrete m w x → m.ontic.ExistsAt w y →
    ¬ m.concrete y → m.grounds w y x → RootAccess m w x

/-- SUPPLY_EDGE_1, partial co-ground on the modal-covariation proxy: an actual
supplier's edge to `x` at `w` such that at some world accessible from `w` the
supplier exists and `x` does not. Reading worlds as the admissible existence
assignments, the supplier then does not select `x`'s existence (the note's
`a = b` constraint admits the all-zero assignment).
Limit: the proxy also sorts here a supplier that does suffice for a contingent
effect, such as a free sustaining cause or a necessary agent with a contingent
effect. Do not read an edge in this sense as showing that other contributors
are needed. Analyst sense, attribution deferred; `Profile.grounds` itself stays
neutral. -/
def PartialCoGround (m : Profile W B) (w : W) (y x : B) : Prop :=
  m.ontic.ExistsAt w y ∧ m.grounds w y x ∧
    ∃ v, m.ontic.frame.access w v ∧ m.ontic.ExistsAt v y ∧ ¬ m.ontic.ExistsAt v x

/-- SUPPLY_EDGE_2, sufficient supply on the modal-covariation proxy: an actual
supplier's edge to `x` at `w` such that at every world accessible from `w`
where the supplier exists, `x` exists. This is the proxy for the
realization-rule reading `L implies a and b`; it records modal covariation,
not how or whether the supplier selects `x`'s existence.
Limit: the proxy also sorts here every edge into a recipient that exists
wherever its supplier exists, including every edge into a NECESSARY_2
recipient, even when that supplier is one partial contributor among several.
Analyst sense, attribution deferred. -/
def SufficientSupply (m : Profile W B) (w : W) (y x : B) : Prop :=
  m.ontic.ExistsAt w y ∧ m.grounds w y x ∧
    ∀ v, m.ontic.frame.access w v → m.ontic.ExistsAt v y → m.ontic.ExistsAt v x

/-- The two proxies exclude each other by construction (constructive). This
does not certify that the intended partial/sufficient distinction is exclusive. -/
theorem not_sufficient_of_partial {m : Profile W B} {w : W} {y x : B}
    (h : PartialCoGround m w y x) : ¬ SufficientSupply m w y x := by
  rintro ⟨-, -, hs⟩
  obtain ⟨-, -, v, hv, hy, hx⟩ := h
  exact hx (hs v hv hy)

/-- Under excluded middle every actual edge falls under one of the two proxies,
by construction. This does not certify that the intended partial/sufficient
distinction is exhaustive. -/
theorem partial_or_sufficient {m : Profile W B} {w : W} {y x : B}
    (em : ∀ p : Prop, p ∨ ¬ p) (hy : m.ontic.ExistsAt w y) (hg : m.grounds w y x) :
    PartialCoGround m w y x ∨ SufficientSupply m w y x := by
  rcases em (∃ v, m.ontic.frame.access w v ∧ m.ontic.ExistsAt v y ∧
      ¬ m.ontic.ExistsAt v x) with h | h
  · exact Or.inl ⟨hy, hg, h⟩
  · refine Or.inr ⟨hy, hg, fun v hv hyv => ?_⟩
    rcases em (m.ontic.ExistsAt v x) with hx | hx
    · exact hx
    · exact absurd ⟨v, hv, hyv, hx⟩ h

def RootAccessEquivalence (m : Profile W B) (w : W) : Prop :=
  ClosedGroundingCollectionsRooted m w ↔ UniversalRootAccess m w

def BorrowedDecomposition (m : Profile W B) (w : W) : Prop :=
  ClosedGroundingCollectionsRooted m w ↔
    NoWhollyBorrowedCollection m w ∧ LocalizedBridge m w

def BlanketEquivalence (m : Profile W B) (w : W) : Prop :=
  ClosedGroundingCollectionsRooted m w ↔ NoWhollyBorrowedCollection m w
end TruthCore.Causality.ConcreteRootAccess
