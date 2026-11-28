module

public import TruthCore.Causality.ContingentBeingNode
public import TruthCore.Modal.ActualistDomains

/-! The forward guarded quantifier transfer (VARYING_DOMAINS_RIGID_IDENTITY_AND_NECESSITY_4,
`BoxAllToAllBox`) imposed at every world of the contingency route's Ontic profile.
In a fixed-domain classical quantified modal logic this transfer is the
converse-Barcan pattern; on this varying-domain profile the library equates it
with increasing domains. It is a necessitist commitment, not an actualist one:
actualists reject it because of contingent existents. Both sides read presence
and accessibility from the same Ontic profile with rigid candidate identity and
total valuation predicates.

The transfer strictly strengthens concrete necessitarianism
(`EveryActualConcreteNecessaryAt`) at every world. The controls below witness
the two respects in which it is stronger: it constrains non-concrete candidates,
and it constrains worlds other than the selected one. -/

@[expose] public section

namespace TruthCore.Modal.ActualistContingencyRoute
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Modal.ActualistDomains (BoxAllToAllBox)

/-- The quantified transfer is imposed at every world of the route's Ontic. -/
def RouteForwardTransfer {W B : Type} (m : Profile W B) : Prop :=
  BoxAllToAllBox m.ontic

/-- Not every world and total predicate of this very profile satisfies the
transfer: the negation of the universally quantified policy. -/
def NoRouteForwardTransfer {W B : Type} (m : Profile W B) : Prop :=
  ¬ RouteForwardTransfer m

end TruthCore.Modal.ActualistContingencyRoute

/-! ## Controls (formal, finite, hand-written carriers) -/

namespace TruthCore.Modal.ActualistContingencyRoute.Control
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ContingentBeingNode
  (EveryActualConcreteNecessaryAt SomeActualContingentAt)

/-- Two universally accessible worlds. Being `true` is concrete and exists at
both worlds; being `false` is not concrete and exists only at world `false`. -/
def abstractDrop : Profile Bool Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w x => x = true ∨ w = false,
             Causes := fun _ _ _ => False }
  concrete := fun x => x = true
  grounds := fun _ _ _ => False

/-- Two universally accessible worlds, every being concrete. Being `true`
exists at both worlds; being `false` exists only at world `false`. -/
def concreteDrop : Profile Bool Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w x => x = true ∨ w = false,
             Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- Strictness of the strength order from the forward transfer to concrete
necessitarianism.
1. Non-concrete candidates (`abstractDrop`): every actual concrete being is
   NECESSARY_2 at every world, the transfer fails, and no actual concrete being
   is CONTINGENT_1 at any world. So the transfer's failure gives the
   contingency node no support.
2. Other worlds (`concreteDrop`, world `true`): every candidate is concrete,
   every actual concrete being is NECESSARY_2 at the selected world `true`, and
   the transfer fails. -/
def Strictness : Prop :=
  ((∀ w, EveryActualConcreteNecessaryAt abstractDrop w) ∧
    NoRouteForwardTransfer abstractDrop ∧
    (∀ w, ¬ SomeActualContingentAt abstractDrop w)) ∧
  (EveryActualConcreteNecessaryAt concreteDrop true ∧
    NoRouteForwardTransfer concreteDrop)

end TruthCore.Modal.ActualistContingencyRoute.Control
