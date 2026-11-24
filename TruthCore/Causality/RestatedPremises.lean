module

public import TruthCore.Causality.ComponentFirstness
public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.Round3CogitoBase
public import TruthCore.Causality.CartesianIdeaOfInfinite
public import TruthCore.Causality.ContingentBeingNode
public import TruthCore.Causality.FirstMoverNecessity
public import TruthCore.Modal.ModalGrounding
public import TruthCore.Modal.PrussPowerPremises

/-! Restated premises: which coincide and which only look alike (#1926, phase 2)

A consolidation slice. It adds no premise to any existing argument and no
bridge between distinct relations. It records three kinds of fact about
premises that a survey reported as restatements of one another.

* **Same proposition, two records.** `ComponentFirstness.ParticipatedHasOtherCause`
  (ST I q.44 a.1 ad 1) and `Round2Grounding.ParticipatedEsseHasDistinctCause`
  (q.44 a.1 co.) have the same body over the same parameters
  (`participatedCauseReadingsIff`, `Iff.rfl`). The cogito premise
  `CartesianIdeaOfInfinite.MeditatorThinks I` is
  `Round3CogitoBase.SelectedBearsOccurringThought` at the idea frame's own
  occurrence, bearing and meditator fields (`meditatorThinksIff`, `Iff.rfl`).
  `ModalGrounding.SomeContingentConcreteAt F concrete w` is
  `ContingentBeingNode.SomeActualContingentAt` on the frame's ground profile
  `groundProfile F concrete grounds`, for every `grounds`
  (`someContingentConcreteIff`, `Iff.rfl`). Each pair stays two records because
  their sources, carriers or routes differ; the equivalence is registered, not
  merged.
* **One principle, several instances.** `AristotelianGroundingEverywhere` is
  Aristotelian modality stated once: at every world `u`, every proposition true
  at some world accessible from `u` and false at `u` is the object of a power
  (`PowerFor`) held at `u` by a being existing at `u`. The bare premises
  `ModalGrounding.ActualAbsenceGrounded` (P1′, at `w`, for the joint absence of
  the actual contingent concreta), `PrussPowerPremises.ActualityGroundedAtAbsenceWorlds`
  (at each absence world, for `w` obtaining) and
  `ModalGrounding.GlobalAbsenceGrounded` (the stronger analyst variant) are
  instances of it for single propositions. The universal entails each instance
  by instantiation (a transcription of kind `instantiation`); no instance or
  conjunction of these three instances entails the universal
  (`Control.GroundingInstancesWithoutUniversal`).
* **Alike in shape only.** The occurrence premises of the assertion, doubt and
  thinking retorsions use disjoint primitives (`Asserts`; `Performed` and
  `DoubtsThought`; `Occurs` and `Bears`); none entails another without an open
  realization bridge, so nothing is registered between them here.

The universal principle is an analyst formulation of the Aristotelian modality
of A. Pruss, *Actuality, Possibility, and Worlds* (2011), navigation only,
attribution deferred. It is a stated framework input; nothing here argues for
it, and the instances keep their own records as the weakest versions the routes
use. `PowerFor` keeps the meaning stated in `ModalGrounding`.
-/

@[expose] public section

namespace TruthCore.Causality.RestatedPremises

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Causality.ComponentFirstness (ParticipatedHasOtherCause)
open TruthCore.Causality.Round2Grounding (ParticipatedEsseHasDistinctCause)
open TruthCore.Causality.Round3CogitoBase (SelectedBearsOccurringThought)
open TruthCore.Causality.CartesianIdeaOfInfinite (IdeaFrame MeditatorThinks)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.ModalGrounding (AristotelianGroundingFor ActualAbsenceGrounded
  GlobalAbsenceGrounded SomeContingentConcreteAt PossiblyNoActualContingentConcrete)
open TruthCore.Modal.PrussPowerPremises (ActualityGroundedAtAbsenceWorlds)

variable {W B T R : Type}

/-- OPEN (Aristotelian modality, stated once): at every world `u`, if a
proposition `p` holds at some world accessible from `u` and fails at `u`, then
some being existing at `u` has, at `u`, a power (`PowerFor u y p`) whose
exercise would initiate a causal chain issuing in `p`. The single-proposition
premises `ActualAbsenceGrounded`, `ActualityGroundedAtAbsenceWorlds` and
`GlobalAbsenceGrounded` are its instances. Analyst formulation of Pruss's
principle; attribution deferred. -/
def AristotelianGroundingEverywhere (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) : Prop :=
  ∀ u p, AristotelianGroundingFor F PowerFor u p

namespace Control

open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 gFrame allC)

/-- Existence for the separator: `g` exists at every world; `c` and `d` exist
at `a` and `z` and not at `b`. -/
def sepEx (v : V3) (x : Bg) : Prop := x = .g ∨ v ≠ .b

/-- The separator frame: three mutually accessible worlds, existence `sepEx`,
no giving. -/
def sepFrame : CausalityFrame V3 Bg Unit Bool :=
  gFrame (fun _ _ => True) sepEx (fun _ _ _ => False)

/-- `g` has, at `a`, a power for whatever holds at `b`, and, at `b`, a power
for whatever holds at `a`; nothing else has a power. In particular nothing at
`a` has a power for `z` obtaining. -/
def sepPower (u : V3) (y : Bg) (p : V3 → Prop) : Prop :=
  y = .g ∧ ((u = .a ∧ p .b) ∨ (u = .b ∧ p .a))

/-- On one frame with contingent concreta (`c`, `d` exist at `a` and not at
`b`), the joint absence of the actual contingent concreta is possible at `a`
(so P1′ is not vacuous), some concrete being is contingent at `a`, the three
single-proposition grounding premises hold at `a`, and the universal
principle fails: `z` obtaining is possible at `a`, fails at `a`, and nothing at
`a` has a power for it. -/
def GroundingInstancesWithoutUniversal : Prop :=
  PossiblyNoActualContingentConcrete sepFrame allC .a ∧
  SomeContingentConcreteAt sepFrame allC .a ∧
  ActualAbsenceGrounded sepFrame sepPower allC .a ∧
  ActualityGroundedAtAbsenceWorlds sepFrame sepPower allC .a ∧
  GlobalAbsenceGrounded sepFrame sepPower allC .a ∧
  ¬ AristotelianGroundingEverywhere sepFrame sepPower

/-- The universal principle is satisfiable on the same frame: if `g`, which
exists at every world, has at every world a power for every proposition. -/
def UniversalGroundingSatisfiable : Prop :=
  AristotelianGroundingEverywhere sepFrame (fun _ y _ => y = .g)

end Control

/-- Restated-premise controls: the three registered equivalences (each by
`Iff.rfl` over the stated carrier), the separator for the grounding
instances, and satisfiability of the universal grounding principle. -/
def RestatedPremisesControls : Prop :=
  (∀ (B R : Type) (Participated : B → Prop) (CausesIn : B → B → R → Prop) (esse : R),
    ParticipatedHasOtherCause Participated CausesIn esse ↔
      ParticipatedEsseHasDistinctCause Participated CausesIn esse) ∧
  (∀ (B R Episode : Type) (I : IdeaFrame B R Episode),
    MeditatorThinks I ↔ SelectedBearsOccurringThought I.Occurs I.Bears I.me) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (concrete : B → Prop)
    (grounds : W → B → B → Prop) (w : W),
    SomeContingentConcreteAt F concrete w ↔
      SomeActualContingentAt (groundProfile F concrete grounds) w) ∧
  Control.GroundingInstancesWithoutUniversal ∧
  Control.UniversalGroundingSatisfiable

end TruthCore.Causality.RestatedPremises
