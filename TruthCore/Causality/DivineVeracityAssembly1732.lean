module

public import TruthCore.Causality.DivineVeracityContent1410

/-! #1732 assembly of the #1410 individuated-content assertion routes.

The two content routes and the legacy representation step are already checked
separately in `TruthCore.Results.Causality.DivineVeracityContent1410`. This
module adds only the joint-witness proposition for the assembled chain: ONE
signature, ONE content semantics, ONE designated world, ONE content-attitude
profile and the legacy attitudes induced from it. No new attitude, norm,
cognition or representation primitive is introduced. Analyst formulation,
attribution deferred; see docs/notes/divine-veracity-1410.md. -/

@[expose] public section
namespace TruthCore.Causality.DivineVeracityAssembly1732
open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1
open TruthCore.Causality.DivineVeracity1410
open TruthCore.Causality.DivineVeracityContent1410
open TruthCore.Causality.DivineVeracityContent1410.Control

/-- The assembled chain is jointly nonvacuous at one bearer, world and content
profile: in the existing selective sample (`Control.selective`, bearer `true`,
designated world `false`, tagged content `a`), every premise of BOTH content
routes holds together with the one-way assertion representation for the
existentially erased legacy attitudes `erase σ semantics false selective`;
that legacy profile actually asserts the truth condition of `a`, and the exact
legacy target `GodAssertsOnlyTruth` holds of it. The representation conjunct
is for this induced legacy profile only, not for an arbitrary given `Veracity`.
The finite sample is a structural interpretation, not a model of divine
cognition, moral permission or historical assertion. -/
def AssembledJointWitness : Prop :=
  σ.IsGod true ∧ σ.HasClassicalAttributes true ∧
  selective.Asserts true a ∧
  ContentSincere σ selective ∧
  ScopedAccuracy σ semantics false selective domain ∧
  AssertionsInDomain σ selective domain ∧
  CounterComplete σ semantics false selective ∧
  NoContraryAssertion σ semantics selective ∧
  AssertionRepresentation σ semantics false selective (erase σ semantics false selective) ∧
  (erase σ semantics false selective).Asserts true (semantics.trueAt false a) ∧
  GodAssertsOnlyTruth σ (erase σ semantics false selective)

end TruthCore.Causality.DivineVeracityAssembly1732
