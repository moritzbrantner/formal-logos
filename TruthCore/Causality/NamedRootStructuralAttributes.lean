module

public import TruthCore.Causality.RootIntellectWill

@[expose] public section

namespace TruthCore.Causality.NamedRootStructuralAttributes

/-- Matter-form composition is one sufficient condition for composition
under the supplied predicates. -/
def MatterFormIsComposite {B : Type} (MatterForm Composite : B → Prop) : Prop :=
  ∀ x, MatterForm x → Composite x

end TruthCore.Causality.NamedRootStructuralAttributes
