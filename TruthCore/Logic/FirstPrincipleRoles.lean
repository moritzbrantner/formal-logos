module

public import TruthCore.Explanation.PSRStrength

/-!
Scoped analyst vocabulary for #1659. These interfaces separate an ontic
requirement from an argument's premise membership and a performance-occurrence
link. They do not identify those relations or supply their application bridges.
The existing `RegressDomains.Justification.inferential` and
`Alternatives.Retorsion.PresuppositionLink` are reused by corpus records.
-/

@[expose] public section

namespace TruthCore.Logic.FirstPrincipleRoles

/-- Conditions are interpreted states of affairs, not premise tokens. At `w`,
`requires w d p` means that the actuality of prerequisite `p` is required for
that of dependent `d`. It is primitive: no truth-functional, modal, causal or
priority definition of this relation is asserted here. Even compatibility with
`obtains` is a separate constraint below. -/
structure OnticRequirements (World Condition : Type) where
  obtains : World → Condition → Prop
  requires : World → Condition → Condition → Prop

/-- A supplied requirement profile is respected at this world. This condition
constrains the primitive relation; it does not define it by material implication
or impose transitivity, asymmetry, well-foundedness or modal necessity. -/
def RequirementsRespectedAt {W C : Type} (R : OnticRequirements W C) (w : W) : Prop :=
  ∀ d p, R.requires w d p → R.obtains w d → R.obtains w p

open TruthCore.Explanation.PSRStrength

/-- The two premises of one local rejection on inexplicability grounds. The
first supplies a local explanatory demand; the second denies any admitted
explanation, not merely any known explanation. This is an analyst deductive
pattern, not the general dialectical warrant for PSR or an attribution of it.
`Explained` retains the supplied arena relation and its open adequacy burden. -/
structure LocalInexplicabilityRejection {W B F : Type}
    (A : Arena W B F) (w : W) (f : F) : Prop where
  demand : A.holds w f → Explained A w f
  unexplained : ¬ Explained A w f

end TruthCore.Logic.FirstPrincipleRoles
