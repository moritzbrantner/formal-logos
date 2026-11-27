import TruthCore.Causality.CogitoNecessaryConcrete

namespace TruthCore.Results.Causality.CogitoAncestorNecessaryConcrete
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.CogitoNecessaryConcrete (NecessaryConcreteAncestorOfThinker
  ThinkerAncestryRootFork ThinkerAncestryGrounded necessaryConcreteAt_of_ancestor)

/-- The Cogito's necessary concrete ground-ancestor is a witness of the shared
`NecessaryConcreteAt` on the same profile, world and occurrence data. The
vocabulary lemma keeps the ancestor `x` and its concreteness, existence at `w`
and `NecessaryAt` at `w`, and drops the bearer, episode and ancestry facts. -/
theorem necessaryConcreteOfThinkerAncestor {W B Episode : Type} {m : Profile W B}
    {Occurs : Episode → Prop} {Bears : B → Episode → Prop} {w : W}
    (h : NecessaryConcreteAncestorOfThinker m Occurs Bears w) :
    NecessaryConcreteAt m w := by
  sorry

/-- The thinker-local anti-brute-root principle closes the contingent horn of
the thinker-local fork: a contingent concrete root among a bearer's
ground-ancestors would have an actual concrete ground at `w`, contradicting
its rootness. No excluded middle is used; the fork is a premise. -/
theorem necessaryAncestorOfFork {W B Episode : Type} (m : Profile W B)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hFork : ThinkerAncestryRootFork m Occurs Bears w)
    (hGrounded : ThinkerAncestryGrounded m Occurs Bears w) :
    NecessaryConcreteAncestorOfThinker m Occurs Bears w := by
  sorry

end TruthCore.Results.Causality.CogitoAncestorNecessaryConcrete
