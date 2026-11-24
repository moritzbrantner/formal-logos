module

public import TruthCore.Causality.NecessarySenseFork

/-!
# The classical-God root and the box K node of the sense fork (#1926, phase 0)

Analyst formulation, attribution deferred. `NecessaryClassicalGodRootAt`
(STMT-NECESSARY-CLASSICAL-GOD-ROOT) and `NecessaryRootBoxK`
(STMT-NECESSARY-ROOT-BOX-K) are stated over the SAME `Signature`, the SAME
`Profile W σ.Being` and the SAME world `w`. The necessity clause of the first
is `NecessaryAt m.ontic w n`, which is the box-existence of the second by
`necessaryAt_iff_boxExistsAt` (`Iff.rfl`), over the same frame `m.ontic.frame`.
So the box K node is a structural projection of the classical-God root; the
projection is proved in `TruthCore.Results.Causality.NecessaryClassicalGodRootBoxK`.

This module only adds the strictness control of that projection: a one-point
model in which the box K node holds and the classical-God root fails. The
model is a statement about this formal interpretation only.
-/

@[expose] public section

namespace TruthCore.Causality.NecessaryClassicalGodRootBoxK
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Latin.Aquinas.SummaTheologiae

namespace Separation

/-- A q.3 a.4 profile on the one-point model of `NecessarySenseFork.Control`:
the one being is in act in the one respect, and its represented esse and
essence coincide. No source reading. -/
def unitQ3Profile : PrimaPars.Question3.Article4.Profile Unit Unit Unit where
  InAct := fun _ _ => True
  CausesIn := fun _ _ _ => False
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  essentialPrinciplesAloneSufficeForEsse := fun _ => True
  esse := ()

/-- Strictness control of the projection (formal interpretation only): on the
one-point model of `NecessarySenseFork.Control` the box K node holds, while the
classical-God root fails once the supplied intellect predicate is empty (the
eighth of the nine case predicates). So the box K node does not entail the
classical-God root: the root's nine predicates, perfection, maximum, firstness,
esse/essence identity, matter/form exclusion and remoteness are content the
box K node lacks. -/
def Separator : Prop :=
  NecessaryRootBoxK NecessarySenseFork.Control.unitSignature
      NecessarySenseFork.Control.unitProfile () (fun _ _ => False) ∧
    ¬ NecessaryClassicalGodRootAt NecessarySenseFork.Control.unitSignature
      NecessarySenseFork.Control.unitProfile () unitQ3Profile
      (fun _ _ => True) (fun _ _ => False) (fun _ _ _ => False) (fun _ _ => False)
      (fun _ _ => False) (fun _ => False) (fun _ => False) (fun _ => True) (fun _ => True)
      (fun _ => False) (fun _ => True)

end Separation
end TruthCore.Causality.NecessaryClassicalGodRootBoxK
