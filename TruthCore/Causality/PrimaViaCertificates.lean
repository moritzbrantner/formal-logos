module

public import TruthCore.Causality.BruteFoundationBoundary
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency

/-!
# Prima via certificates: vocabulary for three inconsistencies and the per se history (#1751)

Analyst formulations, attribution deferred. Three new open propositions used by
the batch `specs/prima-via-certificates.toml`, which certifies the inconsistent
premise sets found by the 2026-11-18 cluster assessments of the prima via route
to GOD_4 exists (notes `prima-via-strength-consumers.md`, lane A, and
`causal-dependence-support-investigation.md`, lane B), the bypass deriving the
per se regress premise from well-founded causal predecessors, and the converse
selection that rebinds well-founded predecessors to the per se regress premise.

Each definition is an explicit parameterized proposition, not an opaque flag:

* `NothingCanBeWithoutItself` constrains the primitive `CanBeWithout`
  (DEF-CAN-BE-WITHOUT, "y can be while x is not") on the diagonal;
* `ReciprocalCrossRespectMoving` is an existence claim about the shared
  `MovesIn`, `InAct` and `InPotency` vocabulary of the prima via;
* `HistoryEdgesArePerSeLinks` is the converse of `PerSeLinksIncluded`
  (DEF `6c9be385`): it selects the studied causal-history relation as per se
  ordered efficient causing.

None of the three is established here; none is attributed to a source.
-/

@[expose] public section

namespace TruthCore.Causality.PrimaViaCertificates

universe u v

/-- Nothing can be without itself: for no `x` can `x` be while `x` is not.

A meaning-postulate candidate for the primitive `CanBeWithout` of
DEF-CAN-BE-WITHOUT ("`CanBeWithout y x`: `y` can be while `x` is not"). On that
gloss, `CanBeWithout x x` asks for a possible situation in which `x` both is and
is not, so the postulate is the diagonal instance of non-contradiction under the
definition's reading. It is recorded as an explicit open statement because the
Lean primitive does not build it in. -/
def NothingCanBeWithoutItself {B : Sort u} (CanBeWithout : B → B → Prop) : Prop :=
  ∀ x, ¬ CanBeWithout x x

/-- Reciprocal cross-respect moving: two distinct beings each move the other,
each in a respect in which the mover is in act and the moved is in potency.
`y`, in act in `r`, moves `x`, which is in potency in `r`; and `x`, in act in
`r'`, moves `y`, which is in potency in `r'`.

Analyst observation premise, unattributed. Candidate instances: two people each
telling the other something the other did not know (each is reduced from
potency to act in knowing by a teller who actually knows it); mutual heating or
pushing of two bodies in contact, where the mover is acted on in turn (Physics
III.2, 202a3-7, read as orientation only; no claim is recorded). Nothing here
requires `r ≠ r'`, and nothing requires the two movings to be per se ordered. -/
def ReciprocalCrossRespectMoving {B : Sort u} {R : Sort v}
    (InAct InPotency : B → R → Prop) (MovesIn : B → B → R → Prop) : Prop :=
  ∃ y x r r', y ≠ x ∧ InAct y r ∧ InPotency x r ∧ MovesIn y x r ∧
    InAct x r' ∧ InPotency y r' ∧ MovesIn x y r'

/-- Every edge of the studied causal history is a per se ordered
efficient-cause link: `cause y x → perSe y x`, on the same carrier and with the
same upstream orientation.

The converse of `PerSeLinksIncluded` (f10d5632). It is a selection of the
studied relation, parallel to the selection `HistoryEdgesAreEfficientCausings`
(57552dce), restricted to per se ordered causing (DEF `4a101a4c`). Together with
`PerSeLinksIncluded` it makes the studied relation exactly the per se link. It
says nothing about accidentally ordered series, which it leaves out of the
studied relation. -/
def HistoryEdgesArePerSeLinks {B : Sort u} (cause perSe : B → B → Prop) : Prop :=
  ∀ ⦃y x⦄, cause y x → perSe y x

/-! ## Finite control interpretations

Mathematical interpretations used by the omission and repair controls of the
batch. They are facts about these stated interpretations only, not claims about
which beings move, depend or ground. -/

namespace Control

namespace CausesIn

/-- `false` is the moved thing, `true` its mover, one respect. -/
def MovedIn (b : Bool) (_ : Unit) : Prop := b = false
/-- `true` moves `false`. -/
def MovesIn (a b : Bool) (_ : Unit) : Prop := a = true ∧ b = false
/-- Only `true` is in act. -/
def InAct (a : Bool) (_ : Unit) : Prop := a = true
/-- Everything can be in the one respect. -/
def CanBe (_ : Bool) (_ : Unit) : Prop := True
/-- Everything is in act. -/
def AllAct (_ : Bool) (_ : Unit) : Prop := True
/-- Nothing is moved. -/
def Never1 (_ : Bool) (_ : Unit) : Prop := False
/-- No pair stands in the relation. -/
def Never2 (_ _ : Bool) (_ : Unit) : Prop := False
/-- Adopted potency at this interpretation's act and capacity. -/
abbrev Pot := TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe

end CausesIn

namespace Reciprocity

/-- `b` is in act exactly in respect `b`. -/
def InAct (b r : Bool) : Prop := b = r
/-- `b` is in potency in the other respect. -/
def InPotency (b r : Bool) : Prop := ¬ b = r
/-- `a` moves `b` in `r` when `a` is in act and `b` in potency in `r`. -/
def MovesIn (a b r : Bool) : Prop := a = r ∧ ¬ b = r
/-- Nothing is in act or in potency. -/
def NeverAct (_ _ : Bool) : Prop := False
/-- Nothing moves anything. -/
def NeverMoves (_ _ _ : Bool) : Prop := False
/-- Nothing is prior to anything. -/
def NeverPrior (_ _ : Bool) : Prop := False
/-- Priority read as distinctness. -/
def Distinct (a b : Bool) : Prop := ¬ a = b
/-- Everything is prior to everything. -/
def AlwaysPrior (_ _ : Bool) : Prop := True

end Reciprocity

namespace Repair

open TruthCore.Causality.BruteFoundationBoundary (Profile)

/-- One world, two concreta: `false` grounds `true`. -/
def profile : Profile Unit Bool where
  ontic :=
    { frame := ⟨fun _ _ => True⟩
      ExistsAt := fun _ _ => True
      Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ a b => a = false ∧ b = true

/-- Reflexive dependence with one strict edge: `true` depends on `false`. -/
def DependsForBeing (x c : Bool) : Prop := x = c ∨ (x = true ∧ c = false)
/-- Being able to be without, read as non-dependence. -/
def CanBeWithout (y x : Bool) : Prop := ¬ DependsForBeing y x
/-- `false` causes the esse of `true`. -/
def CausesIn (a b : Bool) (_ : Unit) : Prop := a = false ∧ b = true

end Repair

end Control

end TruthCore.Causality.PrimaViaCertificates
