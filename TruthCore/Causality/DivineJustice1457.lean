module

public import TruthCore.Causality.DivineVeracity1410

/-! Divine justice as wisdom-governed conformity to due order (#1457).

Analyst reconstruction of *Summa theologiae* I q.21 a.1 co. and ad 2–3, a.2 co.
and a.4 co.; attribution deferred (owner direction 2026-11-05). Navigation only:
a.1 ad 2 says God cannot will anything but what His wisdom approves, and that
this is "as it were" His law of justice; a.2 says His justice establishes things
in the order conformable to that rule; a.1 ad 3 derives what is due to creatures
from their ordering under divine wisdom. No claim record is created.

Two senses of divine justice are kept apart (see the JUSTICE disambiguation):

* JUSTICE_1, `GodActsJustly`: every act a classified GOD_4 wills accords with
  the order due to things. It says nothing about which acts are willed.
* JUSTICE_2, `GodRendersAllDue`: every act whose doing is due to some being is
  willed by such a GOD_4 (distributive completeness). The problem of the
  afflicted just (q.21 a.4 obj. 3) bears on this reading.

`Fitting` is a primitive standard of due order. It is **not** defined as what
any agent wills: the voluntarist reading that makes it so is a separate,
explicit assumption (`VoluntaristFitting`), under which JUSTICE_1 holds for
every will profile and so discriminates nothing (`Control`, and the
`voluntaristTrivializes` result). The route to the existing veracity premise
`GodAssertionsPermitted` passes through two further OPEN bridges: genuine
assertion is a willed act, and a fitting assertion is morally permissible.
See `docs/notes/divine-justice-1457.md`. -/

@[expose] public section
namespace TruthCore.Causality.DivineJustice1457
open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1
open TruthCore.Causality.DivineVeracity1410

/-- Primitive interface for wisdom-governed justice over the skeleton signature.

* `Act` — acts an agent can will: bestowing, preserving, withholding, asserting.
* `Wills g a` — `g` effectively wills (chooses) act `a`; not a mere wish.
* `Approves g a` — `g`'s practical wisdom judges `a` to accord with its rule.
  An intellectual judgement, distinct from willing (q.21 a.2 ad 1).
* `Fitting a` — `a` accords with the order due to things, by their natures and
  conditions and their ordering to the divine good. A standard, not a causal
  arrow and not defined by anyone's willing or approving.
* `DueTo x a` — the doing of `a` is due to being `x` by its nature or condition.
* `assertion g p` — the act of `g`'s genuinely asserting `p`.

No field law relates these; every link is a separate premise. -/
structure Order (σ : Signature) where
  Act : Type
  Wills : σ.Being → Act → Prop
  Approves : σ.Being → Act → Prop
  Fitting : Act → Prop
  DueTo : σ.Being → Act → Prop
  assertion : σ.Being → Prop → Act

/-- OPEN reading of q.21 a.1 ad 2: a GOD_4 with classical attributes wills only
what its wisdom approves. Whether will is *governed* by wisdom, rather than
merely coextensive with it, is not encoded. -/
def GodWillsOnlyApproved (σ : Signature) (O : Order σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ a, O.Wills g a → O.Approves g a

/-- OPEN wisdom-accuracy premise: whatever such a GOD_4's wisdom approves
accords with the order due to things. This is the non-voluntarist content of
the "law of justice": approval tracks a standard it does not create by fiat. -/
def GodApprovalTracksOrder (σ : Signature) (O : Order σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ a, O.Approves g a → O.Fitting a

/-- JUSTICE_1 (conformity): every act such a GOD_4 wills is fitting. Silent on
whether any act is willed and on whether every due is rendered. -/
def GodActsJustly (σ : Signature) (O : Order σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ a, O.Wills g a → O.Fitting a

/-- JUSTICE_2 (distributive completeness): such a GOD_4 wills every act whose
doing is due to some being. A strong reading, not entailed by JUSTICE_1. -/
def GodRendersAllDue (σ : Signature) (O : Order σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ x a, O.DueTo x a → O.Wills g a

/-- OPEN action-theoretic bridge: a genuine assertion by a GOD_4 with classical
attributes is a willed act of that same speaker. -/
def GodAssertionIsWilled (σ : Signature) (V : Veracity σ) (O : Order σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Asserts g p →
    O.Wills g (O.assertion g p)

/-- OPEN normative bridge: a fitting act of assertion is morally permissible for
its speaker in the fixed context (the veracity `Grounds.Permitted` relation).
Under the voluntarist reading this becomes a divine-command account of
permission; under an independent `Fitting` it is a substantive claim that due
order is right-making for assertion. -/
def FittingAssertionPermitted (σ : Signature) (O : Order σ) (G : Grounds σ) : Prop :=
  ∀ g p, O.Fitting (O.assertion g p) → G.Permitted g p

/-- The voluntarist reading of due order, as an explicit assumption: an act is
fitting exactly when some classified GOD_4 wills it. -/
def VoluntaristFitting (σ : Signature) (O : Order σ) : Prop :=
  ∀ a, O.Fitting a ↔ ∃ g, σ.IsGod g ∧ σ.HasClassicalAttributes g ∧ O.Wills g a

namespace Control
open TruthCore.Causality.NamingVeracityBatch1.Control

/-- The veracity skeleton: one classified GOD_4 bearer (`true`). -/
abbrev σ : Signature := sig True True (fun p => p)

/-- Acts are Booleans: `true` is the sample assertion and the fitting act,
`false` an act that is unfitting whenever `Fitting` is the identity. -/
def order (W A F D : Bool → Prop) : Order σ where
  Act := Bool
  Wills _ a := W a
  Approves _ a := A a
  Fitting a := F a
  DueTo _ a := D a
  assertion _ _ := true

/-- A veracity with the classified bearer asserting exactly `True`. -/
def v : Veracity σ := veracity True True (fun p => p) (fun p => p) (fun p => p) (fun p => p)

/-- Permission grounds with the supplied permission predicate on contents. -/
def grounds (P : Prop → Prop) : Grounds σ where
  Permitted _ p := P p
  Defect _ _ := False
  Present _ p := p
  Apprehends _ p := p

/-- Joint structural sample: a classified bearer asserts `True`, wills exactly
the fitting act, and every route premise and the conclusion hold. -/
def Joint : Prop :=
  let O := order (· = true) (· = true) (· = true) (· = true)
  σ.IsGod true ∧ σ.HasClassicalAttributes true ∧ v.Asserts true True ∧
  O.Wills true true ∧
  GodWillsOnlyApproved σ O ∧ GodApprovalTracksOrder σ O ∧ GodActsJustly σ O ∧
  GodRendersAllDue σ O ∧ GodAssertionIsWilled σ v O ∧
  FittingAssertionPermitted σ O (grounds fun _ => True) ∧
  GodAssertionsPermitted σ v (grounds fun _ => True)

/-- Each omission keeps the other premises of its argument and loses the
conclusion; each model retains the classified bearer and its assertion. -/
def Omissions : Prop :=
  (∃ O : Order σ, GodApprovalTracksOrder σ O ∧ ¬ GodActsJustly σ O) ∧
  (∃ O : Order σ, GodWillsOnlyApproved σ O ∧ ¬ GodActsJustly σ O) ∧
  (∃ O : Order σ, ∃ G : Grounds σ, GodActsJustly σ O ∧
    FittingAssertionPermitted σ O G ∧ ¬ GodAssertionsPermitted σ v G) ∧
  (∃ O : Order σ, ∃ G : Grounds σ, GodActsJustly σ O ∧
    GodAssertionIsWilled σ v O ∧ ¬ GodAssertionsPermitted σ v G)

/-- Wisdom-governed conformity (JUSTICE_1 with both of its premises) does not
give distributive completeness (JUSTICE_2): an act is due and not willed. -/
def ConformityNotCompleteness : Prop :=
  ∃ O : Order σ, GodWillsOnlyApproved σ O ∧ GodApprovalTracksOrder σ O ∧
    GodActsJustly σ O ∧ (∃ x a, O.DueTo x a) ∧ ¬ GodRendersAllDue σ O

/-- Under the voluntarist reading the classified bearer may will the act that
is unfitting under the independent standard, and JUSTICE_1 still holds: the
two readings of `Fitting` disagree about the same will profile. -/
def VoluntaristDivergence : Prop :=
  let W : Bool → Prop := fun _ => True
  VoluntaristFitting σ (order W W W W) ∧ GodActsJustly σ (order W W W W) ∧
    ¬ GodActsJustly σ (order W W (· = true) W)

def Certificate : Prop :=
  Joint ∧ Omissions ∧ ConformityNotCompleteness ∧ VoluntaristDivergence
end Control
end TruthCore.Causality.DivineJustice1457
