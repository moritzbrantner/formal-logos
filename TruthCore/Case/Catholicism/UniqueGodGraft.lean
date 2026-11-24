module

public import TruthCore.Case.Catholicism.StagesOneTwo
public import TruthCore.Logic.StrengthComparison

/-!
# From the unique classical God to the root's attribute premise (#1926 graft)

Analyst formulation, attribution deferred. The stage 1–2 same-witness routes
conclude `UniqueClassicalGodExists σ` (`20a2b6a3`): one `g` is God, is the
only being satisfying `σ.IsGod` (`IsTheOneGod`), and has the skeleton's
classical attributes. The root arguments consume `GodHasClassicalAttributes σ`
(`d5ac1620`): every being satisfying `σ.IsGod` has them. The step between them
is a uniqueness transfer: any God is `g`. Without uniqueness it fails
(`Model.TwoGodsOneClassical`).

The strong version adds exactly `UniqueGodExists σ`: some being is God and is
the only being satisfying `σ.IsGod` (#1598 certified difference,
`uniqueClassicalGodOverAttributes`).

Every model is a finite structural surrogate: the signature's other fields are
unused placeholders, not historical or religious assertions. See
`docs/notes/orphan-graft-map.md`.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.UniqueGodGraft

open TruthCore.Case.Catholicism
open TruthCore.Logic.StrengthComparison

/-- Difference statement: some being is God and is the only being satisfying
`σ.IsGod`. It says nothing about the classical attributes. -/
def UniqueGodExists (σ : Signature) : Prop :=
  ∃ g, σ.IsGod g ∧ IsTheOneGod σ.IsGod g

/-- `UniqueClassicalGodExists` over `GodHasClassicalAttributes`; difference:
`UniqueGodExists`. No background. -/
def uniqueClassicalGodOverAttributes (σ : Signature) : ComparisonSpec where
  stronger := UniqueClassicalGodExists σ
  weaker := GodHasClassicalAttributes σ
  delta := UniqueGodExists σ

/-- Exact factorization: on every signature, a unique classical God exists iff
every God has the classical attributes and a unique God exists. -/
def UniqueClassicalGodOverAttributesExact : Prop :=
  ∀ σ : Signature, UniqueClassicalGodExists σ ↔
    GodHasClassicalAttributes σ ∧ UniqueGodExists σ

namespace Model

/-- A signature on `Bool` with the given God and attribute predicates; every
other field is an empty placeholder. -/
def sigOf (isGod attrs : Bool → Prop) : Signature where
  Being := Bool
  IsGod := isGod
  HasClassicalAttributes := attrs
  RevealsRecognizably _ := False
  jesus := false
  ClaimedDivineAuthority _ := False
  RoseFromTheDead _ := False
  Society := Unit
  catholicChurch := ()
  Founded _ _ := False
  VisibleWithAuthority _ := False
  FoundedAsTeachingAuthority _ _ := False
  DefinitivelyProposesAsRevealed _ _ := False
  creedOneGodFatherAlmightyCreator := False
  creedOneLordJesusChristOnlyBegottenConsubstantial := False
  creedIncarnateOfSpiritAndVirginMary := False
  creedCrucifiedUnderPilateSufferedBuried := False
  creedRoseOnTheThirdDay := False
  creedAscendedSeatedAtRightHand := False
  creedWillComeToJudgeKingdomWithoutEnd := False
  creedHolySpiritLordGiverOfLife := False
  creedOneHolyCatholicApostolicChurch := False
  creedOneBaptismForForgiveness := False
  creedResurrectionOfTheDead := False
  creedLifeOfTheWorldToCome := False

/-- `true` alone is God and has the classical attributes. -/
def oneGod : Signature := sigOf (fun b => b = true) (fun b => b = true)

/-- Both beings satisfy `IsGod`; only `true` has the classical attributes. -/
def twoGods : Signature := sigOf (fun _ => True) (fun b => b = true)

/-- **Nonvacuity**: with one God having the attributes, both the premise and
the conclusion of the transfer hold. -/
def OneClassicalGod : Prop :=
  UniqueClassicalGodExists oneGod ∧ GodHasClassicalAttributes oneGod

/-- **Omission of uniqueness**: some God has the classical attributes, yet not
every God does, and the unique-God premise fails. The `IsTheOneGod` conjunct
is what the transfer uses. -/
def TwoGodsOneClassical : Prop :=
  (∃ g, twoGods.IsGod g ∧ twoGods.HasClassicalAttributes g) ∧
  ¬ GodHasClassicalAttributes twoGods ∧ ¬ UniqueClassicalGodExists twoGods

/-- Both beings satisfy `IsGod` and both have the classical attributes. -/
def twoClassicalGods : Signature := sigOf (fun _ => True) (fun _ => True)

/-- **Strictness** of the strength order: every God has the classical
attributes, non-vacuously, while the unique-God premise fails. -/
def TwoClassicalGods : Prop :=
  GodHasClassicalAttributes twoClassicalGods ∧ (∃ g, twoClassicalGods.IsGod g) ∧
  ¬ UniqueClassicalGodExists twoClassicalGods

/-- The certificate: nonvacuity, the omission model and the strictness model. -/
def Controls : Prop := OneClassicalGod ∧ TwoGodsOneClassical ∧ TwoClassicalGods

end Model

end TruthCore.Case.Catholicism.UniqueGodGraft
