module

public import TruthCore.Logic.ExcludedMiddle

/-!
# Is the Euthyphro dilemma exhaustive?

Analyst formulation; attribution deferred. Classical theists answer the
dilemma with an identity: God is his own goodness (ST I q.3, q.6 a.3 are unread
leads). This module encodes the dilemma's coverage claim so that it can fail.

`DependenceFrame` names God, God's nature, God's act of approving and the
standard of goodness (what goodness is), with one primitive relation:

* `DependsFor x y`: x is what it is because of y. This is constitutive,
  explanatory dependence. Example: a club's rule depends for its content on the
  members' vote. Counterexample: the vote's having occurred does not depend for
  its content on the rule. It is distinct from dependence for being on an
  agent cause (`CausalityFrame.DependsForBeing`, which concerns existence, not
  content) and from strict ground between facts (`StrictlyGrounds`). No
  structural property is built in. Asymmetry is an explicit premise.

The horns are typed. Horn 1 (`IndependentStandard`) says goodness is distinct
from God and does not depend on him for what it is. Horn 2
(`ConstitutedByApproval`) says goodness depends for what it is on God's approval,
or simply is that approval. Coverage needs explicit excluded middle plus two
background premises:

* distinctness: goodness is neither God nor God's nature;
* `DistinctDependenceThroughApproval`: whatever else is distinct from God, his
  nature and his approval, and depends on God for what it is, depends on his
  approval.

Dropping distinctness (the identity reply) or the second premise (a distinct
standard depending on the nature, not the will) each leaves neither horn true,
in a finite model. The profile frame of `TruthCore.Ethics.Euthyphro` is
extensional and cannot express this dependence. No bridge between the two
frames is assumed.

`ExplanationOrder` was considered for reuse: its edges order topics of moral
sentences for the Blackburn comparison, not a standard and an act of approval,
so it is not reused.
-/

@[expose] public section

namespace TruthCore.Ethics.EuthyphroDilemma

open TruthCore.Logic

/-- God, God's nature, God's approving and the standard of goodness, with
constitutive dependence as the only primitive relation. -/
structure DependenceFrame where
  Entity : Type
  god : Entity
  nature : Entity
  approval : Entity
  goodness : Entity
  DependsFor : Entity → Entity → Prop

section
variable (d : DependenceFrame)

/-- Horn 1: goodness is a standard distinct from God that does not depend on
God for what it is. -/
def IndependentStandard : Prop :=
  d.goodness ≠ d.god ∧ ¬ d.DependsFor d.goodness d.god

/-- Horn 2: goodness depends for what it is on God's approval, or is that
approval. -/
def ConstitutedByApproval : Prop :=
  d.DependsFor d.goodness d.approval ∨ d.goodness = d.approval

/-- The dilemma's coverage claim. -/
def HornsCover : Prop := IndependentStandard d ∨ ConstitutedByApproval d

/-- The dilemma fails in this frame: neither horn holds. -/
def NeitherHorn : Prop := ¬ IndependentStandard d ∧ ¬ ConstitutedByApproval d

/-- Distinctness: goodness is neither God nor God's nature. -/
def GoodnessDistinctFromGod : Prop := d.goodness ≠ d.god ∧ d.goodness ≠ d.nature

/-- Whatever is distinct from God, his nature and his approval, and depends on
God for what it is, depends on God's approval. -/
def DistinctDependenceThroughApproval : Prop :=
  ∀ x, x ≠ d.god → x ≠ d.nature → x ≠ d.approval →
    d.DependsFor x d.god → d.DependsFor x d.approval

/-- Identity premise: the standard of goodness is God's nature. -/
def GoodnessIsDivineNature : Prop := d.goodness = d.nature

/-- Simplicity-identity premise: God is his own nature. -/
def GodIsOwnNature : Prop := d.nature = d.god

/-- God's approving depends for what it is on God's nature. -/
def ApprovalFollowsNature : Prop := d.DependsFor d.approval d.nature

/-- Constitutive dependence is asymmetric (hence irreflexive). -/
def DependenceAsymmetric : Prop := ∀ x y, d.DependsFor x y → ¬ d.DependsFor y x

end

/-! ## Relocation: which nature God has -/

/-- Profiles of which nature God has, with the goodness standard per profile. -/
structure NatureProfiles where
  Entity : Type
  Profile : Type
  natureAt : Profile → Entity
  goodnessAt : Profile → Entity

def IdentityInEachProfile (n : NatureProfiles) : Prop :=
  ∀ w, n.goodnessAt w = n.natureAt w

/-- God's nature is the same in every profile. -/
def DivineNatureNecessary (n : NatureProfiles) : Prop :=
  ∀ w v, n.natureAt w = n.natureAt v

/-- The relocated arbitrariness: goodness differs between profiles. -/
def GoodnessVariesWithNature (n : NatureProfiles) : Prop :=
  ∃ w v, n.goodnessAt w ≠ n.goodnessAt v

/-! ## Property collapse -/

/-- God, the goodness by which God is good, and the universal that good things
share, with a property predicate. -/
structure PropertyFrame where
  Entity : Type
  god : Entity
  divineGoodness : Entity
  goodnessUniversal : Entity
  IsProperty : Entity → Prop

/-! ## Finite models -/

inductive Item | god | nature | approval | standard deriving DecidableEq

/-- Identity model: goodness and nature are God; approval depends on God. -/
def identityFrame : DependenceFrame where
  Entity := Item
  god := .god
  nature := .god
  approval := .approval
  goodness := .god
  DependsFor := fun x y => x = .approval ∧ y = .god

/-- Distinct exemplar standard: goodness is a standard depending on God (who is
his nature) but not on his approval. -/
def exemplarFrame : DependenceFrame where
  Entity := Item
  god := .god
  nature := .god
  approval := .approval
  goodness := .standard
  DependsFor := fun x y => (x = .approval ∨ x = .standard) ∧ y = .god

/-- Non-simple model: goodness is God's nature, which is distinct from God and
does not depend on him. -/
def nonSimpleFrame : DependenceFrame where
  Entity := Item
  god := .god
  nature := .nature
  approval := .approval
  goodness := .nature
  DependsFor := fun x y => x = .approval ∧ y = .nature

/-- Voluntarist model: goodness is a distinct standard depending on approval. -/
def voluntaristFrame : DependenceFrame where
  Entity := Item
  god := .god
  nature := .god
  approval := .approval
  goodness := .standard
  DependsFor := fun x y => (x = .standard ∧ (y = .approval ∨ y = .god))

/-- Contingent divine nature: two profiles with different natures. -/
def contingentNature : NatureProfiles where
  Entity := Bool
  Profile := Bool
  natureAt := id
  goodnessAt := id

def collapseModel : PropertyFrame where
  Entity := Item
  god := .god
  divineGoodness := .god
  goodnessUniversal := .standard
  IsProperty := fun x => x = .standard

/-- Controls for the coverage question. General conjuncts: identity with a
necessary nature leaves goodness fixed across nature profiles; the property
collapse needs the identification of God's goodness with the shared universal.
Finite conjuncts: identity model (all identity premises, neither horn,
distinctness false); exemplar model (distinctness true, through-approval false,
neither horn); non-simple model (identity and approval following nature hold,
God is not his nature, horn 1 holds); voluntarist model (distinctness and
through-approval hold, horn 2 holds); a contingent-nature model (identity in
each profile, nature not necessary, goodness varies); and a property model
(God is his goodness, that goodness is not the shared universal, which is a
property, and God is not). These are formal interpretations only. -/
def DilemmaControls : Prop :=
  (∀ n : NatureProfiles, IdentityInEachProfile n → DivineNatureNecessary n →
      ¬ GoodnessVariesWithNature n) ∧
  (∀ p : PropertyFrame, p.god = p.divineGoodness →
      p.divineGoodness = p.goodnessUniversal → p.IsProperty p.goodnessUniversal →
      p.IsProperty p.god) ∧
  (GoodnessIsDivineNature identityFrame ∧ GodIsOwnNature identityFrame ∧
    ApprovalFollowsNature identityFrame ∧ DependenceAsymmetric identityFrame ∧
    DistinctDependenceThroughApproval identityFrame ∧
    ¬ GoodnessDistinctFromGod identityFrame ∧ NeitherHorn identityFrame) ∧
  (GoodnessDistinctFromGod exemplarFrame ∧ ApprovalFollowsNature exemplarFrame ∧
    DependenceAsymmetric exemplarFrame ∧
    ¬ DistinctDependenceThroughApproval exemplarFrame ∧ NeitherHorn exemplarFrame) ∧
  (GoodnessIsDivineNature nonSimpleFrame ∧ ApprovalFollowsNature nonSimpleFrame ∧
    DependenceAsymmetric nonSimpleFrame ∧ ¬ GodIsOwnNature nonSimpleFrame ∧
    IndependentStandard nonSimpleFrame) ∧
  (GoodnessDistinctFromGod voluntaristFrame ∧
    DistinctDependenceThroughApproval voluntaristFrame ∧
    ConstitutedByApproval voluntaristFrame) ∧
  (IdentityInEachProfile contingentNature ∧ ¬ DivineNatureNecessary contingentNature ∧
    GoodnessVariesWithNature contingentNature) ∧
  (collapseModel.god = collapseModel.divineGoodness ∧
    collapseModel.divineGoodness ≠ collapseModel.goodnessUniversal ∧
    collapseModel.IsProperty collapseModel.goodnessUniversal ∧
    ¬ collapseModel.IsProperty collapseModel.god)

end TruthCore.Ethics.EuthyphroDilemma
