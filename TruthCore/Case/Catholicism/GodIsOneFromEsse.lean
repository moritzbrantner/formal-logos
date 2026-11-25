module

public import TruthCore.Case.Catholicism.MaximalBeingCauseExclusion
public import TruthCore.Causality.GodMaximalCausal
public import TruthCore.Causality.TermSenseForks3
public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.Round2PerfectionPrimacy

@[expose] public section

namespace TruthCore.Case.Catholicism.GodIsOneFromEsse
open TruthCore.Case.Catholicism
open TruthCore.Causality.GodMaximalCausal
open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.Round2Grounding
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Finite dictionaries. The two respects distinguish esse (true) from a
second respect at which the general genus-causality rule can fail. -/
def actual (_ _ : Bool) : Prop := True
def above (r x y : Bool) : Prop := r = true ∧ x = true ∧ y = false
def gives (c x r : Bool) : Prop := above r c x
def receives (x c : Bool) : Prop := gives c x true
def one (g : Bool) : Prop := g = true
def both (_ : Bool) : Prop := True
def neither (_ : Bool) : Prop := False
def flat (_ _ _ : Bool) : Prop := False
def opposite (x y : Bool) : Prop := x ≠ y
def reciprocal (c x _ : Bool) : Prop := opposite c x
def cyclic (_ x y : Bool) : Prop := opposite x y
def independent (_ _ : Bool) : Prop := False

/-- All three bundles have the same God and actual other here. The general
genus rule fails at the other respect. -/
def Joint : Prop :=
  SomeBeingMaximalInBeing actual above true ∧ GodIsMaximalInBeing one actual above true ∧
  MaximumHasNoDistinctEsseCause actual above gives true ∧ GodCausesBeingOfAllOthers one gives true ∧
  EsseEffectDependsOnItsCause gives true receives ∧ DistinctBeingsNotMutuallyDependent receives ∧
  GodIsOne one ∧ one true ∧ ¬ one false ∧ actual false true ∧ gives true false true ∧
  ¬ MaximumInGenusCausesAllInGenusReading actual above gives

/-- The first three rows omit respectively exclusion, maximal existence (or
God-to-maximality), and universal God causality. Each permits two Gods.
The final row keeps both maximality bundles, with two maxima and no God. -/
def MaximalControls : Prop :=
  (SomeBeingMaximalInBeing actual flat true ∧ GodIsMaximalInBeing both actual flat true ∧
    GodCausesBeingOfAllOthers both reciprocal true ∧ ¬ GodIsOne both) ∧
  (MaximumHasNoDistinctEsseCause actual cyclic reciprocal true ∧
    GodCausesBeingOfAllOthers both reciprocal true ∧ ¬ GodIsOne both) ∧
  (SomeBeingMaximalInBeing actual flat true ∧ GodIsMaximalInBeing both actual flat true ∧
    MaximumHasNoDistinctEsseCause actual flat flat true ∧ ¬ GodIsOne both) ∧
  (SomeBeingMaximalInBeing actual flat true ∧ GodIsMaximalInBeing neither actual flat true ∧
    MaximumHasNoDistinctEsseCause actual flat flat true ∧ GodCausesBeingOfAllOthers neither flat true ∧
    IsMaximumIn actual flat true false ∧ IsMaximumIn actual flat true true ∧
    GodIsOne neither ∧ ¬ ∃ g, neither g)

/-- Omitting the cause-to-dependence bridge, nonmutuality, or universal God
causality permits two Gods. In the second row both beings depend on each other. -/
def DependenceControls : Prop :=
  (GodCausesBeingOfAllOthers both reciprocal true ∧ DistinctBeingsNotMutuallyDependent independent ∧
    ¬ GodIsOne both) ∧
  (GodCausesBeingOfAllOthers both reciprocal true ∧ EsseEffectDependsOnItsCause reciprocal true opposite ∧
    opposite false true ∧ opposite true false ∧ ¬ GodIsOne both) ∧
  (EsseEffectDependsOnItsCause flat true independent ∧ DistinctBeingsNotMutuallyDependent independent ∧
    ¬ GodIsOne both)

/-- Two distinct candidate sources each give esse to an actual recipient.
Neither gives the other's esse. The maxima, exclusion and dependence premises
all hold. The universal naming converse is the assumption this partition loses. -/
def source (x : Bool × Bool) : Prop := x.2 = true
def domainGift (c x : Bool × Bool) (_ : Bool) : Prop :=
  source c ∧ x.2 = false ∧ c.1 = x.1
def sourceAbove (_ : Bool) (c x : Bool × Bool) : Prop := domainGift c x true
def domainReceives (x c : Bool × Bool) : Prop := domainGift c x true

def Partition : Prop :=
  let act := fun (_ : Bool × Bool) (_ : Bool) => True
  SomeBeingMaximalInBeing act sourceAbove true ∧ GodIsMaximalInBeing source act sourceAbove true ∧
  MaximumHasNoDistinctEsseCause act sourceAbove domainGift true ∧
  EsseEffectDependsOnItsCause domainGift true domainReceives ∧
  DistinctBeingsNotMutuallyDependent domainReceives ∧
  domainGift (false, true) (false, false) true ∧ domainGift (true, true) (true, false) true ∧
  ¬ GodCausesBeingOfAllOthers source domainGift true ∧ ¬ GodIsOne source

/-- Actual-recipient scope on four carriers. In the first row both candidates
are outside InAct at esse, although they each give esse to actual recipients.
In the second a unique actual candidate causes a distinct actual recipient
while a third, inactive carrier witnesses the failure of the strong converse. -/
def RecipientBoundary : Prop :=
  let recipients := fun (x : Bool × Bool) (_ : Bool) => x.2 = false
  let sharedGift := fun (c x : Bool × Bool) (_ : Bool) => source c ∧ x.2 = false
  let dep := fun (x c : Bool × Bool) => sharedGift c x true
  let g : Bool × Bool := (true, true)
  let active := fun (x : Bool × Bool) (_ : Bool) => x.2 = true
  let sole := fun x => x = g
  let gift := fun c (x : Bool × Bool) (_ : Bool) => sole c ∧ x.2 = true ∧ x ≠ c
  let higher := fun (_ : Bool) c x => gift c x true
  ((∀ c, source c → CausesAllInGenus recipients sharedGift true c) ∧
    EsseEffectDependsOnItsCause sharedGift true dep ∧ DistinctBeingsNotMutuallyDependent dep ∧
    sharedGift (false, true) (true, false) true ∧ sharedGift (true, true) (true, false) true ∧
    ¬ GodIsOne source) ∧
  ((∀ c, sole c → CausesAllInGenus active gift true c) ∧
    IsMaximumIn active higher true g ∧ MaximumHasNoDistinctEsseCause active higher gift true ∧
    sole g ∧ gift g (false, true) true ∧ ¬ active (false, false) true ∧
    ¬ GodCausesBeingOfAllOthers sole gift true ∧ GodIsOne sole)

def Controls : Prop := Joint ∧ MaximalControls ∧ DependenceControls ∧ Partition ∧ RecipientBoundary

end TruthCore.Case.Catholicism.GodIsOneFromEsse
