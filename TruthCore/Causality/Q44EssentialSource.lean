module

public import TruthCore.Latin.Aquinas.DeEnte.EsseSource
public import TruthCore.Causality.CreatureSenses

/-! Analyst q44 application, attribution deferred. `OwnBeing` reuses the
interpreted primitive of WholePowerPerfection (one's own subsistent esse), not
modal necessity or represented identity by definition. `Participated` retains
the existing q44 predicate. The identity dictionary below is an explicit
premise restricted to relevant actual sources; no definition proves it. -/

@[expose] public section
namespace TruthCore.Causality.Q44EssentialSource

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Latin.Aquinas.DeEnte (AtMostOneEsseIsEssence)

/-- Each participant has a distinct actual cause of its esse that is its own
subsistent being. Stronger than q3's some external cause: the own-being clause
and direct causal edge are substantive assumptions, not consequences of q3. -/
def ParticipatedHasEssentialSource {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) : Prop :=
  ∀ x, Participated x → ∃ c, c ≠ x ∧ f.InAct c f.esse ∧ OwnBeing c ∧
    f.CausesIn c x f.esse

/-- At relevant distinct actual own-being sources only, the represented act of being
and essence denote the same principle. No converse, nonreception or causal
independence is encoded. This dictionary is OPEN even though the intended
own-being meaning motivates it; arbitrary profile maps need not respect it. -/
def RelevantEssentialSourceHasIdentity {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) : Prop :=
  ∀ c x, Participated x → c ≠ x → f.InAct c f.esse → OwnBeing c → f.CausesIn c x f.esse →
    f.esseOf c = f.essenceOf c

/-- One selected, actual identity witness. No own-being, universal causation,
uniqueness, necessity or GOD_4 status is contained in this conjunction. -/
def SelectedActualIdentity {B P R : Type} (f : Profile B P R) (p : B) : Prop :=
  f.InAct p f.esse ∧ f.esseOf p = f.essenceOf p

/-- Every relevant distinct actual own-being cause is the selected p. Quantifies only
over own-being causes of participants; unrelated own-being bearers are not
classified. This is numerical source selection, not mere common description. -/
def RelevantEssentialSourcesSelected {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (p : B) : Prop :=
  ∀ c x, Participated x → c ≠ x → f.InAct c f.esse → OwnBeing c → f.CausesIn c x f.esse → c = p

namespace Control
inductive Three where
  | primary | source | effect
  deriving DecidableEq
open Three

def profile (identity : Three → Bool) (cause : Three → Three → Prop) :
    Profile Three Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => cause c x
  essenceOf := fun _ => false
  esseOf := identity
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

def participant (x : Three) : Prop := x = effect
def own (c : Three) : Prop := c = source
def localCause (c x : Three) : Prop := c = source ∧ x = effect

def primaryOnly := profile (fun c => if c = primary then false else true) localCause
def twoIdentities := profile (fun c => if c = effect then true else false) localCause
def sourceOnly := profile (fun c => if c = source then false else true) localCause

def positive := profile (fun c => if c = primary then false else true)
  (fun c x => c = primary ∧ x ≠ primary)
def other (x : Three) : Prop := x ≠ primary
def ownPrimary (c : Three) : Prop := c = primary

/-- Three source-selection omissions, all with an actual own-being source
causing a participant, and one nonvacuous positive full-route interpretation.
The first deliberately violates the own-being/profile dictionary: it tests
encoding applicability, not the metaphysical possibility of that violation. -/
def Certificate : Prop :=
  (SelectedActualIdentity primaryOnly primary ∧ AtMostOneEsseIsEssence primaryOnly ∧
    ParticipatedHasEssentialSource primaryOnly participant own ∧
    ¬ RelevantEssentialSourceHasIdentity primaryOnly participant own ∧
    ¬ RelevantEssentialSourcesSelected primaryOnly participant own primary) ∧
  (SelectedActualIdentity twoIdentities primary ∧
    RelevantEssentialSourceHasIdentity twoIdentities participant own ∧
    ParticipatedHasEssentialSource twoIdentities participant own ∧
    ¬ AtMostOneEsseIsEssence twoIdentities ∧
    ¬ RelevantEssentialSourcesSelected twoIdentities participant own primary) ∧
  (AtMostOneEsseIsEssence sourceOnly ∧
    RelevantEssentialSourceHasIdentity sourceOnly participant own ∧
    ParticipatedHasEssentialSource sourceOnly participant own ∧
    ¬ SelectedActualIdentity sourceOnly primary ∧
    ¬ RelevantEssentialSourcesSelected sourceOnly participant own primary) ∧
  (SelectedActualIdentity positive primary ∧ AtMostOneEsseIsEssence positive ∧
    RelevantEssentialSourceHasIdentity positive other ownPrimary ∧
    ParticipatedHasEssentialSource positive other ownPrimary ∧
    RelevantEssentialSourcesSelected positive other ownPrimary primary ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
      (TruthCore.Causality.CreatureSenses.IsCreatureOfUniversalCause
        positive.InAct positive.CausesIn positive.esse) primary ∧
    positive.CausesIn primary effect ())
end Control
end TruthCore.Causality.Q44EssentialSource
