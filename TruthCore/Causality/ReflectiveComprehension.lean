module

public import TruthCore.Causality.ComprehensionByMeasure
public import TruthCore.Causality.IntentionalExemplarExtension
public import TruthCore.Causality.SoleEsseGiver

/-! A cognitive comparison on the selected actual roster. The identification of
measured whole act with represented esse is a premise about this state. -/

@[expose] public section
namespace TruthCore.Causality.ReflectiveComprehension

open TruthCore.Causality.ComprehensionByMeasure
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

variable {B P R D : Type} [Preorder D]

/-- Open calibration up to equivalence in the preorder, at actual bearers only. -/
def MeasuredActAgreesWithEsse (f : Profile B P R) (degree : R → B → D)
    (M : Measures B D) : Prop :=
  ∀ x, f.InAct x f.esse →
    degree f.esse x ≤ M.actDegree x ∧ M.actDegree x ≤ degree f.esse x

/-- Open applicability premise. Each recipient is an object of the selected
source's measured comprehension. The recipient need not itself know anything. -/
def ComprehendsParticipants (f : Profile B P R) (Participated : B → Prop)
    (M : Measures B D) (s : B) : Prop :=
  ∀ x, f.InAct x f.esse → Participated x → ComprehendsByMeasure M s x

/-- A witnessed act of self-comprehension fixes a recipient's own grade up to
preorder equivalence. Any higher knowing by another actual bearer then gives a
strict comparison at esse. The two knowings may have different objects. -/
def ReflectiveComparison (f : Profile B P R) (degree : R → B → D)
    (M : Measures B D) : Prop :=
  ∀ x a, f.InAct x f.esse → M.KnowsAt x x a → M.knowability x ≤ a →
    (M.actDegree x ≤ a ∧ a ≤ M.actDegree x) ∧
    (M.knowability x ≤ a ∧ a ≤ M.knowability x) ∧
    ∀ s y b, f.InAct s f.esse → M.KnowsAt s y b → a < b → degree f.esse x < degree f.esse s

/-- Comprehension orders whole acts. Two beings comprehending each other
therefore agree in both order directions, even on a non-antisymmetric scale. -/
def ComprehensionOrdersAct (M : Measures B D) : Prop :=
  ∀ s x, ComprehendsByMeasure M s x → M.actDegree x ≤ M.actDegree s

namespace Control
open TruthCore.Causality.IntentionalExemplarExtension (UnderstandsActualEffects)
open TruthCore.Causality.IntentionalExemplarExtension.Control
  (frame about correct sourceTakesUp)

/-- The ordinary Boolean order with its three laws checked by enumeration. -/
local instance twoDegreeOrder : Preorder Bool where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by decide
  le_trans := by decide
  lt_iff_le_not_ge := by decide

/-- For these controls, genuinely apprehended true contents are the objects of
actual measured knowings. The higher self-knowing belongs to the source. -/
def tied : Measures Bool Bool where
  actDegree := fun _ => true
  knowability := fun _ => true
  KnowsAt := fun g x d => sourceTakesUp g x ∧ d = (g && x)

/-- On the same content and uptake dictionary, no actual knowing is above the
low degree. The source is at the low degree and the recipient at the high. -/
def lowerSource : Measures Bool Bool where
  actDegree := Bool.not
  knowability := Bool.not
  KnowsAt := fun g x d => sourceTakesUp g x ∧ d = false

/-- The actual q.44 roster uses the same two beings and causal edge as the
exemplar control at world true. -/
def profile : Profile Bool Bool Unit where
  InAct := fun x _ => frame.history.ontic.ExistsAt true x
  CausesIn := frame.CausesIn
  essenceOf := fun _ => false
  esseOf := Bool.not
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- Each knowing reaches just its object's grade and only a knower at least
that high can perform it. -/
def full : Measures Bool Bool :=
  ⟨id, id, fun g x d => x ≤ g ∧ d = x⟩

/-- The source apprehends the recipient to its full grade while the recipient
never knows the source. Their degrees of whole act still coincide. -/
def asymmetric : Measures Bool Bool :=
  ⟨fun _ => true, fun _ => true, fun g x d => sourceTakesUp g x ∧ d = true⟩

def Controls : Prop :=
  frame.history.ontic.ExistsAt true false ∧ frame.CausesIn true false frame.esse ∧
  UnderstandsActualEffects frame true about correct sourceTakesUp sourceTakesUp true ∧
  KnowableInsofarAsInAct tied ∧ KnowingWithinKnowersAct tied ∧
  tied.KnowsAt true true true ∧ tied.KnowsAt false false false ∧
  tied.KnowsAt true false false ∧
  ¬ ComprehendsByMeasure tied true false ∧ ¬ ComprehendsByMeasure tied false false ∧
  tied.actDegree true = tied.actDegree false ∧
  KnowableInsofarAsInAct lowerSource ∧ KnowingWithinKnowersAct lowerSource ∧
  lowerSource.KnowsAt true false false ∧ ¬ ComprehendsByMeasure lowerSource true false ∧
  lowerSource.actDegree true < lowerSource.actDegree false ∧
  (∀ g x, sourceTakesUp g x ↔ ∃ d, tied.KnowsAt g x d) ∧
  (∀ g x, sourceTakesUp g x ↔ ∃ d, lowerSource.KnowsAt g x d) ∧
  KnowableInsofarAsInAct asymmetric ∧ KnowingWithinKnowersAct asymmetric ∧
  ComprehendsByMeasure asymmetric true false ∧ ¬ ComprehendsByMeasure asymmetric false true ∧
  ComprehendsByMeasure asymmetric false false ∧ asymmetric.actDegree false = asymmetric.actDegree true ∧
  SoleEsseGiver.SoleEssentialGiver profile (· = false) (· = true) true ∧
  ComprehendsParticipants profile (· = false) full true ∧
  MeasuredActAgreesWithEsse profile (fun _ => id) full ∧
  KnowableInsofarAsInAct full ∧ KnowingWithinKnowersAct full ∧
  ComprehendsByMeasure full false false ∧ full.KnowsAt false false false ∧
  full.KnowsAt true true true ∧ full.knowability false ≤ false ∧
  full.actDegree false < full.actDegree true


end Control
end TruthCore.Causality.ReflectiveComprehension
