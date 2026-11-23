module

public import TruthCore.German.Kant.CosmologicalInference
public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Modal.NecessaryIfExistent
public import TruthCore.Modal.PossibilityTransfer

/-! Guarded quantification over existing Ontic presence extensions. Predicate P
is arbitrary and TOTAL on the fixed candidate roster: absence does not make
P undefined or force it false. Only the quantifier is existence-guarded.
Domains vary as ExistsAt extensions, never as Lean identity or counterpart
rosters. No causal, temporal or nonempty-domain hypothesis is built in.
The two transfers concern this explicit profile, not every quantified logic. -/

@[expose] public section

namespace TruthCore.Modal.ActualistDomains
open TruthCore.German.Kant.CosmologicalInference
variable {W B : Type}

/-- All currently existing candidates satisfy the total supplied predicate. -/
def ActualistAll (m : Ontic W B) (P : W → B → Prop) (w : W) : Prop :=
  ∀ x, m.ExistsAt w x → P w x
/-- Existing membership persists along each accessibility edge. -/
def IncreasingDomains (m : Ontic W B) : Prop :=
  ∀ w v, m.frame.access w v → ∀ x, m.ExistsAt w x → m.ExistsAt v x
/-- Every successor member already belongs to the current domain. -/
def DecreasingDomains (m : Ontic W B) : Prop :=
  ∀ w v, m.frame.access w v → ∀ x, m.ExistsAt v x → m.ExistsAt w x
/-- Box of guarded forall entails guarded forall of box, for every total P. -/
def BoxAllToAllBox (m : Ontic W B) : Prop :=
  ∀ (P : W → B → Prop) w,
    (∀ v, m.frame.access w v → ActualistAll m P v) →
    ∀ x, m.ExistsAt w x → ∀ v, m.frame.access w v → P v x
/-- Guarded forall of box entails box of guarded forall, for every total P. -/
def AllBoxToBoxAll (m : Ontic W B) : Prop :=
  ∀ (P : W → B → Prop) w,
    (∀ x, m.ExistsAt w x → ∀ v, m.frame.access w v → P v x) →
    ∀ v, m.frame.access w v → ActualistAll m P v


/-! ## A fixed divine-attribute bundle, independent of the naming predicate

#1864, complementary to #1865's generic MaximalProfile. The nine classical
predicates are fed into the existing NineClassicalAttributes definition. The
additional omnipotence, omniscience, moral impeccability, and freedom fields are explicit selected
senses, NOT consequences of the nine and not world-invariant by stipulation.
Simplicity, metaphysical goodness, moral goodness, freedom and intellect here name chosen *extensions*;
interpreting them by the relevant real essences, powers and acts is OPEN.

In particular this bundle excludes IsGod: importing the world-invariant root
predicate into a possible-world witness would trivialize a GodExists projection.
-/

/-- One fixed interpretation of each candidate essential perfection at each
world and bearer. These fields are not independently satisfiable axioms. -/
structure DivinePredicates (World Entity : Type) where
  simple : World → Entity → Prop
  perfect : World → Entity → Prop
  good : World → Entity → Prop
  one : World → Entity → Prop
  infinite : World → Entity → Prop
  immutable : World → Entity → Prop
  eternal : World → Entity → Prop
  intellect : World → Entity → Prop
  will : World → Entity → Prop
  omnipotent : World → Entity → Prop
  omniscient : World → Entity → Prop
  morallyPerfect : World → Entity → Prop
  free : World → Entity → Prop

/-- StageTwo's SAME nine attributes instantiated at one world and one bearer;
this does not change its curried sufficiency bridge. -/
def NineAt (p : DivinePredicates W B) (w : W) (x : B) : Prop :=
  TruthCore.Case.Catholicism.NineClassicalAttributes
    (p.simple w) (p.perfect w) (p.good w) (p.one w)
    (p.infinite w) (p.immutable w) (p.eternal w)
    (p.intellect w) (p.will w) x

/-- A joint thirteen-predicate candidate: all conjuncts concern THE SAME x
at THE SAME world. Not a claim that these extensions describe possible essences. -/
def ExcellenceAt (p : DivinePredicates W B) (w : W) (x : B) : Prop :=
  NineAt p w x ∧ p.omnipotent w x ∧ p.omniscient w x ∧
    p.morallyPerfect w x ∧ p.free w x

/-- Maximal greatness additionally requires existence and the COMPLETE bundle
for the same bearer at every successor of the candidate world. Reuses #1865. -/
def GreatnessAt (m : Ontic W B) (p : DivinePredicates W B) (x : B) (w : W) : Prop :=
  TruthCore.Modal.NecessaryIfExistent.MaximalProfile
    m.frame m.ExistsAt (ExcellenceAt p) x w

/-- Metaphysically accessible joint greatness, relative to m.frame.
Reading that frame as genuine metaphysical accessibility remains OPEN. -/
def PossibleGreatness (m : Ontic W B) (p : DivinePredicates W B) (w : W) : Prop :=
  ∃ v, m.frame.access w v ∧ ∃ x, GreatnessAt m p x v

/-- Candidate-description possibility, with a potentially broader relation E.
Unlike M-possibility this alone does not establish an actual modal witness. -/
def DescribedPossibleGreatness (E : TruthCore.Modal.Frame W)
    (m : Ontic W B) (p : DivinePredicates W B) (w : W) : Prop :=
  ∃ v, E.access w v ∧ ∃ x, GreatnessAt m p x v

/-- A *profile-specific*, witness-preserving admissibility condition. E-successors
bearing this complete profile must be M-admissible at w. We do NOT require the
much stronger universal IncludedAt E M w for arbitrary descriptions.
The condition is still a substantive OPEN metaphysical premise. -/
def AdmitGreatnessWorlds (E : TruthCore.Modal.Frame W)
    (m : Ontic W B) (p : DivinePredicates W B) (w : W) : Prop :=
  ∀ v, E.access w v → (∃ x, GreatnessAt m p x v) → m.frame.access w v

/-- A source/causal/naming judgment applied ONLY after the full bundle has
been instantiated by an actual existing bearer. Neither the bundle nor the
modal inference defines the root predicate IsGod. This bridge is OPEN. -/
def ActualDivineNaming (σ : TruthCore.Case.Catholicism.Signature)
    (m : Ontic W σ.Being) (p : DivinePredicates W σ.Being) (w : W) : Prop :=
  ∀ x, m.ExistsAt w x → ExcellenceAt p w x → σ.IsGod x

/-- The bundle is essential to this ACTUAL bearer in the selected component.
Freedom here must be construed as an essential capacity, not as a necessarily
fixed contingent choice. This substantive principle is NOT derived. -/
def EssentialExcellenceAt (m : Ontic W B)
    (p : DivinePredicates W B) (w : W) : Prop :=
  ∀ x, m.ExistsAt w x → ExcellenceAt p w x →
    ∀ v, m.frame.access w v → m.ExistsAt v x ∧ ExcellenceAt p v x

/-! Explicit finite structural controls. They do not establish that a real
divine essence is metaphysically possible. Both frames of #438 satisfy S5. -/
namespace DivineControl

/-- Under M = identity, only the selected world's one bearer exists, and all
thirteen predicates hold together exactly where that bearer exists. -/
def holdsAt (selected : Bool) (v x : Bool) : Prop :=
  v = selected ∧ x = true

def ontic (selected : Bool) : Ontic Bool Bool where
  frame := TruthCore.Modal.PossibilityTransfer.metaphysical
  ExistsAt := holdsAt selected
  Causes := fun _ _ _ => False

def attributes (selected : Bool) : DivinePredicates Bool Bool where
  simple := holdsAt selected
  perfect := holdsAt selected
  good := holdsAt selected
  one := holdsAt selected
  infinite := holdsAt selected
  immutable := holdsAt selected
  eternal := holdsAt selected
  intellect := holdsAt selected
  will := holdsAt selected
  omnipotent := holdsAt selected
  omniscient := holdsAt selected
  morallyPerfect := holdsAt selected
  free := holdsAt selected

/-- K5/EUCLIDEAN without actual reflexivity: every world sees true, but
false does NOT see itself. The full profile can exist at true without any
actually existing bearer at false. This fixes the difference between K5
necessity over successors and an actual-world inference. -/
def k5Frame : TruthCore.Modal.Frame Bool := ⟨fun _ v => v = true⟩

def k5Ontic : Ontic Bool Bool where
  frame := k5Frame
  ExistsAt := at true
  Causes := fun _ _ _ => False

/-- Individually satisfiable power and knowledge attributed to DIFFERENT
bearers; the remaining eleven predicates are unproblematic in this control. -/
def split : DivinePredicates Bool Bool where
  simple := fun _ _ => True
  perfect := fun _ _ => True
  good := fun _ _ => True
  one := fun _ _ => True
  infinite := fun _ _ => True
  immutable := fun _ _ => True
  eternal := fun _ _ => True
  intellect := fun _ _ => True
  will := fun _ _ => True
  omnipotent := fun _ x => x = true
  omniscient := fun _ x => x = false
  morallyPerfect := fun _ _ => True
  free := fun _ _ => True

/-- The E witness is jointly realized (by an existing bearer at true) but is
not admitted by M at false. Conversely, at false a complete E-witness is
admitted by M without including EVERY E-successor in M. Distinct individual
attribute witnesses still do not establish a joint bearer. -/
def Checks : Prop :=
  (DescribedPossibleGreatness TruthCore.Modal.PossibilityTransfer.epistemic
      (ontic true) (attributes true) false ∧
   ¬ PossibleGreatness (ontic true) (attributes true) false) ∧
  (DescribedPossibleGreatness TruthCore.Modal.PossibilityTransfer.epistemic
      (ontic false) (attributes false) false ∧
   AdmitGreatnessWorlds TruthCore.Modal.PossibilityTransfer.epistemic
      (ontic false) (attributes false) false ∧
   ¬ TruthCore.Modal.PossibilityTransfer.IncludedAt
       TruthCore.Modal.PossibilityTransfer.epistemic
       (ontic false).frame false ∧
   PossibleGreatness (ontic false) (attributes false) false) ∧
  (∃ x, split.omnipotent false x) ∧
  (∃ x, split.omniscient false x) ∧
  (¬ ∃ x, ExcellenceAt split false x) ∧
  (TruthCore.Modal.Euclidean k5Frame ∧
   PossibleGreatness k5Ontic (attributes true) false ∧
   ¬ ∃ x, k5Ontic.ExistsAt false x)

end DivineControl

end TruthCore.Modal.ActualistDomains
