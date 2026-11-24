module

public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Case.Catholicism.DivineLoveBridge

/-! Analyst profile for the personal interpretation of two immanent processions.
The role of source, expression or inclination need not have a personal realizer,
and two roles can be realized by one person. All metaphysical readings of the
primitive relations are open. See docs/notes/immanent-origins.md. -/

@[expose] public section

namespace TruthCore.Case.Catholicism.ImmanentOrigins

structure Profile where
  Role : Type
  Person : Type
  Esse : Type
  Mode : Type
  source : Role
  word : Role
  love : Role
  generation : Mode
  spiration : Mode
  divineEsse : Esse
  esseOf : Person → Esse
  expresses : Role → Role → Prop
  inclines : Role → Role → Prop
  subsistsAs : Role → Person → Prop
  origin : Mode → Person → Person → Prop

def Divine (d : Profile) (p : d.Person) : Prop := d.esseOf p = d.divineEsse

def Realizer (d : Profile) (r : d.Role) (p : d.Person) : Prop :=
  d.subsistsAs r p ∧ Divine d p

def Receives (d : Profile) (k : d.Mode) (p : d.Person) : Prop :=
  ∃ a, Divine d a ∧ d.origin k a p

def Underived (d : Profile) (p : d.Person) : Prop :=
  ∀ k, ¬ Receives d k p

/-- The two operations have specified internal directions and distinct kinds of
origin. Distinct kinds can still have the same personal terminus. -/
def TwoModes (d : Profile) : Prop :=
  d.expresses d.source d.word ∧ d.inclines d.source d.love ∧ d.generation ≠ d.spiration

/-- Personal subsistence in the same numerical esse is an assumption for each
role. OPEN: 'subsistsAs' means constituted as this personal supposit, a stronger
claim than being entertained or performed by a subject. -/
def Subsistence (d : Profile) : Prop :=
  (∃ f, Realizer d d.source f) ∧ (∃ w, Realizer d d.word w) ∧ (∃ l, Realizer d d.love l)

/-- OPEN: transporting the intentional order to these personal realizers gives
a real origin at the indicated mode. The personal opposition premise applies to
real origins, not to self-directed knowing and loving. -/
def PersonalOrder (d : Profile) : Prop :=
  (∀ a b p q, d.expresses a b → Realizer d a p → Realizer d b q → d.origin d.generation p q) ∧
  (∀ a b p q, d.inclines a b → Realizer d a p → Realizer d b q → d.origin d.spiration p q) ∧
  (∀ k p, Divine d p → ¬ d.origin k p p)

/-- Either the Word has an active role in the selected Love-origin, or the two modes
of reception have incompatible personal termini. The second disjunct is an open
criterion of personal constitution, not a rule about different relation names. -/
def Separation (d : Profile) : Prop :=
  d.inclines d.word d.love ∨
    (∀ p, Divine d p → Receives d d.generation p → ¬ Receives d d.spiration p)

structure Triple (d : Profile) (f w l : d.Person) : Prop where
  father : Realizer d d.source f
  word : Realizer d d.word w
  love : Realizer d d.love l
  generates : d.origin d.generation f w
  spirates : d.origin d.spiration f l
  modesDiffer : d.generation ≠ d.spiration
  fw : f ≠ w
  fl : f ≠ l
  wl : w ≠ l

/-- Separate lower and upper bounds. All other persons in the same esse must
be considered, including additional unoriginated or same-mode termini. -/
def AtLeast (d : Profile) : Prop := ∃ f w l, Triple d f w l

def Exactly (d : Profile) : Prop :=
  ∃ f w l, Triple d f w l ∧ ∀ p, Divine d p → p = f ∨ p = w ∨ p = l

/-- Inventory of the personal bearers, classified by their incoming origins.
Additional origin edges or modes can coexist with this inventory. -/
def SourceUnderived (d : Profile) : Prop :=
  ∀ f, Realizer d d.source f → Underived d f

def Classifies (d : Profile) : Prop :=
  ∀ p, Divine d p → Underived d p ∨ Receives d d.generation p ∨ Receives d d.spiration p

def UniqueUnderived (d : Profile) : Prop :=
  ∀ p q, Divine d p → Divine d q → Underived d p → Underived d q → p = q

def UniqueTerm (d : Profile) (k : d.Mode) : Prop :=
  ∀ p q, Divine d p → Divine d q → Receives d k p → Receives d k q → p = q

def Inventory (d : Profile) : Prop :=
  SourceUnderived d ∧ Classifies d ∧ UniqueUnderived d ∧
    UniqueTerm d d.generation ∧ UniqueTerm d d.spiration

/-- Finite interpretations for the cardinality and subsistence tests. The three
positions are roles only. 'P' has different cardinalities in different tests.
The 'Esse' field takes a token, rather than a kind shared by similar tokens. -/
def fixture (P : Type) (realizes : Fin 3 → P → Prop) (active : Bool)
    (origins : Bool → P → P → Prop) : Profile where
  Role := Fin 3
  Person := P
  Esse := Unit
  Mode := Bool
  source := 0
  word := 1
  love := 2
  generation := false
  spiration := true
  divineEsse := ()
  esseOf := fun _ => ()
  expresses a b := a = 0 ∧ b = 1
  inclines a b := (a = 0 ∨ (active = true ∧ a = 1)) ∧ b = 2
  subsistsAs := realizes
  origin := origins

def single : Profile := fixture (Fin 1) (fun r _ => r = 0) true (fun _ _ _ => False)

/-- On the same selected esse, the Word-role is actual correct, grounded
self-content. Both possession of the own good and actual willing of it are
populated, and the existing recipient-good specification gives thin self-love.
These are interpretations of the upstream primitives, not an exhaustive
account of perfect divine knowledge or a psychological explanation. -/
def SingleSelfActs : Prop :=
  let g := single.divineEsse
  let good := fun (_ : single.Esse) (r : single.Role) => r = single.love
  let wills := fun (a b : single.Esse) (r : single.Role) => a = b ∧ r = single.love
  let loves := fun (a b : single.Esse) => ∃ r, good b r ∧ wills a b r
  TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.IntrinsicSelfKnowledge
    (fun c _ => c = single.word) (fun c _ => c = single.word)
    (fun _ c => c = single.word) (fun _ c => c = single.word) g ∧
  good g single.love ∧ wills g g single.love ∧
  TruthCore.Case.Catholicism.DivineLoveBridge.WillingGoodEntailsLove good wills loves ∧ loves g g

def coincident : Profile := fixture Bool (fun r p => (p = false ↔ r = 0))
  false (fun _ p q => p = false ∧ q = true)

def complete : Profile := fixture (Fin 3) (fun r p => r = p) true
  (fun k p q => (k = false ∧ p = 0 ∧ q = 1) ∨ (k = true ∧ (p = 0 ∨ p = 1) ∧ q = 2))

def separateReceptions : Profile := fixture (Fin 3) (fun r p => r = p) false
  (fun k p q => p = 0 ∧ ((k = false ∧ q = 1) ∨ (k = true ∧ q = 2)))

def iterated : Profile := fixture (Fin 4) (fun r p => r.val = p.val) true
  (fun k p q =>
    (k = false ∧ ((p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 3))) ∨
    (k = true ∧ (p = 0 ∨ p = 1) ∧ q = 2))

def Controls : Prop :=
  (SingleSelfActs ∧ TwoModes single ∧ Separation single ∧ PersonalOrder single ∧
    (∃ f, Realizer single single.source f) ∧ ¬ Subsistence single ∧ ¬ AtLeast single) ∧
  (TwoModes coincident ∧ Subsistence coincident ∧ PersonalOrder coincident ∧
    ¬ Separation coincident ∧ ¬ AtLeast coincident) ∧
  (TwoModes complete ∧ Subsistence complete ∧ PersonalOrder complete ∧ Separation complete ∧
    Inventory complete ∧ Exactly complete) ∧
  (TwoModes separateReceptions ∧ Subsistence separateReceptions ∧ PersonalOrder separateReceptions ∧
    ¬ separateReceptions.inclines separateReceptions.word separateReceptions.love ∧
    Separation separateReceptions ∧ Inventory separateReceptions ∧ Exactly separateReceptions) ∧
  (TwoModes iterated ∧ Subsistence iterated ∧ PersonalOrder iterated ∧ Separation iterated ∧
    SourceUnderived iterated ∧ Classifies iterated ∧ UniqueUnderived iterated ∧
    UniqueTerm iterated iterated.spiration ∧ ¬ UniqueTerm iterated iterated.generation ∧
    AtLeast iterated ∧ ¬ Exactly iterated)

/-- If identity of the divine act entails identity of any personal bearers of it,
the three-candidate conclusion is impossible even without any inventory laws. -/
def TokenCollapse : Prop := ∀ d : Profile,
  (∀ p q, d.esseOf p = d.esseOf q → p = q) → ¬ AtLeast d

end TruthCore.Case.Catholicism.ImmanentOrigins
