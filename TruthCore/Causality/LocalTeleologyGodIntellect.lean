module

public import TruthCore.Causality.WitnessLocalTeleology
public import TruthCore.Case.Catholicism.StageTwo

/-! Fixed two-being controls for local teleology's attachment to GOD_4.
False is a noncognitive natural body; true alone directs and moves it, and is
unmoved. All tests use this SAME motion/director dictionary. These are formal
interpretations, not evidence for actual teleological or identity premises. -/

@[expose] public section
namespace TruthCore.Causality.LocalTeleologyGodIntellect
open TruthCore.Causality.WitnessLocalTeleology
open TruthCore.Case.Catholicism

namespace Control

def yes (_ : Bool) : Prop := True
def no (_ : Bool) : Prop := False
def intellect (x : Bool) : Prop := x = true
def body (x : Bool) : Prop := x = false
def moved (_ : Bool) (_ : Unit) : Prop := False
def moves (d x : Bool) (_ : Unit) : Prop := d = true ∧ x = false
def regular (x : Bool) (_ : Unit) : Prop := x = false
def best (_ : Bool) (_ : Unit) : Prop := True
def chance (_ : Bool) (_ : Unit) : Prop := False
def act (_ : Bool) (_ : Unit) : Prop := True
/-- true strictly exceeds false; hence only true is maximal. -/
def more (_ : Unit) (y x : Bool) : Prop := y = true ∧ x = false
/-- Flat degrees make both beings maximal; direction remains non-flat. -/
def flat (_ : Unit) (_ _ : Bool) : Prop := False

def Local (Intel : Bool → Prop) : Prop :=
  Bundle moved moves body intellect Intel regular best chance regular moves

def Identity (More : Unit → Bool → Bool → Prop) : Prop :=
  FirstUnmovedMoverIsMaximeEns moved moves act More ()

def Maximal (God : Bool → Prop) (More : Unit → Bool → Bool → Prop) : Prop :=
  GodIsMaximalInBeing God act More ()

/-- Populated joint interpretation, then three distinct omission tests:
identity, God-to-maximum, and local intellectual direction. None refutes a
metaphysical premise. The first preserves an intellectual first mover and a
nonintellectual GOD_4 maximum at distinct beings, exposing the identity gap. -/
def Controls : Prop :=
  (Local intellect ∧ Identity more ∧ Maximal intellect more ∧
    intellect true ∧ GodHasIntellect intellect intellect) ∧
  (Local intellect ∧ Maximal body flat ∧ ¬ Identity flat ∧
    ¬ GodHasIntellect body intellect) ∧
  (Local intellect ∧ Identity more ∧ ¬ Maximal body more ∧
    ¬ GodHasIntellect body intellect) ∧
  (Identity more ∧ Maximal intellect more ∧ ¬ Local no ∧
    ¬ GodHasIntellect intellect no)

end Control
end TruthCore.Causality.LocalTeleologyGodIntellect
