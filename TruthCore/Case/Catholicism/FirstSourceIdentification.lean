module

public import TruthCore.Causality.TermSenseForks4
public import TruthCore.Case.Catholicism.StageTwo

/-! Restrictions on the extension of the stage-one names. These are analyst
premises about an already fixed interpretation of each name. -/

@[expose] public section

namespace TruthCore.Case.Catholicism.FirstSourceIdentification

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.TermSenseForks

/-- Reverse restriction on GOD_2 in the fixed Fourth Way vocabulary. -/
def SummaGodIsMaximum {B R : Type} (God : B → Prop)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∀ x, God x → IsMaximumIn InAct MoreIn esse x

/-- The community's use of the name is restricted to maxima in the fixed
Fourth Way vocabulary. This is substantive even for a community that applies
the name correctly to a fully described maximum. -/
def CalledGodIsMaximum {B R Name : Type} (Calls : Name → B → Prop) (godName : Name)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∀ x, CalledGod Calls godName x → IsMaximumIn InAct MoreIn esse x

end TruthCore.Case.Catholicism.FirstSourceIdentification
