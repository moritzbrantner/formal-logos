module

public import TruthCore.Causality.ParticipatedEsseScale
public import TruthCore.Causality.SourceScopedAscent

@[expose] public section
namespace TruthCore.Causality.StrictEsseScale

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.ParticipatedEsseScale (realizedLevels)

variable {B P R A D : Type} [Preorder D]

/-- For each actual recipient of a distinct actual identity giver, a bound
assigned to its nature bounds every admitted level it actually realizes. -/
def RecipientLevelsWithinCapacity (f : Profile B P R) (Pure : A → Prop) (Has : B → A → Prop)
    (level : A → D) (capacity : P → D) : Prop :=
  ∀ c x, f.InAct c f.esse → f.InAct x f.esse → f.esseOf c = f.essenceOf c →
    c ≠ x → f.CausesIn c x f.esse →
    capacity (f.essenceOf x) ∈ upperBounds (realizedLevels Pure Has level x)

/-- The same actual giver realizes a selected determination whose level
strictly exceeds the capacity assigned to this recipient's nature. -/
def GiverRealizesBeyondCapacity (f : Profile B P R) (Pure : A → Prop) (Has : B → A → Prop)
    (level : A → D) (capacity : P → D) : Prop :=
  ∀ c x, f.InAct c f.esse → f.InAct x f.esse → f.esseOf c = f.essenceOf c →
    c ≠ x → f.CausesIn c x f.esse →
    ∃ a, Pure a ∧ Has c a ∧ capacity (f.essenceOf x) < level a

end TruthCore.Causality.StrictEsseScale
