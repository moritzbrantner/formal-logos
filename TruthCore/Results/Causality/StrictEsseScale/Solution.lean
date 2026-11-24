module

public import TruthCore.Causality.StrictEsseScale

@[expose] public section
namespace TruthCore.Results.Causality.StrictEsseScale

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.ParticipatedEsseScale
open TruthCore.Causality.StrictEsseScale
open TruthCore.Causality.Round2PerfectionPrimacy (GreaterDegreeIsMore)
open TruthCore.Causality.SourceScopedAscent (IdentityCauseAscent)

theorem identityAscentFromCapacity {B P R A D : Type} [Preorder D] (f : Profile B P R)
    (Pure : A → Prop) (Has : B → A → Prop) (level : A → D) (capacity : P → D)
    (degree : R → B → D) (MoreIn : R → B → B → Prop)
    (hBound : RecipientLevelsWithinCapacity f Pure Has level capacity)
    (hExceeds : GiverRealizesBeyondCapacity f Pure Has level capacity)
    (hScale : OwnDegreeFromRealizedLevels f Pure Has level degree)
    (hMore : GreaterDegreeIsMore (fun (_ : Unit) => MoreIn f.esse)
      (fun x (_ : Unit) => degree f.esse x)) : IdentityCauseAscent f MoreIn := by
  intro c x hc hx hid hne hcauses
  obtain ⟨a, hpure, hhas, hlt⟩ := hExceeds c x hc hx hid hne hcauses
  have hxBound := (hScale x hx).2 (hBound c x hc hx hid hne hcauses)
  have hcLevel : level a ≤ degree f.esse c := (hScale c hc).1 ⟨a, hpure, hhas, rfl⟩
  exact hMore () c x (lt_of_le_of_lt hxBound (lt_of_lt_of_le hlt hcLevel))

end TruthCore.Results.Causality.StrictEsseScale
