module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question103.DirectorInheritance
public import TruthCore.Case.Catholicism.StageOneQuintaVia
public import TruthCore.Logic.ExcludedMiddle

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.DirectorInheritance
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.DirectorInheritance
open TruthCore.Case.Catholicism (NaturalDirectionReducedToIntelligentImmobileDirector)

theorem weaken {Being Respect End : Type} (NaturalBody : Being → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (Directs : Being → Being → End → Prop)
    (hThrough : DirectionPassesToMoversOfDirectors MovesIn Directs) :
    SameEndMoverSelection NaturalBody MovesIn Directs := by
  intro f x e _ hf hMovers
  obtain ⟨g, r, hg, hNe⟩ := hMovers
  exact ⟨g, r, hg, hNe, hThrough g f x e r hf hg hNe⟩

theorem fromSelection {Being Respect End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop)
    (hOther : MovedByAnotherReading MovedIn MovesIn)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved)
    (hEM : ExcludedMiddle)
    (hSelect : SameEndMoverSelection NaturalBody MovesIn Directs)
    (hDesign : UnmovedDirectorKnowsAndUnderstands MovedIn HasCognition Intelligent Directs) :
    NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody HasCognition
      Intelligent Directs := by
  intro d x e hx hd
  have hTop : ∀ f, Directs f x e → ∃ h, Directs h x e ∧ ∀ r, ¬ MovedIn h r := by
    intro f
    induction hRegress f with
    | intro f _ ih =>
      intro hf
      cases hEM (∃ r, MovedIn f r) with
      | inr hUnmoved => exact ⟨f, hf, fun r hr => hUnmoved ⟨r, hr⟩⟩
      | inl hMoved =>
        obtain ⟨r, hr⟩ := hMoved
        obtain ⟨g, hNe, hg⟩ := hOther f r hr
        -- Selection need not retain the arbitrary mover supplied above.
        obtain ⟨g', r', hg', hNe', hDir⟩ := hSelect f x e hx hf ⟨g, r, hg, hNe⟩
        cases hEM (∃ r'', MovedIn g' r'') with
        | inr hUnmoved => exact ⟨g', hDir, fun r'' hr'' => hUnmoved ⟨r'', hr''⟩⟩
        | inl hgMoved => exact ih g' (hPerSe g' f r' hNe' hg' hgMoved) hDir
  obtain ⟨h, hh, hUnmoved⟩ := hTop d hd
  obtain ⟨hCog, hIntel⟩ := hDesign h x e hh hUnmoved
  exact ⟨h, hCog, hIntel, hUnmoved, hh⟩

end TruthCore.Results.Aquinas.SummaTheologiae.DirectorInheritance
