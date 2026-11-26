import TruthCore.Case.Catholicism.NoSelfCauseScope
import TruthCore.Alternatives.ActPotencyRegress
import TruthCore.Logic.RootDescent

namespace TruthCore.Results.Case.Catholicism.NoSelfCauseScope

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Case.Catholicism.NoSelfCauseScope
open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.ComposerTemporalDefinitionFork
open TruthCore.Alternatives.ActPotencyRegress (MovedNotYetInActReading)
open TruthCore.Logic (ExcludedMiddle)

theorem anotherMoverOfActualMover {B R : Type}
    (Moved InAct : B → R → Prop) (Moves : B → B → R → Prop)
    (hActual : ReducedOnlyByABeingInActReading Moved Moves InAct)
    (hNotYet : MovedNotYetInActReading Moved InAct) :
    MovedByAnotherReading Moved Moves := by
  sorry

theorem distinctOfNoSelf {B R : Type} (E : B → B → R → Prop)
    (h : NothingIsEfficientCauseOfItselfReading E) :
    EffectsHaveDistinctCauses E := by
  sorry

theorem alternativeOrOriginOfOrigin {B R : Type} (f : CauseFrame B R)
    (h : SelfEfficientCausationIsSelfOrigination f) :
    SelfEfficientHasAlternativeOrOrigin f := by
  sorry

theorem distinctOfNoOrigin {B R : Type} (f : CauseFrame B R)
    (hAlt : SelfEfficientHasAlternativeOrOrigin f)
    (hOrigin : NothingOriginatesItself f) (hEM : ExcludedMiddle) :
    EffectsHaveDistinctCauses f.EfficientlyCausesIn := by
  sorry

theorem firstEfficientOfDistinct {B R : Type}
    (E : B → B → R → Prop) (PerSe : B → B → Prop)
    (hOrder : OrderOfEfficientCausesFoundReading E)
    (hDistinct : EffectsHaveDistinctCauses E)
    (hPerSe : SecondEfficientCausesCauseOnlyAsCausedReading E PerSe)
    (hRegress : NoInfinitePerSeEfficientCauseSeriesReading PerSe) :
    FirstEfficientCauseCannotBeLackingReading E := by
  sorry

universe u v w

theorem uniterOfAllTime {f : Frame.{u,v,w}} (h : AllTimeNoSelf f) :
    NoTemporalSelfUniter f := by
  sorry

theorem compositionOfNoSelfUniter (f : Frame.{u,v,w}) (Composite : f.Being → Prop)
    (Component : f.Being → f.Being → Prop)
    (CausesIn : f.Being → f.Being → f.Respect → Prop) (esse : f.Respect)
    (hTwo : CompositeHasTwoDistinctComponentsReading Composite Component)
    (hUnite : DiverseUnitedOnlyThroughUnitingCauseReading Component f.Unites)
    (hComposer : TemporalComposer f)
    (hBeing : UnitingCauseCausesBeingReading f.Unites CausesIn esse)
    (hNoSelf : NoTemporalSelfUniter f) :
    CompositeHasAUnitingCauseReading Composite CausesIn esse := by
  sorry

open TruthCore.Causality.PartMediatedSelfMotion in
theorem boundaries : Control.Boundaries := by
  sorry

end TruthCore.Results.Case.Catholicism.NoSelfCauseScope
