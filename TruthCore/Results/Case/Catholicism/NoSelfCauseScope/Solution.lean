module

public import TruthCore.Case.Catholicism.NoSelfCauseScope
public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Logic.RootDescent

@[expose] public section

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
  intro x r hx
  obtain ⟨y, hy, ha⟩ := hActual x r hx
  exact ⟨y, fun heq => hNotYet x r hx (heq ▸ ha), hy⟩

theorem distinctOfNoSelf {B R : Type} (E : B → B → R → Prop)
    (h : NothingIsEfficientCauseOfItselfReading E) :
    EffectsHaveDistinctCauses E := by
  intro x ⟨c, r, hc⟩
  exact ⟨c, r, fun heq => h x r (heq ▸ hc), hc⟩

theorem alternativeOrOriginOfOrigin {B R : Type} (f : CauseFrame B R)
    (h : SelfEfficientCausationIsSelfOrigination f) :
    SelfEfficientHasAlternativeOrOrigin f := by
  intro x r hx
  exact Or.inr (h x r hx)

theorem distinctOfNoOrigin {B R : Type} (f : CauseFrame B R)
    (hAlt : SelfEfficientHasAlternativeOrOrigin f)
    (hOrigin : NothingOriginatesItself f) (hEM : ExcludedMiddle) :
    EffectsHaveDistinctCauses f.EfficientlyCausesIn := by
  intro x ⟨c, r, hc⟩
  rcases hEM (c = x) with heq | heq
  · subst c
    exact (hAlt x r hc).elim id (fun hs => (hOrigin x hs).elim)
  · exact ⟨c, r, heq, hc⟩

theorem firstEfficientOfDistinct {B R : Type}
    (E : B → B → R → Prop) (PerSe : B → B → Prop)
    (hOrder : OrderOfEfficientCausesFoundReading E)
    (hDistinct : EffectsHaveDistinctCauses E)
    (hPerSe : SecondEfficientCausesCauseOnlyAsCausedReading E PerSe)
    (hRegress : NoInfinitePerSeEfficientCauseSeriesReading PerSe) :
    FirstEfficientCauseCannotBeLackingReading E := by
  intro hNoFirst
  have noEffect (x : B) : ¬ ∃ c r, E c x r :=
    TruthCore.Logic.RootDescent.acc_not_of_notNot_inherited
      (P := fun x => ∃ c r, E c x r)
      (fun x hx noPredecessor => by
        obtain ⟨c, r, hne, hc⟩ := hDistinct x hx
        exact hNoFirst ⟨c, ⟨x, r, hc⟩, fun d s hd =>
          noPredecessor ⟨c, hPerSe c x r hne hc ⟨d, s, hd⟩, d, s, hd⟩⟩)
      (hRegress x)
  obtain ⟨c, x, r, hc⟩ := hOrder
  exact noEffect x ⟨c, r, hc⟩

universe u v w

theorem uniterOfAllTime {f : Frame.{u,v,w}} (h : AllTimeNoSelf f) :
    NoTemporalSelfUniter f := by
  intro x _ _ _ r ⟨t, ht⟩
  exact h t x r ht

theorem compositionOfNoSelfUniter (f : Frame.{u,v,w}) (Composite : f.Being → Prop)
    (Component : f.Being → f.Being → Prop)
    (CausesIn : f.Being → f.Being → f.Respect → Prop) (esse : f.Respect)
    (hTwo : CompositeHasTwoDistinctComponentsReading Composite Component)
    (hUnite : DiverseUnitedOnlyThroughUnitingCauseReading Component f.Unites)
    (hComposer : TemporalComposer f)
    (hBeing : UnitingCauseCausesBeingReading f.Unites CausesIn esse)
    (hNoSelf : NoTemporalSelfUniter f) :
    CompositeHasAUnitingCauseReading Composite CausesIn esse := by
  intro x hx
  obtain ⟨a, b, ha, hb, hne⟩ := hTwo x hx
  obtain ⟨c, hc⟩ := hUnite x a b ha hb hne
  refine ⟨c, ?_, hBeing c a b x hc⟩
  intro heq
  subst c
  obtain ⟨r, hr⟩ := hComposer x a b x hc
  exact hNoSelf x a b hc r hr

open TruthCore.Causality.PartMediatedSelfMotion in
theorem boundaries : Control.Boundaries := by
  have hp : Part .motor .whole := ⟨rfl, Or.inl rfl⟩
  have hq : Part .load .whole := ⟨rfl, Or.inr rfl⟩
  have hEvent : ComponentMoves .motor .load .displacement := ⟨rfl, rfl, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact .intro _ _ hp hq hEvent
  · intro x r ⟨hx, hr⟩
    subst x
    subst r
    exact ⟨.motor, Or.inl ⟨.load, hq, hEvent⟩, rfl, rfl⟩
  · intro _ _ ⟨hw, _⟩ ⟨hm, _⟩
    cases hw.symm.trans hm
  · intro h
    exact h .whole .displacement ⟨rfl, rfl⟩ (Or.inr ⟨.motor, .load, hp, hq, hEvent⟩)
  · exact ⟨true, true, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · intro _ ⟨hfalse, htrue⟩
    cases hfalse.symm.trans htrue
  · intro x r hx
    have htarget : x = true := hx.elim (fun h => h.2.1) (fun h => h.2.1)
    subst x
    exact Or.inl ⟨false, false, by decide, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro x ⟨c, r, hc⟩
    have htarget : x = true := hc.elim (fun h => h.2.1) (fun h => h.2.1)
    subst x
    exact ⟨false, false, by decide, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro h
    cases (h true true (Or.inr ⟨rfl, rfl, rfl⟩)).1
  · exact fun h => h true true (Or.inr ⟨rfl, rfl, rfl⟩)
  · exact fun h => h true true ⟨rfl, rfl, rfl⟩
  · exact fun h => h true true (Or.inr ⟨rfl, rfl, rfl⟩)
  · exact ⟨false, true, false, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro c x r hne hcx ⟨d, s, hdc⟩
    rcases hcx with h | h
    · have hc : c = true := hdc.elim (fun hh => hh.2.1) (fun hh => hh.2.1)
      cases h.1.symm.trans hc
    · exact hne (h.1.trans h.2.1.symm)
  · exact fun x => Acc.intro x (fun _ h => h.elim)
  · refine ⟨⟨true, false, Or.inl ⟨rfl, rfl, rfl⟩⟩, ?_⟩
    intro _ _ h
    exact Bool.noConfusion (h.elim (fun hh => hh.2.1) (fun hh => hh.2.1))
  · intro c a b x ⟨hc, hx⟩
    subst c
    subst x
    exact ⟨false, false, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨rfl, rfl⟩
  · intro _ _ ⟨ht, _⟩
    cases ht
  · intro _ _ _ ⟨hfalse, htrue⟩
    cases hfalse.symm.trans htrue
  · exact fun h => h false true true ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩

end TruthCore.Results.Case.Catholicism.NoSelfCauseScope
