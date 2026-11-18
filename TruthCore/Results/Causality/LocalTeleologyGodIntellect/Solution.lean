module

public import TruthCore.Causality.LocalTeleologyGodIntellect
public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill

/-! Analyst composition of the local Fifth Way and the existing first-mover /
maximum identity. One HasIntellect dictionary instantiates Intelligent and
HAS_INTELLECT_1. Its intellectual (rather than merely sensory) interpretation
remains an application burden; the proof introduces no recognition rule. -/

@[expose] public section
namespace TruthCore.Results.Causality.LocalTeleologyGodIntellect
open TruthCore.Causality.WitnessLocalTeleology
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Keep the intelligent director discarded by the old firstMover projection,
then identify it with each supplied GOD_4 maximum. No global governor needed. -/
theorem godHasIntellect {B R E : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body Cog HasIntellect IsGod : B → Prop)
    (Reg Best Chance Tends : B → E → Prop) (Dir : B → B → E → Prop)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hLocal : Bundle Moved Moves Body Cog HasIntellect Reg Best Chance Tends Dir)
    (hIdentity : FirstUnmovedMoverIsMaximeEns Moved Moves InAct MoreIn esse)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse) :
    GodHasIntellect IsGod HasIntellect := by
  obtain ⟨x, e, hl, ⟨hx, he, hb⟩, hn, hd, ha, hr, hm⟩ := hLocal
  have ht : Tends x e := (hd he hb).resolve_left (hn he)
  obtain ⟨d, _, _, hdir⟩ := ha hl ht
  obtain ⟨f, _, hfIntellect, hu, hf⟩ := hr d hx hdir
  obtain ⟨r, hmove⟩ := hm f hf
  have hFirst : IsFirstUnmovedMover Moved Moves f := ⟨⟨x, r, hmove⟩, hu⟩
  intro g hg
  exact hIdentity f hFirst g (hMaximal g hg) ▸ hfIntellect

/-- Modular consumer: whichever support option gives intellect can feed will.
The existing capacity-level will principle is retained, not exercise or freedom. -/
theorem godHasWill {B : Type} (IsGod HasIntellect HasWill : B → Prop)
    (hIntellect : GodHasIntellect IsGod HasIntellect)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill) :
    GodHasWill IsGod HasWill :=
  fun g hg => hWill g (hIntellect g hg)


/-- The identity and naming-converse assumptions can each fail while the local
intellectual director survives. The all-input model has a GOD_4 witness. -/
theorem controls : TruthCore.Causality.LocalTeleologyGodIntellect.Control.Controls := by
  let localIntellect : TruthCore.Causality.LocalTeleologyGodIntellect.Control.Local
      TruthCore.Causality.LocalTeleologyGodIntellect.Control.intellect := by
    refine ⟨false, (), Bool.false_ne_true, ⟨rfl, rfl, trivial⟩,
      (fun _ h => h), (fun h _ => Or.inr h), ?_, ?_, ?_⟩
    · intro _ _; exact ⟨true, rfl, rfl, rfl, rfl⟩
    · intro _ _ _; exact ⟨true, rfl, rfl, (fun _ h => h), rfl, rfl⟩
    · intro d h; exact ⟨(), h⟩
  have identity : TruthCore.Causality.LocalTeleologyGodIntellect.Control.Identity
      TruthCore.Causality.LocalTeleologyGodIntellect.Control.more := by
    intro f hf m hm
    have hfTrue : f = true := by obtain ⟨x, r, h⟩ := hf.1; exact h.1
    cases m
    · exact (hm.2 true ⟨rfl, rfl⟩).elim
    · exact hfTrue
  have maximal : TruthCore.Causality.LocalTeleologyGodIntellect.Control.Maximal
      TruthCore.Causality.LocalTeleologyGodIntellect.Control.intellect
      TruthCore.Causality.LocalTeleologyGodIntellect.Control.more := by
    intro g hg; cases hg
    exact ⟨trivial, fun _ h => Bool.noConfusion h.2⟩
  refine ⟨⟨localIntellect, identity, maximal, rfl, fun _ h => h⟩,
    ⟨localIntellect, (fun _ _ => ⟨trivial, fun _ h => h⟩), ?_, ?_⟩,
    ⟨localIntellect, identity, ?_, ?_⟩, ⟨identity, maximal, ?_, ?_⟩⟩
  · intro h
    have heq := h true ⟨⟨false, (), rfl, rfl⟩, fun _ h => h⟩ false
      ⟨trivial, fun _ h => h⟩
    exact Bool.noConfusion heq
  · intro h; exact Bool.noConfusion (h false rfl)
  · intro h; exact (h false rfl).2 true ⟨rfl, rfl⟩
  · intro h; exact Bool.noConfusion (h false rfl)
  · rintro ⟨x, e, hl, ⟨_, he, hb⟩, hn, hd, ha, _⟩
    obtain ⟨_, _, hFalse, _⟩ := ha hl ((hd he hb).resolve_left (hn he))
    exact hFalse
  · intro h; exact h true rfl

end TruthCore.Results.Causality.LocalTeleologyGodIntellect
