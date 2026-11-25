module

public import TruthCore.Case.Catholicism.ImmanentOrigins

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.ImmanentOrigins
open TruthCore.Case.Catholicism.ImmanentOrigins

theorem threeCandidates (d : Profile) (modes : TwoModes d) (personal : Subsistence d)
    (order : PersonalOrder d) (separate : Separation d) : AtLeast d := by
  obtain ⟨⟨f, hf⟩, ⟨w, hw⟩, ⟨l, hl⟩⟩ := personal
  obtain ⟨express, incline, irrefl⟩ := order
  have gen := express _ _ _ _ modes.1 hf hw
  have spir := incline _ _ _ _ modes.2.1 hf hl
  refine ⟨f, w, l, hf, hw, hl, gen, spir, modes.2.2, ?_, ?_, ?_⟩
  · intro eq
    subst w
    exact irrefl _ f hf.2 gen
  · intro eq
    subst l
    exact irrefl _ f hf.2 spir
  · intro eq
    subst l
    cases separate with
    | inl active => exact irrefl _ w hw.2 (incline _ _ _ _ active hw hl)
    | inr different => exact different w hw.2 ⟨f, hf.2, gen⟩ ⟨f, hf.2, spir⟩

theorem exhaustPersons (d : Profile) (lower : AtLeast d) (inventory : Inventory d) :
    Exactly d := by
  obtain ⟨f, w, l, h⟩ := lower
  obtain ⟨sourceFree, cover, uniqueFree, uniqueGen, uniqueSpir⟩ := inventory
  refine ⟨f, w, l, h, ?_⟩
  intro p hp
  rcases cover p hp with unorig | gen | spir
  · exact Or.inl (uniqueFree p f hp h.father.2 unorig (sourceFree f h.father))
  · exact Or.inr (Or.inl (uniqueGen p w hp h.word.2 gen ⟨f, h.father.2, h.generates⟩))
  · exact Or.inr (Or.inr (uniqueSpir p l hp h.love.2 spir ⟨f, h.father.2, h.spirates⟩))

theorem restrictExact (d : Profile) (h : Exactly d) : AtLeast d := by
  obtain ⟨f, w, l, t, _⟩ := h
  exact ⟨f, w, l, t⟩

theorem collapse : TokenCollapse := by
  intro d injective ⟨f, w, _, h⟩
  exact h.fw (injective f w (h.father.2.trans h.word.2.symm))

-- Use constructor disjointness for finite numerals; all interpretation
-- certificates in this batch have an empty permitted-axiom list.
local instance : Zero Nat := ⟨0⟩
local instance (n : Nat) : NeZero (Nat.succ n) := ⟨Nat.noConfusion⟩

set_option synthInstance.maxSize 4096
set_option maxRecDepth 4000

/-- Enumerate finite witnesses constructively for the zero-axiom controls. -/
private def checkExists : (n : Nat) → (p : Fin n → Prop) → [DecidablePred p] →
    Decidable (∃ i, p i)
  | 0, _, _ => isFalse (fun ⟨i, _⟩ => Fin.elim0 i)
  | n + 1, p, dp => by
    haveI : Decidable (∃ i : Fin n, p i.succ) := checkExists n (fun i => p i.succ)
    apply decidable_of_iff (p 0 ∨ ∃ i : Fin n, p i.succ)
    constructor
    · rintro (hz | ⟨i, hi⟩)
      · exact ⟨0, hz⟩
      · exact ⟨i.succ, hi⟩
    · rintro ⟨⟨i, bound⟩, hi⟩
      cases i with
      | zero => exact Or.inl hi
      | succ i => exact Or.inr ⟨⟨i, Nat.lt_of_succ_lt_succ bound⟩, hi⟩

private instance finExists (n : Nat) (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∃ i, p i) := checkExists n p

local macro "finite_check" : tactic =>
  `(tactic| (dsimp [single, coincident, complete, separateReceptions, iterated, fixture, TwoModes, Separation,
      PersonalOrder, Subsistence, Inventory, SourceUnderived, Classifies, UniqueUnderived,
      UniqueTerm, Underived, Receives, Realizer, Divine] <;> decide))

theorem controls : Controls := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨⟨single.word, rfl, rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl⟩,
        fun _ _ r good will => ⟨r, good, will⟩, ⟨single.love, rfl, rfl, rfl⟩⟩
    all_goals try finite_check
    intro ⟨_, w, _, h⟩
    exact (by decide : ¬ (1 : Fin 3) = 0) h.word.1
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try finite_check
    intro ⟨f, w, l, h⟩
    have fw := h.fw
    have fl := h.fl
    have wl := h.wl
    change Bool at f w l
    cases f <;> cases w <;> cases l <;> contradiction
  constructor
  · have hm : TwoModes complete := by finite_check
    have hs : Subsistence complete := by finite_check
    have ho : PersonalOrder complete := by finite_check
    have hd : Separation complete := by finite_check
    have hi : Inventory complete := by finite_check
    exact ⟨hm, hs, ho, hd, hi, exhaustPersons _ (threeCandidates _ hm hs ho hd) hi⟩
  constructor
  · have hm : TwoModes separateReceptions := by finite_check
    have hs : Subsistence separateReceptions := by finite_check
    have ho : PersonalOrder separateReceptions := by finite_check
    have hd : Separation separateReceptions := by finite_check
    have hi : Inventory separateReceptions := by finite_check
    exact ⟨hm, hs, ho, by finite_check, hd, hi, exhaustPersons _ (threeCandidates _ hm hs ho hd) hi⟩
  · have hm : TwoModes iterated := by finite_check
    have hs : Subsistence iterated := by finite_check
    have ho : PersonalOrder iterated := by finite_check
    have hd : Separation iterated := by finite_check
    refine ⟨hm, hs, ho, hd, ?_, ?_, ?_, ?_, ?_, threeCandidates _ hm hs ho hd, ?_⟩
    all_goals try finite_check
    intro ⟨f, w, l, h, cover⟩
    obtain h0 | h1 | h2 := cover (3 : Fin 4) rfl
    · exact (by decide : ¬ (0 : Fin 3).val = (3 : Fin 4).val) (h0.symm ▸ h.father.1)
    · exact (by decide : ¬ (1 : Fin 3).val = (3 : Fin 4).val) (h1.symm ▸ h.word.1)
    · exact (by decide : ¬ (2 : Fin 3).val = (3 : Fin 4).val) (h2.symm ▸ h.love.1)

end TruthCore.Results.Case.Catholicism.ImmanentOrigins
