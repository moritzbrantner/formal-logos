module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7UnitingControl

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseControls
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

/-- Each of the five uniting-cause premises is needed for the derivation of
`CompositeHasAUnitingCauseReading`, and the five are jointly satisfiable with a
composite present. -/
theorem checks : Control.Certificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `true` is composite with the single component `false`; nothing causes.
    refine ⟨Bool, Unit, fun x => x = true, fun a x => a = false ∧ x = true,
      fun _ _ _ _ => False, fun _ _ _ => False, fun _ _ _ => False, (), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨a, b, ha, hb, hab⟩ := h true rfl
      exact hab (ha.1.trans hb.1.symm)
    · intro x hx
      exact ⟨false, ⟨rfl, hx⟩, fun h => Bool.noConfusion (h.trans hx)⟩
    · intro x a b ha hb hab
      exact (hab (ha.1.trans hb.1.symm)).elim
    · intro _ _ _ _ h
      exact h.elim
    · intro _ _ _ _ h
      exact h.elim
    · intro _ _ h
      exact h
    · intro h
      obtain ⟨_, _, hc⟩ := h true rfl
      exact hc
  · -- `true` has components `false` and `true`, but nothing unites them.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun _ _ _ _ => False, fun _ _ _ => False, fun _ _ _ => False, (), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro h
      obtain ⟨_, hc⟩ := h true false true rfl rfl (fun h => Bool.noConfusion h)
      exact hc
    · intro _ _ _ _ h
      exact h.elim
    · intro _ _ _ _ h
      exact h.elim
    · intro _ _ h
      exact h
    · intro h
      obtain ⟨_, _, hc⟩ := h true rfl
      exact hc
  · -- The whole `true` unites itself and causes its own being, not efficiently.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun c _ _ x => c = true ∧ x = true, fun _ _ _ => False,
      fun c x _ => c = true ∧ x = true, (), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro x _ _ hx _ _
      exact ⟨true, rfl, hx⟩
    · intro h
      obtain ⟨_, hr⟩ := h true false true true ⟨rfl, rfl⟩
      exact hr
    · intro _ _ _ _ h
      exact h
    · intro _ _ h
      exact h
    · intro h
      obtain ⟨c, hne, hc, _⟩ := h true rfl
      exact hne hc
  · -- A distinct efficient uniter `false` that causes no being.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun c _ _ x => c = false ∧ x = true, fun c x _ => c = false ∧ x = true,
      fun _ _ _ => False, (), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro x _ _ hx _ _
      exact ⟨false, rfl, hx⟩
    · intro _ _ _ _ h
      exact ⟨(), h⟩
    · intro h
      exact h false false true true ⟨rfl, rfl⟩
    · intro x _ h
      exact Bool.noConfusion (h.1.symm.trans h.2)
    · intro h
      obtain ⟨_, _, hc⟩ := h true rfl
      exact hc
  · -- The whole `true` efficiently unites itself and causes its own being.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun c _ _ x => c = true ∧ x = true, fun c x _ => c = true ∧ x = true,
      fun c x _ => c = true ∧ x = true, (), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro x _ _ hx _ _
      exact ⟨true, rfl, hx⟩
    · intro _ _ _ _ h
      exact ⟨(), h⟩
    · intro _ _ _ _ h
      exact h
    · intro h
      exact h true () ⟨rfl, rfl⟩
    · intro h
      obtain ⟨c, hne, hc, _⟩ := h true rfl
      exact hne hc
  · -- A distinct efficient uniter `false` that causes the being of `true`.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun c _ _ x => c = false ∧ x = true, fun c x _ => c = false ∧ x = true,
      fun c x _ => c = false ∧ x = true, (), ?_, ?_, ?_, ?_, ?_, ⟨true, rfl⟩⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro x _ _ hx _ _
      exact ⟨false, rfl, hx⟩
    · intro _ _ _ _ h
      exact ⟨(), h⟩
    · intro _ _ _ _ h
      exact h
    · intro x _ h
      exact Bool.noConfusion (h.1.symm.trans h.2)

  · -- A stronger omission: a genuine composite 3, two proper parts 0 and 1,
    -- and a third, distinct efficient uniter 2. Their union is nonvacuous
    -- but none of the efficient activity causes the composite's esse.
    refine ⟨⟨3, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a x hPart
      rcases hPart with ⟨hx, hPart⟩
      rcases hPart with ha | ha
      · subst a
        subst x
        decide
      · subst a
        subst x
        decide
    · intro x hx
      change x = (3 : Fin 4) at hx
      subst x
      exact ⟨0, 1, by decide, by decide, by decide⟩
    · intro x a b ha hb hab
      exact ⟨2, rfl, ha, hb, hab⟩
    · intro c a b x hu
      obtain ⟨hc, ha, _, _⟩ := hu
      exact ⟨(), hc, ha.1⟩
    · intro x _ hx
      obtain ⟨hc, hw⟩ := hx
      exact (by decide : (2 : Fin 4) ≠ 3) (hc.symm.trans hw)
    · exact ⟨2, 0, 1, 3, by decide⟩
    · intro h
      exact h 2 0 1 3 (by decide)
    · intro h
      obtain ⟨c, _, hc⟩ := h 3 (by decide)
      exact hc

end TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseControls
