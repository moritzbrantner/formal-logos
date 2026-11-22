module

public import TruthCore.Modal.NecessaryIfExistent

@[expose] public section

namespace TruthCore.Results.Modal.NecessaryIfExistent
open TruthCore.Modal TruthCore.Modal.NecessaryIfExistent
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

/-- Euclidean accessibility alone transports the boxed conditional across
siblings. Neither reflexivity, transitivity nor seriality is used. -/
theorem forward {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) :
    Dia F G w → Box F G w := by
  rintro ⟨v, hv, hg⟩ z hz
  exact hn v hv hg z (he w v z hv hz)

/-- Reverse escalation is constructive under exactly the same modal premise. -/
theorem reverse {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) :
    Dia F (fun v => ¬ G v) w → Box F (fun v => ¬ G v) w := by
  rintro ⟨v, hv, hng⟩ z hz hg
  exact hng (hn z hz hg v (he w z v hz hv))

/-- EM supplies coverage; it chooses no preferred disjunct. -/
theorem certificate : Certificate := by
  intro W F G w he hn hem
  refine ⟨forward F G w he hn, reverse F G w he hn, ?_⟩
  rcases hem (Dia F G w) with hp | hnp
  · exact Or.inl (forward F G w he hn hp)
  · exact Or.inr (fun v hv hg => hnp ⟨v, hv, hg⟩)

/-- A successor, unlike coverage, rules out the conjunction. Empty successor
sets must not be called an exclusive dichotomy. -/
theorem exclusive {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (hs : ∃ v, F.access w v) :
    ¬ (Box F G w ∧ Box F (fun v => ¬ G v) w) := by
  rintro ⟨hp, hn⟩
  obtain ⟨v, hv⟩ := hs
  exact hn v hv (hp v hv)

/-- S5 specialization reuses the K5 proof and the existing cube semantics. -/
theorem s5 {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (hs : FrameSatisfies .S5 F) (hn : NecessaryIf F G w)
    (hem : TruthCore.Logic.ExcludedMiddle) : Matrix F G w ∧
      ¬ (Box F G w ∧ Box F (fun v => ¬ G v) w) := by
  exact ⟨certificate W F G w hs.2 hn hem,
    exclusive F G w ⟨w, hs.1 w⟩⟩

/-- The proponent still owes PossibleExistence; the conditional alone supplies none. -/
theorem positive {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) (hp : PossibleExistence F G w) :
    NecessaryExistence F G w := forward F G w he hn hp

/-- The reverse rival owes PossibleNonexistence under the same modal assumptions. -/
theorem negative {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) (hp : PossibleNonexistence F G w) :
    ImpossibleExistence F G w := reverse F G w he hn hp

/-- Coverage chooses no side; explicit classicality is needed only here. -/
theorem coverage {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w)
    (hem : TruthCore.Logic.ExcludedMiddle) : Coverage F G w :=
  (certificate W F G w he hn hem).2.2

set_option synthInstance.maxSize 4096 in
theorem controls : Controls := by
  dsimp [Controls, FrameSatisfies, ActualConditional, NecessaryIf, Box, Dia,
    Euclidean, Serial, Reflexive, Transitive, ascending, universal, empty, identity, G]
  decide

/-- In one fixed classical modal interpretation, absence of impossibility is
possibility. This uses the explicitly supplied excluded-middle premise, and
must not be read as an inference from *no known proof* of impossibility. -/
theorem absence_of_impossibility_iff_possible {W : Type} (F : Frame W)
    (P : W → Prop) (w : W) (hem : TruthCore.Logic.ExcludedMiddle) :
    (¬ ImpossibleExistence F P w) ↔ PossibleExistence F P w := by
  constructor
  · intro hnot
    rcases hem (PossibleExistence F P w) with hp | hno
    · exact hp
    · exfalso
      apply hnot
      intro v hv hP
      exact hno ⟨v, hv, hP⟩
  · rintro ⟨v, hv, hP⟩ hbox
    exact hbox v hv hP

/-- The precise slogan's conditional application: S5, essential necessity
and *metaphysical* non-impossibility yield actual G. No profile, God naming
or metaphysical accessibility interpretation is supplied by this theorem. -/
theorem s5_not_impossible_actual {W : Type} (F : Frame W)
    (G : W → Prop) (w : W) (hs : FrameSatisfies .S5 F)
    (hn : NecessaryIf F G w) (hem : TruthCore.Logic.ExcludedMiddle)
    (hnot : ¬ ImpossibleExistence F G w) : G w := by
  have hp : PossibleExistence F G w :=
    (absence_of_impossibility_iff_possible F G w hem).mp hnot
  have hbox : NecessaryExistence F G w := positive F G w hs.2 hn hp
  exact hbox w (hs.1 w)

/-- Adding a label or a further property cannot repair two independently
incompatible essential attributes of the SAME bearer at the SAME world.
This does not declare that any particular divine pair is incompatible. -/
theorem incompatible_bundle_not_possible {W B : Type} (F : Frame W)
    (P Q tag : W → B → Prop) (w : W)
    (hExclude : ∀ v x, P v x → ¬ Q v x) :
    ¬ Dia F (fun v => ∃ x, P v x ∧ Q v x ∧ tag v x) w := by
  rintro ⟨v, _hv, x, hp, hq, _htag⟩
  exact (hExclude v x hp) hq

/-- One possible maximal profile carries ONE rigid individual through to the
actual world and every world in its S5 component. This is not the invalid
shift from worldwise nonempty existential populations to a shared individual.
The excellence predicate remains supplied until related to the GOD_4 senses. -/
theorem possible_maximal_profile_same_bearer {W B : Type} (F : Frame W)
    (existsAt excellent : W → B → Prop) (w : W)
    (hs : FrameSatisfies .S5 F)
    (hPoss : PossibleMaximalProfile F existsAt excellent w) :
    ∃ x, excellent w x ∧ MaximalProfile F existsAt excellent x w := by
  obtain ⟨v, hwv, x, _hEx, _hExcellent, hAcross⟩ := hPoss
  have hSym : Symmetric F :=
    reflexive_euclidean_implies_symmetric F hs.1 hs.2
  have hvw : F.access v w := hSym w v hwv
  have hActual : existsAt w x ∧ excellent w x := hAcross w hvw
  refine ⟨x, hActual.2, ⟨hActual.1, hActual.2, ?_⟩⟩
  intro u hwu
  exact hAcross u (hs.2 w v u hwv hwu)

end TruthCore.Results.Modal.NecessaryIfExistent
