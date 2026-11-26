module

public import TruthCore.Causality.RelaySourceRecognition
public import TruthCore.Results.Causality.FiniteGroundingHasSource.Solution

@[expose] public section
namespace TruthCore.Results.Causality.RelaySourceRecognition

open TruthCore.Causality
open TruthCore.Causality.RelaySourceRecognition
open TruthCore.Logic.CorrectionCriterion (AdmitsCriterion)

private theorem primaryCutStep (d n : Nat) (cut : Option Nat) :
    ReachesFeed d cut n ↔ n = d ∨ (cut ≠ some n ∧ ReachesFeed d cut (n + 1)) := by
  constructor
  · rintro ⟨depth, retains⟩
    rcases Nat.eq_or_lt_of_le depth with atFeed | below
    · exact Or.inl atFeed
    · exact Or.inr ⟨retains n (Nat.le_refl _) below, Nat.succ_le_of_lt below,
        fun i above under => retains i (Nat.le_of_succ_le above) under⟩
  · rintro (rfl | ⟨intact, depth, retains⟩)
    · exact ⟨Nat.le_refl _, fun i above under => False.elim (Nat.not_lt_of_ge above under)⟩
    · refine ⟨Nat.le_of_succ_le depth, ?_⟩
      intro i above under
      rcases Nat.eq_or_lt_of_le above with rfl | strictlyAbove
      · exact intact
      · exact retains i (Nat.succ_le_of_lt strictlyAbove) under

private theorem active_iff (d : Nat) (sourced entranceIntact : Bool)
    (cut : Option Nat) :
    LocalActivity d sourced entranceIntact cut (active d sourced entranceIntact cut) := by
  intro x
  change active d sourced entranceIntact cut x ↔
    intrinsic sourced x ∨ ∃ y, transmits d sourced entranceIntact cut y x
  cases x with
  | feed =>
    constructor
    · intro on
      cases sourced with
      | true => exact Or.inl rfl
      | false => exact Or.inr ⟨.auxiliary 0, ⟨rfl, rfl, on⟩, rfl⟩
    · rintro (source | ⟨supplier, retained, _⟩)
      · change sourced = true at source
        cases source
        rfl
      · cases supplier with
        | primary n => exact False.elim retained
        | feed => exact False.elim retained
        | auxiliary n =>
          have borrowed : sourced = false := retained.2.1
          cases borrowed
          exact retained.2.2
  | auxiliary n =>
    constructor
    · intro on
      exact Or.inr ⟨.auxiliary (n + 1), rfl, on⟩
    · rintro (source | ⟨supplier, retained, on⟩)
      · exact False.elim source
      · cases supplier with
        | primary m => exact False.elim retained
        | feed => exact False.elim retained
        | auxiliary m => exact on
  | primary n =>
    constructor
    · rintro ⟨feedOn, connected⟩
      rcases (primaryCutStep d n cut).1 connected with atDepth | ⟨intact, higher⟩
      · exact Or.inr ⟨.feed, atDepth, feedOn⟩
      · exact Or.inr ⟨.primary (n + 1), ⟨rfl, intact⟩, feedOn, higher⟩
    · rintro (source | ⟨supplier, retained, on⟩)
      · exact False.elim source
      · cases supplier with
        | primary m =>
          obtain ⟨position, intact⟩ := retained
          subst m
          exact ⟨on.1, (primaryCutStep d n cut).2 (Or.inr ⟨intact, on.2⟩)⟩
        | feed => exact ⟨on, (primaryCutStep d n cut).2 (Or.inl retained)⟩
        | auxiliary m => exact False.elim retained

private theorem noIntrinsic (x : Stage) : ¬ intrinsic false x := by
  cases x with
  | primary _ => exact id
  | feed => exact Bool.noConfusion
  | auxiliary _ => exact id

private theorem descendFromDepth (d : Nat) (holds : Nat → Prop) (atDepth : holds d)
    (pass : ∀ n, n < d → holds (n + 1) → holds n) (n : Nat) (depth : n ≤ d) : holds n := by
  have descend : ∀ gap n, d = n + gap → holds n := by
    intro gap
    induction gap with
    | zero =>
      intro n atN
      have same : d = n := atN
      exact same ▸ atDepth
    | succ gap ih =>
      intro n position
      have next : d = (n + 1) + gap :=
        position.trans ((Nat.add_succ n gap).trans (Nat.succ_add n gap).symm)
      have below : n < d := by
        rw [next]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
      exact pass n below (ih (n + 1) next)
  have gapExists : ∃ gap, d = n + gap := by
    clear atDepth pass descend
    induction depth with
    | refl => exact ⟨0, rfl⟩
    | step _ ih =>
      obtain ⟨gap, position⟩ := ih
      exact ⟨gap + 1, congrArg Nat.succ position⟩
  obtain ⟨gap, position⟩ := gapExists
  exact descend gap n position

private theorem intactBaseline (d n : Nat) (depth : n ≤ d) : ReachesFeed d none n :=
  ⟨depth, fun _ _ _ impossible => by cases impossible⟩

private theorem inheritFromFeed (d : Nat) (sourced : Bool) (holds : Stage → Prop)
    (atFeed : holds .feed)
    (pass : ∀ {y x}, transmits d sourced true none y x → holds y → holds x) :
    holds (.primary 0) := by
  apply descendFromDepth d (fun n => holds (.primary n))
  · exact pass (y := .feed) ⟨rfl, Bool.or_true _⟩ atFeed
  · intro n below above
    exact pass (y := .primary (n + 1))
      ⟨⟨rfl, fun impossible => by cases impossible⟩, Bool.or_true _,
        intactBaseline d (n + 1) (Nat.succ_le_of_lt below)⟩ above
  · exact Nat.zero_le _

private theorem relayFromFeed (d : Nat) (sourced entranceIntact : Bool)
    (profile : Stage → Prop) (localRule : LocalActivity d sourced entranceIntact (some d) profile) :
    profile (.primary 0) ↔ profile .feed := by
  apply descendFromDepth d (fun n => profile (.primary n) ↔ profile .feed)
  · apply (localRule (.primary d)).trans
    constructor
    · rintro (source | ⟨supplier, retained, on⟩)
      · exact False.elim source
      · cases supplier with
        | primary m => exact False.elim (retained.2 rfl)
        | feed => exact on
        | auxiliary m => exact False.elim retained
    · exact fun on => Or.inr ⟨.feed, rfl, on⟩
  · intro n below higher
    have retained : some d ≠ some n := fun same =>
      (Nat.ne_of_lt below) (Option.some.inj same).symm
    apply (localRule (.primary n)).trans
    constructor
    · rintro (source | ⟨supplier, connected, on⟩)
      · exact False.elim source
      · cases supplier with
        | primary m =>
          have position : m = n + 1 := connected.1
          subst m
          exact higher.mp on
        | feed => exact False.elim (Nat.ne_of_lt below connected)
        | auxiliary m => exact False.elim connected
    · exact fun on => Or.inr ⟨.primary (n + 1), ⟨rfl, retained⟩, higher.mpr on⟩
  · exact Nat.zero_le _

theorem primaryCutSourceComparison : PrimaryCutSourceComparison := by
  intro d
  refine ⟨active_iff d, ?_, ?_, ?_, ?_, rfl, noIntrinsic, ?_, ?_, rfl, ?_, ?_, ?_,
    relayFromFeed d, ?_⟩
  · intro entranceIntact cut x
    apply (active_iff d false entranceIntact cut x).trans
    exact ⟨fun h => h.elim (fun impossible => False.elim (noIntrinsic x impossible)) id, Or.inr⟩
  · intro sourced
    refine ⟨⟨Bool.or_true _, intactBaseline d 0 (Nat.zero_le _)⟩, ⟨rfl, Bool.or_true _⟩, ?_⟩
    exact inheritFromFeed d sourced
      (fun x => FiniteCausalPath (transmits d sourced true none) x .feed)
      (.same _) (fun edge path => .link edge path)
  · intro sourced supplier
    cases supplier with
    | primary n => exact ⟨False.elim, fun ⟨impossible, _⟩ => Stage.noConfusion impossible⟩
    | feed => exact ⟨False.elim, fun ⟨impossible, _⟩ => Stage.noConfusion impossible⟩
    | auxiliary n =>
      exact ⟨fun ⟨atZero, borrowed, _⟩ => ⟨congrArg Stage.auxiliary atZero, borrowed⟩,
        fun ⟨same, borrowed⟩ => ⟨Stage.auxiliary.inj same, borrowed, rfl⟩⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  · exact inheritFromFeed d true
      (FinitelyGroundedPower (transmits d true true none) (intrinsic true))
      (FinitelyGroundedPower.intrinsic Stage.feed rfl) (fun edge grounded => .borrowed edge grounded)
  · intro grounded
    obtain ⟨source, _, intrinsicAtSource⟩ :=
      TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource
        Stage (transmits d false true none) (intrinsic false) (.primary 0) grounded
    exact noIntrinsic source intrinsicAtSource
  · intro sourced i
    constructor
    · intro on
      exact Nat.not_lt.mp (fun under => on.2.2 i (Nat.zero_le _) under rfl)
    · intro above
      refine ⟨Bool.or_true _, Nat.zero_le _, ?_⟩
      intro j _ under same
      cases Option.some.inj same
      exact Nat.not_lt_of_ge above under
  · rintro ⟨classifier, classifies⟩
    have positive : classifier (primaryRecord d true) := (classifies true).2 rfl
    exact noIntrinsic Stage.feed ((classifies false).1 positive)
  · intro sourced
    cases sourced <;>
      exact ⟨fun on => on.1, fun source => ⟨source, intactBaseline d 0 (Nat.zero_le _)⟩⟩
  · intro sourced profile localRule
    apply (relayFromFeed d sourced false profile localRule).trans
    apply (localRule Stage.feed).trans
    constructor
    · rintro (original | ⟨supplier, connected, _⟩)
      · exact original
      · cases supplier with
        | primary m => exact False.elim connected
        | feed => exact False.elim connected
        | auxiliary m => exact False.elim (Bool.noConfusion connected.2.2)
    · exact Or.inl

end TruthCore.Results.Causality.RelaySourceRecognition
