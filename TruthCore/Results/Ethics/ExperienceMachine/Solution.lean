module

public import TruthCore.Ethics.ExperienceMachine

/-!
Results of the experience-machine test of ST I q.5 a.1's "each thing is desirable
insofar as it is perfect". Analyst formulations, attribution deferred. See
`docs/notes/experience-machine.md`.
-/

@[expose] public section

namespace TruthCore.Results.Ethics.ExperienceMachine

open TruthCore.Latin.Aquinas.SummaTheologiae TruthCore.Ethics.ExperienceMachine
open TruthCore.Logic.StrengthComparison

/-- Near-transcription (instantiation): the stay-out verdict on two lives with the
same experiential profile, with the transfer bridge, gives a respect in which one
is desirable and the other is not, which experientialism excludes. Conjunct 8 of
`ExperienceMachineComparison` shows that the premise bundle, with the lives and
the betterness relation existentially closed, is equivalent to the conclusion: the
verdict is exactly a counterexample to experientialism, and all evidential weight
lies in the verdict and the bridge. -/
theorem experientialismFailsFromStayOut {Being Perfection Profile : Type}
    (experience : Being → Profile) (DesirableIn : Being → Perfection → Prop)
    (BetterFor : Being → Being → Prop) (real machine : Being)
    (hSame : SameExperience experience real machine)
    (hVerdict : StayOutVerdict BetterFor real machine)
    (hBridge : BetterRequiresRespectDifference BetterFor DesirableIn) :
    ExperientialismFails experience DesirableIn := by
  intro hExp
  obtain ⟨p, hReal, hMachine⟩ := hBridge real machine hVerdict
  exact hMachine (((experientialism_iff_pointwise experience DesirableIn).mp hExp
    real machine hSame p).mp hReal)

/-- Strength registration: q.5's biconditional gives its forward half. -/
theorem perfectMakesDesirableOfInsofar {Being Perfection : Type}
    (DesirableIn PerfectIn : Being → Perfection → Prop)
    (hInsofar : DesirableInsofarAsPerfectReading DesirableIn PerfectIn) :
    PerfectMakesDesirableReading DesirableIn PerfectIn :=
  fun x p h => (hInsofar x p).mpr h

/-- Strength registration: q.5's biconditional gives its backward half. -/
theorem desirableOnlyIfPerfectOfInsofar {Being Perfection : Type}
    (DesirableIn PerfectIn : Being → Perfection → Prop)
    (hInsofar : DesirableInsofarAsPerfectReading DesirableIn PerfectIn) :
    DesirableOnlyIfPerfectReading DesirableIn PerfectIn :=
  fun x p h => (hInsofar x p).mp h

theorem forwardExactDifference : ForwardExactDifference := by
  intro Being Perfection DesirableIn PerfectIn
  change DesirableInsofarAsPerfectReading DesirableIn PerfectIn ↔
    PerfectMakesDesirableReading DesirableIn PerfectIn ∧
      DesirableOnlyIfPerfectReading DesirableIn PerfectIn
  exact ⟨fun h => ⟨fun x p hp => (h x p).mpr hp, fun x p hd => (h x p).mp hd⟩,
    fun ⟨hF, hB⟩ x p => ⟨hB x p, hF x p⟩⟩

theorem backwardExactDifference : BackwardExactDifference := by
  intro Being Perfection DesirableIn PerfectIn
  change DesirableInsofarAsPerfectReading DesirableIn PerfectIn ↔
    DesirableOnlyIfPerfectReading DesirableIn PerfectIn ∧
      PerfectMakesDesirableReading DesirableIn PerfectIn
  exact ⟨fun h => ⟨fun x p hd => (h x p).mp hd, fun x p hp => (h x p).mpr hp⟩,
    fun ⟨hB, hF⟩ x p => ⟨hB x p, hF x p⟩⟩

theorem experienceMachineComparison : ExperienceMachineComparison := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Being Perfection Profile experience DesirableIn
    exact experientialism_iff_factor experience DesirableIn
  · intro Being Perfection Profile experience PerfectIn
    constructor
    · rintro ⟨D, hIns, hExp⟩
      have hEq : D = PerfectIn := funext fun x => funext fun p => propext (hIns x p)
      subst hEq
      exact hExp
    · intro hSup
      exact ⟨PerfectIn, fun _ _ => Iff.rfl, hSup⟩
  · intro Being Perfection Profile experience DesirableIn PerfectIn real machine p hSame hCase
    rintro ⟨hIns, hExp⟩
    obtain ⟨_, hReal, hMachine⟩ := hCase
    have hD : DesirableIn real p := (hIns real p).mpr hReal
    have hD' : DesirableIn machine p :=
      (((experientialism_iff_pointwise experience DesirableIn).mp hExp real machine hSame p).mp hD)
    exact hMachine ((hIns machine p).mp hD')
  · intro Being Perfection DesirableIn PerfectIn BetterFor real machine p hIns hCase hDom
    obtain ⟨hSub, hReal, hMachine⟩ := hCase
    apply hDom real machine
    · intro q hq
      exact (hIns real q).mpr (hSub q ((hIns machine q).mp hq))
    · exact ⟨p, (hIns real p).mpr hReal, fun h => hMachine ((hIns machine p).mp h)⟩
  · intro Being Perfection Profile experience DesirableIn BetterFor real machine hExp hSame hBridge
      hVerdict
    exact experientialismFailsFromStayOut experience DesirableIn BetterFor real machine hSame
      hVerdict hBridge hExp
  · intro Being Perfection DesirableIn PerfectIn
    constructor
    · intro h
      exact ⟨fun x p hp => (h x p).mpr hp, fun x p hd => (h x p).mp hd⟩
    · rintro ⟨hF, hB⟩ x p
      exact ⟨hB x p, hF x p⟩
  · intro Being Perfection Profile experience DesirableIn PerfectIn real machine p hExp hSame hCase
    obtain ⟨_, hReal, hMachine⟩ := hCase
    have hPt := (experientialism_iff_pointwise experience DesirableIn).mp hExp real machine hSame p
    refine ⟨fun hF => ⟨hPt.mp (hF real p hReal), hMachine⟩, fun hB => ⟨?_, hReal⟩⟩
    intro hD
    exact hMachine (hB machine p (hPt.mp hD))
  · intro Being Perfection Profile experience DesirableIn
    constructor
    · rintro ⟨real, machine, BetterFor, hSame, hVerdict, hBridge⟩
      exact experientialismFailsFromStayOut experience DesirableIn BetterFor real machine hSame
        hVerdict hBridge
    · intro hFails
      rw [ExperientialismFails, experientialism_iff_pointwise] at hFails
      simp only [not_forall] at hFails
      obtain ⟨x, y, hxy, p, hp⟩ := hFails
      by_cases hx : DesirableIn x p
      · have hy : ¬ DesirableIn y p := fun hy => hp ⟨fun _ => hy, fun _ => hx⟩
        exact ⟨x, y, fun a b => DesirableIn a p ∧ ¬ DesirableIn b p, hxy, ⟨hx, hy⟩,
          fun _ _ h => ⟨p, h⟩⟩
      · have hy : DesirableIn y p := by
          by_contra hy
          exact hp ⟨fun h => absurd h hx, fun h => absurd h hy⟩
        exact ⟨y, x, fun a b => DesirableIn a p ∧ ¬ DesirableIn b p, hxy.symm, ⟨hy, hx⟩,
          fun _ _ h => ⟨p, h⟩⟩

open TruthCore.Ethics.ExperienceMachine.Carrier in
theorem experienceMachineControls : ExperienceMachineControls := by
  have domBetter : ∀ (D : Life → Good → Prop), RespectDominanceMakesBetter (Dominates D) D :=
    fun _ _ _ h₁ h₂ => ⟨h₁, h₂⟩
  have domBridge : ∀ (D : Life → Good → Prop),
      BetterRequiresRespectDifference (Dominates D) D :=
    fun _ _ _ h => h.2
  refine ⟨⟨?_, ?_, ?_, ?_, domBetter _, domBridge _, ?_, ?_⟩,
    ⟨?_, ?_, ?_, domBetter _, domBridge _, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩⟩ <;>
  simp only [DesirableInsofarAsPerfectReading, PerfectInsofarAsInActReading, SameExperience,
    RealPerfectionsExceed, StayOutVerdict, Dominates, PerfectMakesDesirableReading,
    DesirableOnlyIfPerfectReading, BetterRequiresRespectDifference,
    experientialism_iff_pointwise] <;>
  decide

end TruthCore.Results.Ethics.ExperienceMachine
