module

public import TruthCore.Causality.CartesianAdequacy
public import TruthCore.Causality.ComparativePerfectionScale

/-! Finite structural controls for a supplied degree map and for the two
extra capacity conditions. The causality fields of the frames are unused. -/

@[expose] public section

namespace TruthCore.Models.ComparativePerfectionScale

open TruthCore.Causality.CartesianAdequacy (gradesOf)
open TruthCore.Causality.ComparativePerfectionScale
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Causality.Round3FourthWay

abbrev degree (_ : Unit) (x : Bool) : Fin 3 := if x then 2 else 1
abbrev actual (_ : Bool) (_ : Unit) : Prop := True
abbrev raises (r : Unit) (x y : Bool) : Prop := degree r y < degree r x
abbrev limited (x : Bool) (_ : Unit) (z : Bool) : Prop := x = z
abbrev capacity (z : Bool) (_ : Unit) : Fin 3 := degree () z
abbrev frame := gradesOf actual raises (fun _ _ _ => False) ()

/-- Both bearers have a positive degree, and the strictly greater one is
qualitatively more. Each bearer is limited by itself only. The smaller
bearer's degree lies within the other's capacity despite there being no
limitation by that other bearer. -/
theorem linearScaleWithoutCapacityBridge :
    Represents frame degree 0 ∧
      ¬ UnlimitedHavingExceedsCapacity actual limited (fun y r => degree r y) capacity := by
  constructor
  · refine ⟨fun _ _ _ h => h, ?_, fun _ _ _ => trivial, fun _ _ _ _ _ h => h⟩
    have h : ∀ r x, (0 : Fin 3) ≤ degree r x := by decide
    exact h
  · intro h
    exact (by decide : ¬ (2 : Fin 3) < 1) (h false () true trivial (by decide))

abbrev vector (_ : Unit) (x : Bool) : Fin 2 × Fin 2 :=
  if x then (1, 0) else (0, 1)

abbrev vectorLimit (x : Bool) (r : Unit) (z : Bool) : Prop :=
  vector r x ≤ vector r z

/-- Interpreting limitation as falling within capacity still gives no strict
excess when the degree and capacity are incomparable. -/
theorem withinCapacityMeaningWithoutComparability :
    (∀ y r z, vector r y ≤ vector r z → vectorLimit y r z) ∧
      ¬ UnlimitedHavingExceedsCapacity actual vectorLimit (fun y r => vector r y)
        (fun z r => vector r z) :=
  ⟨fun _ _ _ h => h, fun h => by
    have hNotWithin : ¬ vectorLimit false () true := fun hWithin =>
      (by decide : ¬ (1 : Fin 2) ≤ 0) hWithin.2
    have hExceeds := h false () true trivial hNotWithin
    exact (by decide : ¬ (1 : Fin 2) ≤ 0) (le_of_lt hExceeds).1⟩

abbrev noComparison (_ : Unit) (_ _ : Bool) : Prop := False

/-- Saturating no qualitative comparisons satisfies the forward calibration
vacuously, even though both bearers have unequal strictly positive degrees. -/
theorem forwardWithoutReflection :
    MoreInExceedsDegree noComparison degree ∧ NoDegreeBelowNull degree 0 ∧
      AboveNullDegreeHasThePerfection actual degree 0 ∧
      ¬ DegreeExcessAmongBearersIsMoreIn actual noComparison degree :=
  ⟨fun _ _ _ h => h.elim, (by decide : ∀ r x, (0 : Fin 3) ≤ degree r x),
    fun _ _ _ => trivial, fun h => h () true false trivial trivial (by decide)⟩

abbrev onlyTrue (x : Bool) (_ : Unit) : Prop := x = true
abbrev absenceRank (_ : Unit) (x : Bool) : Fin 2 := if x then 1 else 0
abbrev absenceFrame := gradesOf onlyTrue noComparison (fun _ _ _ => False) ()

/-- Exactly one bearer has the perfection and the other's degree is null.
All four shared conditions hold, including reflection between bearers,
but the mixed pair has different degrees without a qualitative comparison. -/
theorem bearerReflectionWithoutMixedPairs :
    Represents absenceFrame absenceRank 0 ∧
      ¬ MoreInMatchesDegreeEverywhere noComparison () (absenceRank ()) := by
  constructor
  · refine ⟨fun _ _ _ h => h.elim, ?_, ?_, ?_⟩
    · exact (by decide : ∀ r x, (0 : Fin 2) ≤ absenceRank r x)
    · exact (by decide : ∀ r x, (0 : Fin 2) < absenceRank r x → onlyTrue x r)
    · intro r x y hx hy hlt
      subst x
      subst y
      exact (lt_irrefl _) hlt
  · exact fun h => h true false |>.mpr (by decide)

abbrev pareto (_ : Unit) (x y : Fin 3) : Prop :=
  y = 0 ∧ x = 1

abbrev paretoFrame :=
  gradesOf (fun (_ : Fin 3) (_ : Unit) => True) pareto (fun _ _ _ => False) ()

/-- Three bearers with one strict comparison admit the partial-order scale.
There is no exact linear representation of this same relation. -/
theorem partialWithoutExactLinear :
    Represents paretoFrame (bearerCone paretoFrame) ∅ ∧
      ∀ (D : Type) [LinearOrder D] (value : Fin 3 → D),
        ¬ MoreInMatchesDegreeEverywhere pareto () value := by
  constructor
  · apply representsByBearerCones
    refine ⟨fun _ _ _ _ => trivial, ?_, ?_⟩
    · intro r
      cases r
      exact (by decide : ∀ x, ¬ pareto () x x)
    · intro r x y z _ _ _ hxy hyz
      exact False.elim ((by decide : (0 : Fin 3) ≠ 1) (hxy.1.symm.trans hyz.2))
  · intro D _ value
    exact noExactLinearRankOfIncomparability (F := paretoFrame) (r := ())
      (value := value) (x := 1) (y := 0) (z := 2)
      (by decide : pareto () 1 0) (by decide : ¬ pareto () 1 2)
      (by decide : ¬ pareto () 2 1) (by decide : ¬ pareto () 2 0)

abbrev participates (x : Bool) (_ : Unit) : Prop := x = true
abbrev received (x : Bool) (_ : Unit) (z : Bool) : Prop := x = true ∧ z = false
abbrev caused (c x : Bool) (_ : Unit) : Prop := c = true ∧ x = false
abbrev receptionFrame := gradesOf actual raises caused ()

/-- The same scale leaves the causal and receptive links undetermined.
The distinct cause is true and its effect is false. Only true participates,
and its reception is in false, so participation need not yield self-reception.
The frame's dependence relation is empty, despite that cross-reception. -/
theorem linearScaleWithoutReceptionBridges :
    Represents receptionFrame degree 0 ∧
      ¬ CausedByAnotherIsParticipated receptionFrame.CausesIn participates ∧
      ¬ ParticipatedIsReceivedInParticipant participates received ∧
      ¬ HaverDependsOnRecipient received receptionFrame.DependsForBeing := by
  refine ⟨⟨fun _ _ _ h => h, linearScaleWithoutCapacityBridge.1.least,
    fun _ _ _ => trivial, fun _ _ _ _ _ h => h⟩, ?_, ?_, ?_⟩
  · intro h
    exact (by decide : ¬ participates false ()) (h true false () (by decide) ⟨rfl, rfl⟩)
  · intro h
    exact (by decide : ¬ received true () true) (h true () rfl)
  · intro h
    exact h true () false ⟨rfl, rfl⟩

end TruthCore.Models.ComparativePerfectionScale
