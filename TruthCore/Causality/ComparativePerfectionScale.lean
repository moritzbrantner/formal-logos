module

public import Mathlib.Data.Set.Lattice.Order
public import TruthCore.Causality.GradesFrame
public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Results.Causality.Round3FourthWay.Solution

/-! A common ordinal representation for the Fourth Way's two comparative
calibrations and its two null conditions. The receiving-capacity inference
has separate premises about the same degree map. -/

@[expose] public section

namespace TruthCore.Causality.ComparativePerfectionScale

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Causality.Round3FourthWay
open TruthCore.Latin.Aquinas.SummaTheologiae

variable {W B T R D : Type}

/-- One degree assignment and one null for the four existing conditions.
The reverse calibration ranges only over bearers of the selected perfection. -/
structure Represents [Preorder D] (F : GradesFrame W B T R)
    (degree : R → B → D) (null : D) : Prop where
  exceeds : MoreInExceedsDegree F.MoreIn degree
  least : NoDegreeBelowNull degree null
  above : AboveNullDegreeHasThePerfection F.InAct degree null
  reflectsOnBearers : DegreeExcessAmongBearersIsMoreIn F.InAct F.MoreIn degree

/-- The qualitative conditions needed for the common representation. -/
structure ComparativeOrder (F : GradesFrame W B T R) : Prop where
  has : MoreSuchHasThePerfectionReading F.InAct F.MoreIn
  irrefl : ∀ r x, ¬ F.MoreIn r x x
  transOnBearers : ∀ r x y z, F.InAct x r → F.InAct y r → F.InAct z r →
    F.MoreIn r x y → F.MoreIn r y z → F.MoreIn r x z

theorem comparativeOrderOfRepresentation [Preorder D] {F : GradesFrame W B T R}
    {degree : R → B → D} {null : D} (h : Represents F degree null) :
    ComparativeOrder F where
  has := TruthCore.Results.Causality.Round3FourthWay.moreSuchFromPositiveDegree
    F.InAct F.MoreIn degree null h.exceeds h.least h.above
  irrefl := fun r x hxx => (lt_irrefl _) (h.exceeds r x x hxx)
  transOnBearers := fun r x y z hx _ hz hxy hyz =>
    h.reflectsOnBearers r x z hx hz (lt_trans (h.exceeds r y z hyz) (h.exceeds r x y hxy))

/-- Rank by the bearers weakly below the candidate: include the candidate
itself only if it has the perfection. Compare these sets by inclusion. -/
def bearerCone (F : GradesFrame W B T R) (r : R) (x : B) : Set B :=
  { y | F.InAct y r ∧ (y = x ∨ F.MoreIn r x y) }

theorem coneEmptyOfAbsence {F : GradesFrame W B T R} (h : ComparativeOrder F)
    {r : R} {x : B} (hx : ¬ F.InAct x r) : bearerCone F r x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  rcases hy.2 with hyx | hxy
  · exact hx (hyx ▸ hy.1)
  · exact hx (h.has r x y hxy)

theorem representsByBearerCones {F : GradesFrame W B T R} (h : ComparativeOrder F) :
    Represents F (bearerCone F) ∅ where
  exceeds := by
    intro r x y hxy
    have hx := h.has r x y hxy
    rw [lt_iff_le_not_ge]
    constructor
    · intro z hz
      refine ⟨hz.1, Or.inr ?_⟩
      rcases hz.2 with hzy | hyz
      · exact hzy ▸ hxy
      · exact h.transOnBearers r x y z hx (h.has r y z hyz) hz.1 hxy hyz
    · intro hReverse
      have hmem : x ∈ bearerCone F r x := ⟨hx, Or.inl rfl⟩
      have hInY := hReverse hmem
      rcases hInY.2 with hEq | hyx
      · exact h.irrefl r x (hEq.symm ▸ hxy)
      · exact h.irrefl r x (h.transOnBearers r x y x hx (h.has r y x hyx) hx hxy hyx)
  least := fun _ _ => bot_le
  above := by
    intro r x hPositive
    rcases Set.nonempty_iff_ne_empty.mpr (ne_of_gt hPositive) with ⟨y, hy⟩
    rcases hy.2 with hEq | hxy
    · exact hEq ▸ hy.1
    · exact h.has r x y hxy
  reflectsOnBearers := by
    intro r x y _ hy hlt
    have hySelf : y ∈ bearerCone F r y := ⟨hy, Or.inl rfl⟩
    have hyInX := (le_of_lt hlt) hySelf
    rcases hyInX.2 with hEq | hxy
    · exact False.elim ((ne_of_lt hlt) (congrArg (bearerCone F r) hEq))
    · exact hxy

theorem representationIffComparativeOrder (F : GradesFrame W B T R) :
    (∃ (degree : R → B → Set B) (null : Set B), Represents F degree null) ↔
      ComparativeOrder F :=
  ⟨fun ⟨_, _, h⟩ => comparativeOrderOfRepresentation h,
    fun h => ⟨bearerCone F, ∅, representsByBearerCones h⟩⟩

/-- The constructed null is exact absence. In particular the construction
places every bearer strictly above every nonbearer of that same perfection. -/
theorem conePositiveIffPossession {F : GradesFrame W B T R} (h : ComparativeOrder F)
    {r : R} {x : B} : ∅ < bearerCone F r x ↔ F.InAct x r :=
  ⟨(representsByBearerCones h).above r x, fun hx =>
    lt_of_le_not_ge bot_le (fun hEmpty => hEmpty (show x ∈ bearerCone F r x from
      ⟨hx, Or.inl rfl⟩))⟩

/-- If the whole selected comparison domain possesses the perfection, the
restricted reverse direction already gives exact calibration on that domain. -/
theorem exactCalibrationOfAllBearers [Preorder D] {F : GradesFrame W B T R}
    {degree : R → B → D} {null : D} (h : Represents F degree null)
    (r : R) (hAll : ∀ x, F.InAct x r) :
    MoreInMatchesDegreeEverywhere F.MoreIn r (degree r) :=
  fun x y => ⟨h.exceeds r x y, h.reflectsOnBearers r x y (hAll x) (hAll y)⟩

/-- An exact scalar representation cannot collapse two incomparable bearers
to a tie if one of them has a strict comparison with a third that the other
lacks. The finite control below realizes this pattern. -/
theorem noExactLinearRankOfIncomparability [LinearOrder D]
    {F : GradesFrame W B T R} {r : R} {value : B → D} {x y z : B}
    (hxy : F.MoreIn r x y) (hnxz : ¬ F.MoreIn r x z) (hnzx : ¬ F.MoreIn r z x)
    (hnzy : ¬ F.MoreIn r z y) :
    ¬ MoreInMatchesDegreeEverywhere F.MoreIn r value := by
  intro h
  have heq : value x = value z :=
    le_antisymm (le_of_not_gt (fun hlt => hnxz ((h x z).mpr hlt)))
      (le_of_not_gt (fun hlt => hnzx ((h z x).mpr hlt)))
  exact hnzy ((h z y).mpr (heq ▸ (h x y).mp hxy))

/-- The weak local sufficiency conditions for crossing a recipient's capacity.
A bound on the degree must imply actual limitation, and the two values must
be comparable for the tuple in question. Both hypotheses concern the same
degree and capacity. A fixed linear order supplies the second hypothesis. -/
theorem exceedsCapacityOfWithinImpliesLimited [Preorder D]
    (F : GradesFrame W B T R) (LimitedBy : B → R → B → Prop)
    (degree : R → B → D) (capacity : B → R → D)
    (hWithin : ∀ y r z, F.InAct y r → degree r y ≤ capacity z r → LimitedBy y r z)
    (hComparable : ∀ y r z, F.InAct y r → degree r y ≤ capacity z r ∨ capacity z r ≤ degree r y) :
    UnlimitedHavingExceedsCapacity F.InAct LimitedBy (fun y r => degree r y) capacity := by
  intro y r z hy hn
  have hNotWithin : ¬ degree r y ≤ capacity z r := fun h => hn (hWithin y r z hy h)
  exact lt_of_le_not_ge ((hComparable y r z hy).resolve_left hNotWithin) hNotWithin

end TruthCore.Causality.ComparativePerfectionScale
