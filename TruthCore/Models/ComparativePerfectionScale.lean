module

public import TruthCore.Causality.CartesianAdequacy
public import TruthCore.Causality.ComparativePerfectionScale

/-! Finite structural controls for a supplied degree map and for the two
extra capacity conditions. The scale and capacity controls leave the
causality fields of their frames unused. The reception control
`linearScaleWithoutReceptionBridges` assigns `CausesIn` a distinct cause and
leaves `DependsForBeing` empty. -/

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

/-- A coarse observation can collapse an acknowledged comparison on the
same two bearers, although the underlying rank preserves it. -/
theorem collapsedObservation :
    MoreInExceedsDegree raises degree ∧
      ¬ MoreInExceedsDegree raises (fun _ _ => (1 : Fin 3)) := by
  exact ⟨fun _ _ _ h => h, fun h => (lt_irrefl (1 : Fin 3))
    (h () true false (by decide))⟩

/-- The null clause requires a common lower bound even on a partial order.
Neither represented profile lies strictly below this reference profile. -/
theorem incomparableNull :
    (∀ r x, ¬ vector r x < ((1, 0) : Fin 2 × Fin 2)) ∧
      ¬ NoDegreeBelowNull vector ((1, 0) : Fin 2 × Fin 2) := by
  exact ⟨by intro r x h; cases x with
    | false => exact (by decide : ¬ (1 : Fin 2) ≤ 0) (le_of_lt h).2
    | true => exact (lt_irrefl _) h, fun h => (by decide : ¬ ((1, 0) : Fin 2 × Fin 2) ≤
    vector () false) (h () false)⟩

/-- With the same comparison and origin, raising the possession threshold
makes the lower bearer's positive reading insufficient. -/
theorem thresholdWithoutAboveNull :
    MoreInExceedsDegree raises degree ∧ NoDegreeBelowNull degree 0 ∧
      ¬ AboveNullDegreeHasThePerfection onlyTrue degree 0 := by
  exact ⟨fun _ _ _ h => h, linearScaleWithoutCapacityBridge.1.least,
    fun h => (by decide : ¬ onlyTrue false ()) (h () false (by decide))⟩

/-- Both members possess the respect at capacity. A distinct source gives
it to the effect, which limits only its own act. The capacity failure occurs
on the very causal pair. -/
theorem equalCapacityOnCausalPair :
    caused true false () ∧ actual true () ∧ ¬ limited true () false ∧
      ¬ UnlimitedHavingExceedsCapacity actual limited
        (fun _ _ => (1 : Fin 2)) (fun _ _ => (1 : Fin 2)) := by
  exact ⟨⟨rfl, rfl⟩, trivial, by decide,
    fun h => (lt_irrefl (1 : Fin 2)) (h true () false trivial (by decide))⟩

section Endpoints

open TruthCore.Causality.DirectEsseRootUniquenessAtBeing

/-- Every degree is represented by itself in the selected respect. -/
abbrev identityDegree {D : Type} (_ : Unit) (x : D) := x

abbrev hasLeast (D : Type) [Preorder D] := ∃ x : D, IsLeast Set.univ x
abbrev hasGreatest (D : Type) [Preorder D] := ∃ x : D, IsGreatest Set.univ x

theorem representedEndpointExamples :
    (hasLeast (Fin 2) ∧ hasGreatest (Fin 2)) ∧
    (¬ hasLeast ℤ ∧ ¬ hasGreatest ℤ) ∧
    (hasLeast ℕ ∧ ¬ hasGreatest ℕ) ∧
    (¬ hasLeast ℕᵒᵈ ∧ hasGreatest ℕᵒᵈ) := by
  have lower (D : Type) [PartialOrder D] [OrderBot D] : hasLeast D :=
    ⟨⊥, trivial, fun _ _ => bot_le⟩
  have upper (D : Type) [PartialOrder D] [OrderTop D] : hasGreatest D :=
    ⟨⊤, trivial, fun _ _ => le_top⟩
  have noLower (D : Type) [PartialOrder D] [NoMinOrder D] : ¬ hasLeast D := by
    rintro ⟨x, _, h⟩
    obtain ⟨y, hy⟩ := exists_lt x
    exact (not_le_of_gt hy) (h (Set.mem_univ y))
  have noUpper (D : Type) [PartialOrder D] [NoMaxOrder D] : ¬ hasGreatest D := by
    rintro ⟨x, _, h⟩
    obtain ⟨y, hy⟩ := exists_gt x
    exact (not_le_of_gt hy) (h (Set.mem_univ y))
  exact ⟨⟨lower _, upper _⟩, ⟨noLower _, noUpper _⟩, ⟨lower _, noUpper _⟩,
    ⟨noLower _, upper _⟩⟩

variable {D : Type} [LinearOrder D]

abbrev strictDegree (_ : Unit) (x y : D) : Prop := y < x
abbrev allPossess (_ : D) (_ : Unit) : Prop := True

theorem nullOnFullRange (n : D) :
    NoDegreeBelowNull identityDegree n ↔ IsLeast Set.univ n :=
  ⟨fun h => ⟨trivial, fun x _ => h () x⟩, fun h _ x => h.2 (Set.mem_univ x)⟩

theorem calibrationOnFullRange (n : D) :
    MoreInExceedsDegree strictDegree (@identityDegree D) ∧
      AboveNullDegreeHasThePerfection allPossess identityDegree n :=
  ⟨fun _ _ _ h => h, fun _ _ _ => trivial⟩

/-- With a witnessed strict pair the route's maximal bearer is exactly a
greatest degree on this fully represented linear order. -/
theorem ascentIffGreatestOnFullRange {x y : D} (hxy : x < y) :
    GradesToMaximumAtBeing allPossess (@strictDegree D _) () ↔ hasGreatest D := by
  constructor
  · intro h
    obtain ⟨m, _, hm⟩ := h ⟨y, x, hxy⟩
    exact ⟨m, trivial, fun z _ => le_of_not_gt (hm z)⟩
  · rintro ⟨m, _, hm⟩ _
    exact ⟨m, trivial, fun z => not_lt_of_ge (hm (Set.mem_univ z))⟩

/-- A measure-based limit licenses excess. Dropping that limit even at
equality defeats excess on exactly the same scale with the same capacities. -/
theorem capacityAlternativesOnFullRange (n : D) :
    UnlimitedHavingExceedsCapacity allPossess (fun (x : D) _ z => x ≤ z)
      (fun x _ => x) (fun z _ => z) ∧
    ¬ UnlimitedHavingExceedsCapacity allPossess (fun (_ : D) _ _ => False)
      (fun x _ => x) (fun z _ => z) := by
  exact ⟨fun _ _ _ _ h => lt_of_not_ge h,
    fun h => (lt_irrefl n) (h n () n trivial id)⟩

/-- The same witnessed pair tests a coarsened observation and a stricter
possession threshold, independently of either endpoint. -/
theorem observationAndThresholdExceptions {a b : D} (hab : a < b) :
    ¬ MoreInExceedsDegree (@strictDegree D _) (fun _ _ => a) ∧
    ¬ AboveNullDegreeHasThePerfection (fun x (_ : Unit) => b < x) identityDegree a :=
  ⟨fun h => (lt_irrefl a) (h () b a hab),
   fun h => (lt_irrefl b) (h () b hab)⟩

/-- Both bridges can hold on a designated causal pair if its effect
participates and receives. Swapping which bearer participates and giving
it only cross-reception defeats both bridges on the same ordered domain. -/
theorem receptionAlternativesOnFullRange {c e : D} (hec : e < c) :
    let gives := fun y x (_ : Unit) => y = c ∧ x = e
    (CausedByAnotherIsParticipated gives (fun x _ => x = e) ∧
      ParticipatedIsReceivedInParticipant (fun x (_ : Unit) => x = e)
        (fun x _ z => x = e ∧ z = x)) ∧
    (¬ CausedByAnotherIsParticipated gives (fun x _ => x = c) ∧
      ¬ ParticipatedIsReceivedInParticipant (fun x (_ : Unit) => x = c)
        (fun x _ z => x = c ∧ z = e)) := by
  exact ⟨⟨fun _ _ _ _ h => h.2, fun _ _ h => ⟨h, rfl⟩⟩,
    ⟨fun h => (ne_of_lt hec) (h c e () (ne_of_gt hec) ⟨rfl, rfl⟩),
     fun h => (ne_of_gt hec) (h c () rfl).2⟩⟩

end Endpoints

end TruthCore.Models.ComparativePerfectionScale
