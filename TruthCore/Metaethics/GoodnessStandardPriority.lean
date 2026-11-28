module

public import TruthCore.Results.Logic.CorrectionCriterion.Solution
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

/-!
# Strict priority and option-specific eligibility

The three-edge cycle uses a single priority relation. The equal-data result
applies exact classification separately to each option.
-/

@[expose] public section

namespace TruthCore.Metaethics.GoodnessStandardPriority

open TruthCore.Logic.CorrectionCriterion

theorem noStrictCycle {F : Type} (prior : F → F → Prop)
    (trans : ∀ {x y z}, prior x y → prior y z → prior x z)
    (irrefl : ∀ x, ¬ prior x x)
    (a r d : F) (hAR : prior a r) (hRD : prior r d)
    (hDA : prior d a) : False :=
  irrefl a (trans (trans hAR hRD) hDA)

theorem eligibilityOnEqualData {S E O : Type}
    (data : S → E) (Good : S → O → Prop)
    (h : ∀ o, AdmitsCriterion data (fun s => Good s o))
    {s t : S} (same : data s = data t) (o : O) :
    Good s o ↔ Good t o :=
  ((TruthCore.Results.Logic.CorrectionCriterion.characterization.1
    S E data (fun s => Good s o)).mp (h o)) s t same

/-! ## Finite strict-priority comparison

The three facts have labels 0, 1 and 2. The census counts relations on
these labels and linear extensions of selected edges in the same order.
-/

abbrev Fact := Fin 3
abbrev Edges := Fact → Fact → Bool

def cycle (a b : Fact) : Bool := (a + 1) == b

def strictOrder (edges : Edges) : Bool :=
  decide ((∀ a, edges a a = false) ∧
    ∀ a b c, edges a b = true → edges b c = true → edges a c = true)

def extendsEdges (selected order : Edges) : Bool :=
  decide (∀ a b, selected a b = true → order a b = true)

def relations : List Edges :=
  (List.range 512).map fun mask a b => mask.testBit (3 * a.val + b.val)

def linearOrders : List Edges :=
  ([0, 1, 2] : List Fact).permutations'.map fun order a b =>
    decide (order.idxOf a < order.idxOf b)

def withoutEdge (a : Fact) : Edges := fun x y => x != a && cycle x y
def oneEdge (a : Fact) : Edges := fun x y => x == a && cycle x y

theorem cycleCensus :
    linearOrders.length = 6 ∧ (relations.filter strictOrder).length = 19 ∧
    (linearOrders.filter (extendsEdges cycle)).isEmpty ∧
    (relations.filter (fun r => strictOrder r && extendsEdges cycle r)).isEmpty ∧
    (∀ a, (linearOrders.filter (extendsEdges (withoutEdge a))).length = 1 ∧
      (relations.filter (fun r => strictOrder r && extendsEdges (withoutEdge a) r)).length = 1 ∧
      strictOrder (oneEdge a) = true) ∧
    strictOrder cycle = false ∧ cycle 0 1 ∧ cycle 1 2 ∧ cycle 0 2 = false := by
  decide +kernel

theorem cycleClosure : ∀ a b, Relation.TransGen (fun x y => cycle x y = true) a b := by
  have two (a b c : Fact) (ab : cycle a b = true) (bc : cycle b c = true) :
      Relation.TransGen (fun x y => cycle x y = true) a c :=
    Relation.TransGen.tail (Relation.TransGen.single ab) bc
  have loop (a b c : Fact) (ab : cycle a b = true) (bc : cycle b c = true)
      (ca : cycle c a = true) : Relation.TransGen (fun x y => cycle x y = true) a a :=
    (two a b c ab bc).tail ca
  intro a b
  fin_cases a <;> fin_cases b
  · exact loop 0 1 2 rfl rfl rfl
  · exact .single rfl
  · exact two 0 1 2 rfl rfl
  · exact two 1 2 0 rfl rfl
  · exact loop 1 2 0 rfl rfl rfl
  · exact .single rfl
  · exact .single rfl
  · exact two 2 0 1 rfl rfl
  · exact loop 2 0 1 rfl rfl rfl

end TruthCore.Metaethics.GoodnessStandardPriority
