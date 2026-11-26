module

/-! Four equally weighted tickets compare sensitivity to an independently specified good with neutral selection and an aligned cue. -/

@[expose] public section

namespace TruthCore.Causality.ChoiceEvidence

-- Four equally weighted tickets in the order listed. True selects plan A.
def tickets (a b c d : Bool) := [a, b, c, d]

def responsive (favoursA : Bool) := tickets favoursA favoursA favoursA (!favoursA)

def neutral := tickets true true false false

def matchCount (fact : Bool) (xs : List Bool) := (xs.filter (· == fact)).length

theorem discriminate (fact : Bool) :
    matchCount fact (responsive fact) = 3 ∧ matchCount fact neutral = 2 ∧
    matchCount fact (responsive (!fact)) = 1 := by
  cases fact <;> decide

-- Under aligned inputs even the ordered plan outputs match, ticket by ticket.
theorem aligned (fact cue : Bool) (h : fact = cue) :
    responsive fact = responsive cue := by
  rw [h]

end TruthCore.Causality.ChoiceEvidence
