module

public import TruthCore.Causality.ModalSenseSupport

/-! Frame-class strength orders among the route's open frame premises
(`OnticFrameKT`, `OnticFrameS4`, `OnticFrameKTB`, `OnticFrameS5` of
`TruthCore.Causality.NecessarySenseFork`), found by a `truth discover` run over
the modal sense-fork nodes. The proofs reuse the frame-class theorems of the
modal library (`TruthCore.Modal.s5_implies_s4` and `s5_implies_ktb` of
`TruthCore.Modal.Cube`); nothing is restated.
Each frame premise is about the same route frame `m.ontic.frame`; none is
asserted to hold. -/

@[expose] public section

namespace TruthCore.Results.Causality.ModalFrameStrength

open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.BruteFoundationBoundary (Profile)

/-- An S5 route frame is an S4 route frame (`s5_implies_s4`: a reflexive
Euclidean relation is transitive). -/
theorem frameS5ToS4 {W B : Type} (m : Profile W B) (h : OnticFrameS5 m) :
    OnticFrameS4 m :=
  s5_implies_s4 m.ontic.frame h

/-- An S5 route frame is a KTB route frame (`s5_implies_ktb`: a reflexive
Euclidean relation is symmetric). -/
theorem frameS5ToKTB {W B : Type} (m : Profile W B) (h : OnticFrameS5 m) :
    OnticFrameKTB m :=
  s5_implies_ktb m.ontic.frame h

/-- An S4 route frame is a KT route frame (its reflexivity conjunct). -/
theorem frameS4ToKT {W B : Type} (m : Profile W B) (h : OnticFrameS4 m) :
    OnticFrameKT m :=
  h.1

/-- A KTB route frame is a KT route frame (its reflexivity conjunct). -/
theorem frameKTBToKT {W B : Type} (m : Profile W B) (h : OnticFrameKTB m) :
    OnticFrameKT m :=
  h.1

/-- Strictness of the four orders, on explicit frames. -/
theorem frameStrictness : TruthCore.Causality.ModalSenseSupport.Control.FrameStrictness := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro a
    exact Or.inl rfl
  · intro h
    rcases h.2 0 1 2 (Or.inr rfl) (Or.inr rfl) with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · intro a
    show a = false ∨ a = true
    cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro h
    rcases h.2 false true (Or.inl rfl) with h | h
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  · intro a
    show a = false ∨ a = true
    cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro a b c hab hbc
    show a = false ∨ c = true
    rcases hab with h | h
    · exact Or.inl h
    · rcases hbc with h' | h'
      · exact absurd (h.symm.trans h') (by decide)
      · exact Or.inr h'
  · intro h
    rcases h.2 false true false (Or.inl rfl) (Or.inl rfl) with h | h
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  · intro a
    exact Or.inl rfl
  · intro a b h
    show b = a ∨ b + 1 = a ∨ a + 1 = b
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · intro h
    rcases h.2 1 0 2 (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) with h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)

/-- A KTB route frame that is also an S4 route frame is an S5 route frame
(`symmetric_transitive_implies_euclidean`: a symmetric transitive relation is
Euclidean). With `frameS5ToS4` and `frameS5ToKTB` this shows that the S5 frame
premise says exactly what the KTB and S4 frame premises say jointly. -/
theorem frameS5OfKTBAndS4 {W B : Type} (m : Profile W B) (hB : OnticFrameKTB m)
    (hS4 : OnticFrameS4 m) : OnticFrameS5 m :=
  ⟨hB.1, symmetric_transitive_implies_euclidean m.ontic.frame hB.2 hS4.2⟩

open TruthCore.Causality.ModalSenseSupport in
/-- Certified difference: S5 ⇔ S4 ∧ symmetric (a reflexive Euclidean frame is
symmetric; a symmetric transitive frame is Euclidean). -/
theorem frameS5OverS4Exact : FrameS5OverS4Exact := by
  intro W B m
  constructor
  · intro h
    exact ⟨s5_implies_s4 m.ontic.frame h,
      reflexive_euclidean_implies_symmetric m.ontic.frame h.1 h.2⟩
  · rintro ⟨⟨hRefl, hTrans⟩, hSym⟩
    exact ⟨hRefl, symmetric_transitive_implies_euclidean m.ontic.frame hSym hTrans⟩

open TruthCore.Causality.ModalSenseSupport in
/-- Certified difference: S5 ⇔ KTB ∧ transitive (a reflexive Euclidean frame is
transitive; a symmetric transitive frame is Euclidean). -/
theorem frameS5OverKTBExact : FrameS5OverKTBExact := by
  intro W B m
  constructor
  · intro h
    exact ⟨s5_implies_ktb m.ontic.frame h,
      reflexive_euclidean_implies_transitive m.ontic.frame h.1 h.2⟩
  · rintro ⟨⟨hRefl, hSym⟩, hTrans⟩
    exact ⟨hRefl, symmetric_transitive_implies_euclidean m.ontic.frame hSym hTrans⟩

open TruthCore.Causality.ModalSenseSupport in
/-- Certified difference: S4 ⇔ KT ∧ transitive (frame class S4 is reflexivity
together with transitivity; conjunction regrouping). -/
theorem frameS4OverKTExact : FrameS4OverKTExact := by
  intro W B m
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

open TruthCore.Causality.ModalSenseSupport in
/-- Certified difference: KTB ⇔ KT ∧ symmetric (frame class KTB is reflexivity
together with symmetry; conjunction regrouping). -/
theorem frameKTBOverKTExact : FrameKTBOverKTExact := by
  intro W B m
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

end TruthCore.Results.Causality.ModalFrameStrength
