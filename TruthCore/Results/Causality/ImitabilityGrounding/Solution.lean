module

public import TruthCore.Causality.ImitabilityGrounding
public import TruthCore.Results.Causality.AxiarchicGuidance.Solution
public import TruthCore.Results.Causality.RootClosure.Solution

/-! Conditional applications of existing priority and modal transport proofs.
The interpretations, open bridges, and model boundaries are stated in the
vocabulary module. -/

@[expose] public section

namespace TruthCore.Results.Causality.ImitabilityGrounding

open TruthCore.Causality.ImitabilityGrounding
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Explanation.PSRStrength (Arena Access Contingent failure_transport)
open TruthCore.Explanation.TruthmakerTheories (Making WorldImmanent MakerNecessitation)

/-- A three-fact cycle is excluded by the existing priority theorem. The
bridge from giving being to the exercise fact's priority is a separate
premise; it cannot be inferred from a union of differently interpreted
relations. The source may apprehend the modes or not: the proof is unchanged. -/
theorem noEffectGroundedGiving {W B T R F : Type}
    (K : CausalityFrame W B T R) (A : Arena W B F) (w : W)
    (source : B) (mode production : F) (t : T)
    (hAsym : FactPriorityAsymmetricAt A w)
    (hTrans : FactPriorityTransitiveAt A w)
    (hMode : ModeExplainsProductionAt A w mode production)
    (hGiving : GivingExercisePriorityAt K A w source production t) :
    NoEffectGroundedGivingAt K A w source mode t := by
  intro effect hEffect
  exact TruthCore.Explanation.PriorityOmission.constitutionNotPriorOfWholeFirst
    (fun f h => hAsym f f h h)
    (fun {a b c} h₁ h₂ => hTrans a b c h₁ h₂)
    hMode (hGiving effect hEffect)

/-- The accessible falsifier of the fact is also an accessible absence of
each necessitating maker, by the existing failure-transport theorem. Actual
existence of that maker uses world immanence. No necessary fact is inferred
to need a necessary maker, and no existence of a maker is inferred. -/
theorem makersOfContingentFactAreContingent {W B F : Type}
    (A : Arena W B F) (M : Making W B F) (w : W) (fact : F)
    (hActual : WorldImmanent A M)
    (hNec : MakerNecessitation A M)
    (hFact : Contingent A w fact) :
    EveryMakerContingentAt A M w fact := by
  intro b hb
  exact failure_transport (Access A) w
    (fun v => A.ontic.ExistsAt v b) (fun v => A.holds v fact)
    (fun v hv hExists => hNec w b fact hb v hv hExists)
    (hActual w b fact hb) hFact.2

namespace Availability

open TruthCore.Causality.ImitabilityGrounding.AvailabilityControl
open TruthCore.Causality.AxiarchicGuidance.Control
  (Cand Scen good)

private theorem modeInjective : Function.Injective mode := by
  intro x y h
  cases x <;> cases y <;> simp_all [mode]

private theorem modeRealization :
    ∀ s x y, good s x y ↔ InvImage (modeRelation s) mode x y := by
  intro s x y
  change good s x y ↔ ∃ a b, mode a = mode x ∧ mode b = mode y ∧ good s a b
  constructor
  · intro h
    exact ⟨x, y, rfl, rfl, h⟩
  · rintro ⟨a, b, ha, hb, h⟩
    exact modeInjective ha ▸ modeInjective hb ▸ h

private theorem rankIrreflexive : ∀ s x, ¬ good s x x := by
  intro s x
  cases s <;> cases x <;> simp [good]

end Availability

open AvailabilityControl

/-- A populated effect-absent world retains distinct modes and a ranked,
guided profile. The produced world satisfies the cycle theorem's premises
with two actual effects. Explanation is factive but not necessitating, so
necessary rank facts do not here force a necessary productive exercise. -/
theorem availabilityControl : AvailabilityControl.Certificate := by
  have hAsym : FactPriorityAsymmetricAt arena true := by
    unfold FactPriorityAsymmetricAt
    dsimp [arena, priority, basis, mode, ranking, production]
    decide
  have hTrans : FactPriorityTransitiveAt arena true := by
    unfold FactPriorityTransitiveAt
    dsimp [arena, priority, basis, mode, ranking, production]
    decide
  have hMode : ModeExplainsProductionAt arena true ranking production := by
    unfold ModeExplainsProductionAt
    dsimp [arena, priority, basis, mode, ranking, production]
    decide
  have hGiving : GivingExercisePriorityAt frame arena true 0 production () := by
    unfold GivingExercisePriorityAt
    dsimp [frame, arena, priority, basis, mode, ranking, production]
    decide
  refine ⟨?_, ?_, ?_, ?_, ?_, by trivial, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, by trivial,
    Availability.modeRealization, Availability.rankIrreflexive,
    TruthCore.Results.Causality.AxiarchicGuidance.guidanceTable.2.1,
    ?_, hAsym, hTrans, hMode, hGiving,
    noEffectGroundedGiving frame arena true 0 ranking production () hAsym hTrans hMode hGiving⟩
  · unfold TruthCore.Explanation.PSRStrength.Coherent
    dsimp [arena, frame, existsAt]
    decide
  · unfold TruthCore.Explanation.PSRStrength.Factive
    dsimp [arena, priority, basis, mode, ranking, production]
    decide
  · dsimp [arena, frame, existsAt]
    decide
  · intro x
    cases x <;> dsimp [arena, frame, existsAt, candidate] <;> decide
  · intro x
    cases x <;> dsimp [arena, frame, existsAt, candidate] <;> decide
  · intro v x
    cases v <;> cases x <;> dsimp [arena, mode] <;> decide
  · unfold TruthCore.Explanation.StoppingPoints.NecessaryFact Access
    dsimp [arena, frame, ranking]
    decide
  · intro v x
    cases v <;> cases x <;> dsimp [arena, priority, basis, mode, ranking, production] <;> decide
  · dsimp [arena, priority, basis, mode, ranking, production]
    decide
  · unfold Contingent Access
    dsimp [arena, frame, production]
    decide
  · intro x
    cases x <;> unfold Contingent Access <;> dsimp [arena, frame, candidate] <;> decide
  · unfold TruthCore.Explanation.PSRStrength.Necessitating Access
    dsimp [arena, frame, priority, basis, mode, ranking, production]
    decide
  · exact TruthCore.Results.Causality.AxiarchicFoundation.favouredIndividuated
      (TruthCore.Causality.AxiarchicGuidance.Control.good .base)
      (AvailabilityControl.modeRelation .base) AvailabilityControl.mode
      (Availability.modeRealization .base) (Availability.rankIrreflexive .base) .c .d
      (by trivial)
  · intro x
    cases x <;> dsimp [frame, candidate] <;> decide

/-- Each core premise has a populated omission witness. The third row
permits an after-the-effect descriptive mode; the fourth retains actual
giving but refuses its translation into the selected fact-priority relation.
Neither is an exclusion of all extrinsic modes. -/
theorem cycleControls : CycleControl.Certificate := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro rel
    exact ⟨fun _ _ => Iff.rfl, fun _ _ _ _ => ⟨trivial, trivial⟩⟩
  all_goals
    dsimp [CycleControl.OmitAsymmetry, CycleControl.OmitTransitivity,
      CycleControl.OmitModeRelevance, CycleControl.OmitGivingBridge,
      FactPriorityAsymmetricAt, FactPriorityTransitiveAt, ModeExplainsProductionAt,
      GivingExercisePriorityAt, NoEffectGroundedGivingAt, CycleControl.arena,
      CycleControl.frame, CycleControl.allPriority, CycleControl.cycle,
      CycleControl.posteriorMode, CycleControl.missingGivingBridge,
      CycleControl.mode, CycleControl.production, CycleControl.effect, CycleControl.Fact]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

namespace Makers

open MakerControl
open TruthCore.Explanation.TruthmakerTheories (Sound NeedsMakerAt)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt NecessaryAt)

private theorem positive : Positive := by
  have hActual : WorldImmanent contingentArena making := by
    dsimp [WorldImmanent, contingentArena, mk, making, selected, MakerControl.Fact]
    decide
  have hNec : MakerNecessitation contingentArena making := by
    dsimp [MakerNecessitation, Access, contingentArena, mk, making, selected, MakerControl.Fact]
    simp [and_imp]
  have hFact : Contingent contingentArena true selected := by
    dsimp [Contingent, Access, contingentArena, mk, selected, MakerControl.Fact]
    decide
  exact ⟨hActual, hNec, hFact, ⟨rfl, rfl, rfl⟩,
    makersOfContingentFactAreContingent contingentArena making true selected hActual hNec hFact⟩

private theorem necessaryAlternatives : NecessaryFactAlternatives := by
  have hNecessary : ∀ v, Access necessaryTruthArena true v →
      necessaryTruthArena.holds v selected := by
    intro v _
    simp [necessaryTruthArena, mk, selected]
  have hEffect : necessaryTruthArena.ontic.ExistsAt true false := Or.inr ⟨rfl, rfl⟩
  have hSource : necessaryTruthArena.ontic.ExistsAt true true := Or.inl rfl
  have hEffectMaking : Sound necessaryTruthArena making ∧
      NeedsMakerAt necessaryTruthArena making true selected ∧
      MakerNecessitation necessaryTruthArena making :=
    TruthCore.Results.Causality.RootClosure.necessaryFactAnyMaker
      necessaryTruthArena true false selected hEffect hNecessary (hNecessary true trivial)
  have hSourceMaking : Sound necessaryTruthArena sourceMaking ∧
      NeedsMakerAt necessaryTruthArena sourceMaking true selected ∧
      MakerNecessitation necessaryTruthArena sourceMaking :=
    TruthCore.Results.Causality.RootClosure.necessaryFactAnyMaker
      necessaryTruthArena true true selected hSource hNecessary (hNecessary true trivial)
  refine ⟨hNecessary, ?_, ?_, hEffectMaking, hSourceMaking⟩
  · dsimp [ContingentAt, necessaryTruthArena, mk, selected, MakerControl.Fact]
    decide
  · intro v _
    exact Or.inl rfl

end Makers

/-- Populated contingency controls, every premise omission, and two allowed
maker assignments for the SAME necessary fact. The latter applies the existing
necessary-fact theorem instead of claiming a new truthmaker discriminator. -/
theorem makerControls : MakerControl.Certificate := by
  refine ⟨?_, Makers.positive, ?_, ?_, ?_, Makers.necessaryAlternatives⟩
  · intro present rankTrue
    constructor
    · intro v b
      cases b <;> simp [MakerControl.mk, MakerControl.selected]
    · intro v
      exact Or.inl rfl
  all_goals
    dsimp [MakerControl.OmitImmanence, MakerControl.OmitNecessitation,
      MakerControl.OmitFactContingency, WorldImmanent, MakerNecessitation,
      EveryMakerContingentAt, Contingent,
      TruthCore.German.Kant.CosmologicalInference.ContingentAt, Access,
      MakerControl.absentMakerArena, MakerControl.necessaryBearerArena,
      MakerControl.everywhereArena, MakerControl.mk, MakerControl.making,
      MakerControl.selected, MakerControl.Fact]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | decide | simp [and_imp]

end TruthCore.Results.Causality.ImitabilityGrounding
