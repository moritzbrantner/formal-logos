module

public import TruthCore.Results.Causality.NarDerivation.Solution
public import TruthCore.Results.Modal.OptimalCreationChoice.Solution

/-!
# Grafting the optimal-creation controls onto the WN rival (#1926 orphan grafts)

Analyst formulations, attribution deferred (logic first). Two verified result
families did not reach the root: #462/#1737's selected-effect and
optimal-creation controls (`TruthCore.Modal.SelectedEffectBridge`,
`TruthCore.Modal.OptimalCreationChoice`, on a world-indexed `OutputProfile`) and
the root-route premise WN of #1947 (`RationalFixedGivingIsRequired`,
`0266eac2`, on #1897's `CausalityFrame`). WN's recorded rivals hold a perfect
will fixed toward effects its end does not require (navigation, not
attributed). This module states a narrow being-level "one best effect" variant
of that rival on the root's giving (closer to *ex uno non fit nisi unum* than
to Rowe's world-level argument, which is not represented), records the
standing selective-diffusion and world-level-optimizer rivals, and connects
the two families through one adapter.

**The adapter (`givingProfile`).** For a being `y` of a `CausalityFrame` `F`,
the `OutputProfile` whose ontology is `F`'s own `Ontic`, whose source is `y`,
whose single act (the `Unit` token) is performed exactly where `y` exists, and
whose outputs at `v` are the beings `y` gives being at `v` (`GivesTo`). It
identifies nothing: `GivesTo` stays #1897's giving, and no causal-edge
realization (`RealizedOutputs`) is asserted, because the frame's `Ontic` causal
field is not tied to giving. Under it, `StableActOutput` is exactly "fixed
toward every being given at `w`" (`stable_iff_fixed`).

**The optimizing rival (`ActualRootsGiveUniqueOptimum`).** Every actual root
of `G` at `w` gives by total optimal output over a fixed candidate set and a
fixed partially ordered quality scale (`OptimalOutputs`: at `w` and every
accessible world where it exists it gives something, and only optimal
candidates), and at most one candidate is optimal. Since every given being is
optimal and at most one is, each root gives being to exactly one being at each
accessible world where it exists; with (b1) and the common root's reach there
is at most one actual concretum besides the root. A being-level "one best
effect" variant: the candidates are beings, not complete worlds or orders of
effects.

Every model is a finite structural surrogate; it witnesses only its formal
interpretation, never metaphysical possibility. See
`docs/notes/orphan-graft-map.md`.
-/

@[expose] public section

namespace TruthCore.Causality.NarGrafts

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.PrussPowerPremises (GivesTo GivenExists)
open TruthCore.Causality.WillVersusChance (AgencyFrame)
open TruthCore.Causality.NarDerivation (FixedTowardAt TwoWayTowardAt
  RationalFixedGivingIsRequired ActualRootsEndRequiresNoOther)
open TruthCore.Modal.SelectedEffectBridge (OutputProfile StableActOutput)
open TruthCore.Modal.OptimalCreationChoice (Optimal OptimalOutputs)

variable {W B T R S P : Type}

/-- The giving-output profile of `y` in `F` (adapter, no new primitive): `F`'s
`Ontic`, source `y`, one act token performed exactly where `y` exists, and as
outputs at `v` the beings `y` gives being at `v`. -/
def givingProfile (F : CausalityFrame W B T R) (y : B) : OutputProfile W B Unit where
  ontic := F.history.ontic
  source := y
  performs := fun v _ => F.history.ontic.ExistsAt v y
  output := fun v _ x => GivesTo F v y x

/-- OPEN rival (a being-level "one best effect" variant): every actual root `n`
of `G` at `w` gives by total optimal output over the fixed candidate set
`feasible` and quality scale `quality` (`OptimalOutputs` on `givingProfile F n`:
at `w` and every accessible world where `n` exists it gives being to something,
and every being it gives is optimal), and at most one candidate is optimal.
Consequently each root gives being to exactly one being, the unique optimal
candidate, at each accessible world where it exists; with (b1) and the common
root's reach there is at most one actual concretum besides the root. Closer to
*ex uno non fit nisi unum* than to Rowe's world-level argument, which is not
represented. It does not say why the root optimizes. Without direct reach it
is satisfiable by a mediated creator (#1947's `chainG`, candidates `{g}`). -/
def ActualRootsGiveUniqueOptimum (F : CausalityFrame W B T R) (concrete : B → Prop)
    (G : W → B → B → Prop) (w : W) (V : Type) [PartialOrder V] (feasible : Set B)
    (quality : B → V) : Prop :=
  ∀ n, ActualRoot (groundProfile F concrete G) w n →
    OptimalOutputs (givingProfile F n) w () feasible quality ∧
      ∀ x y, Optimal feasible quality x → Optimal feasible quality y → x = y

/-- The denial of the optimizing rival, the conclusion of its refutation. -/
def NotEveryActualRootGivesUniqueOptimum (F : CausalityFrame W B T R) (concrete : B → Prop)
    (G : W → B → B → Prop) (w : W) (V : Type) [PartialOrder V] (feasible : Set B)
    (quality : B → V) : Prop :=
  ¬ ActualRootsGiveUniqueOptimum F concrete G w V feasible quality

/-- OPEN standing rival (selective necessary diffusion at the root): some
actual root `n` of `G` at `w` exercises a rational power `p` toward a being `x`
other than itself, is fixed (NECESSITATE_5) toward `x`, and `x` is not
required by `n`'s own end (`EndRequires`, the means-to-end relation), while `n`
is two-way toward some being `c`. A perfect will fixed toward an effect its
good does not require, selectively: the necessary diffusion of the good toward
a necessary intermediary (Plotinus; Avicenna's First as standardly reported;
Kretzmann; navigation, not attributed), with free giving of the contingents.
Stated only; no argument here supports or refutes it. #1947's `MixedModeRoot`
model is of this shape. It is the denial of WN at one root, together with a
two-way effect. -/
def SelectiveNecessaryDiffusionAtRoot (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (concrete : B → Prop) (G : W → B → B → Prop) (EndRequires : B → B → Prop) (w : W) :
    Prop :=
  ∃ n p x c, ActualRoot (groundProfile F concrete G) w n ∧ x ≠ n ∧ A.PowerOf n p ∧
    A.Rational p ∧ A.Exercises w n x p ∧ FixedTowardAt F w n x ∧ ¬ EndRequires n x ∧
    TwoWayTowardAt F w n c

/-- OPEN standing rival (the world-level optimizer, ties allowed): every actual
root `n` of `G` at `w`, at `w` and at every accessible world where it exists,
gives being to exactly the beings of some optimal complete output: the set
`{x | GivesTo F v n x}` is an optimal candidate among the fixed admissible sets
`feasible` under the fixed quality `quality`. Candidates are complete outputs,
not single beings. With several optimal complete outputs that all contain a
necessary intermediary, the root would be fixed toward it and free toward the
rest (not proved here). Closer to Rowe's and Leibniz's best-world framing than
the being-level variant; stated only, neither supported nor refuted here. -/
def ActualRootsGiveOptimalCompleteOutputs (F : CausalityFrame W B T R) (concrete : B → Prop)
    (G : W → B → B → Prop) (w : W) (V : Type) [PartialOrder V] (feasible : Set (Set B))
    (quality : Set B → V) : Prop :=
  ∀ n, ActualRoot (groundProfile F concrete G) w n →
    ∀ v, (v = w ∨ F.history.ontic.frame.access w v) → F.history.ontic.ExistsAt v n →
      Optimal feasible quality {x | GivesTo F v n x}

/-! ## Laws and a tied-optimum model -/

namespace Model

open TruthCore.Causality.HolderRootIdentification.Model (gGroundsOthers)
open TruthCore.Modal.PrussPowerPremises.Model (Bg gFrame allC uni)
open TruthCore.Causality.HolderRootIdentification.Model (dThereEx)
open TruthCore.Causality.WillVersusChance.Model (onlyG)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)
open TruthCore.Causality.NarDerivation (ActualRootsGiveGroundedHere ActualRootsNecessary)
open TruthCore.Modal.ModalGrounding (SomeContingentConcreteAt)

/-- `g` gives `c` being at `false` and `d` being at `true`. -/
def tiedGives (v : Bool) (y x : Bg) : Prop := y = .g ∧ ((x = .c ∧ v = false) ∨ (x = .d ∧ v = true))

/-- A root that gives a different contingent at each world (`g` everywhere, `c`
only at `false`, `d` only at `true`; universal access). -/
def tiedG : CausalityFrame Bool Bg Unit Bool := gFrame uni dThereEx tiedGives

/-- Candidates: `c` and `d`; equal quality. -/
def tiedFeasible : Set Bg := {x | x = .c ∨ x = .d}
/-- Constant quality. -/
def tiedQuality (_ : Bg) : Nat := 0

/-- General laws.

1. **Stability is fixity.** Under the adapter, `StableActOutput` of
   `givingProfile F y` at `w` is exactly: `y` is fixed (NECESSITATE_5) toward
   every being it gives at `w` (`FixedTowardAt`).
2. **A unique optimum makes the root fixed toward every effect.** If an actual
   root gives by total optimal output and at most one candidate is optimal, it
   is fixed toward every being it gives at `w`, so it is two-way toward none:
   a unique-optimum root cannot be a mixed-mode root (it gives exactly one
   being per world). Without direct reach it can still be a mediated creator
   that gives only a necessary intermediary.
3. **The optimizing rival is a rival to WN.** With SS, a root that gives by a
   unique optimum and gives some other being `x` at `w` by exercising a
   rational power makes WN fail.

Laws 2 and 3 use #1737's `OptimalChoiceCertificate` (its first conjunct). -/
def Laws : Prop :=
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (y : B),
    (StableActOutput (givingProfile F y) w () ↔ ∀ x, GivesTo F w y x → FixedTowardAt F w y x)) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (concrete : B → Prop)
      (G : W → B → B → Prop) (w : W) (V : Type) [PartialOrder V] (feasible : Set B)
      (quality : B → V),
    ActualRootsGiveUniqueOptimum F concrete G w V feasible quality →
    ∀ n, ActualRoot (groundProfile F concrete G) w n →
      (∀ x, GivesTo F w n x → FixedTowardAt F w n x) ∧ ∀ x, ¬ TwoWayTowardAt F w n x) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
      (concrete : B → Prop) (G : W → B → B → Prop) (EndRequires : B → B → Prop) (w : W)
      (V : Type) [PartialOrder V] (feasible : Set B) (quality : B → V),
    ActualRootsGiveUniqueOptimum F concrete G w V feasible quality →
    ActualRootsEndRequiresNoOther F concrete G EndRequires w →
    (∃ n p x, ActualRoot (groundProfile F concrete G) w n ∧ x ≠ n ∧ A.PowerOf n p ∧
      A.Rational p ∧ A.Exercises w n x p ∧ GivesTo F w n x) →
    ¬ RationalFixedGivingIsRequired F A EndRequires w)

/-- **Tied optimum** (omission of uniqueness from the refutation): on `tiedG`
at `false`, with `g` grounding every other being and `g` the GOD_4 root with
intellect (`onlyG`), the premises the refutation uses besides uniqueness hold:
(b1), factive giving, the common GOD_4 root with intellect, necessary roots and
some concrete contingent being. `g` gives by total optimal output over `{c, d}`
under constant quality, yet two candidates are optimal, `g` is two-way toward
`c`, and the optimizing rival with uniqueness fails. Here the tied root is
two-way toward `c`: #1737's tied control, now on the root's giving. Encoding
disclosures: quality is constant; `G` and existence are fixed by construction;
the frame's `Ontic` causal field and other relations are empty; `d` exists
only at `true`. -/
def TiedOptimum : Prop :=
  ActualRootsGiveGroundedHere tiedG allC gGroundsOthers false ∧
  GivenExists tiedG ∧
  IntellectualGodCommonRootAt (groundProfile tiedG allC gGroundsOthers) false onlyG onlyG ∧
  ActualRootsNecessary tiedG allC gGroundsOthers false ∧
  SomeContingentConcreteAt tiedG allC false ∧
  OptimalOutputs (givingProfile tiedG .g) false () tiedFeasible tiedQuality ∧
  Optimal tiedFeasible tiedQuality .c ∧ Optimal tiedFeasible tiedQuality .d ∧
  TwoWayTowardAt tiedG false .g .c ∧
  ¬ ActualRootsGiveUniqueOptimum tiedG allC gGroundsOthers false Nat tiedFeasible tiedQuality

/-- The certificate: laws and the tied-optimum model. -/
def Controls : Prop := Laws ∧ TiedOptimum

end Model

end TruthCore.Causality.NarGrafts
