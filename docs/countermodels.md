# Omission countermodel finder

An omission countermodel for premise k of a theorem
`thm (carriers) (predicates) (functions) (h₁ : P₁) … (hₙ : Pₙ) : C` is a finite
interpretation in which every Pᵢ with i ≠ k holds and C fails. It shows that the
remaining premises do not entail C under the encoded vocabulary. Workers used to
write these models and their `Control.Certificate` proofs by hand.
`truth countermodel` (the Rust CLI, `truth/README.md`) searches for them. [Original PR #1204](https://github.com/moritzbrantner/formal-logos/pull/1204)

```bash
target/release/truth countermodel TruthCore.Results.Causality.SelfOperationLife.pureActLives
target/release/truth countermodel THEOREM --omit hLife      # by binder name or 1-based position
target/release/truth countermodel THEOREM --all --size 3    # every premise plus a joint witness
target/release/truth --json countermodel THEOREM --no-check
target/release/truth countermodel THEOREM --module TruthCore.X.Solution   # skip locating the module
```

## How it works

1. `scripts/Countermodel.lean` (run with `lake env lean --run`) opens the
   elaborated theorem type. It sorts the binders into carriers (`B : Type`,
   `Sort u`), predicate parameters (into `Prop`, over carriers or over
   carrier predicates `T → Prop`), element constants (`esse : R`), total
   nondependent unary functions with explicit inputs (`f : A → B`, where both
   carriers are already declared), and premises.
   It unfolds each premise and the conclusion through their definitions into
   `∀ ∃ ∧ ∨ ¬ → ↔ = ≠ True False` over predicate atoms. A quantifier over `Prop`,
   as in `ExcludedMiddle`, ranges over the two truth values. Fully applied and
   nested function terms, such as `g (f x)`, retain their function names and
   declared domain and codomain carriers.
2. The finder grounds these formulas over `Fin m` carriers (smallest total size
   first, each carrier from 1 up to `--size`, default 2) and every choice of the
   element constants. For each choice it lazily enumerates total function
   tables, with exactly one codomain element for every domain element. All
   occurrences of a function use the same table, including nested applications.
   It encodes the resulting target in CNF and solves it with a small
   DPLL solver, preferring false atoms, so the models are sparse. A
   predicate-of-predicates argument (`Possible (fun t => ¬ IsAt x t)`) is
   matched against every concrete subset. The found model is evaluated again
   directly before it is reported.
3. The model, including typed functions, is rendered as Lean `abbrev`s and a
   `certificate` theorem
   `¬ Pₖ ∧ P₁ ∧ … ∧ ¬ C`, proved by `delta <unfolded definitions>; decide`.
   A premise quantified over `Prop` is closed by `Classical.em`. Unless
   `--no-check` is given, Lean checks every certificate. Statuses: `lean-checked`,
   `lean-rejected` (with the Lean output), `candidate` (not checked) or
   `unresolved`. `--all` adds a joint witness in which every premise and the
   conclusion hold.

A checked certificate can be pasted into a `Control` namespace, renamed and
cited from the result's `controls` theorem. Copy the statement, not just the
model: the certificate's Lean check is the evidence, not the solver.

The companion `truth prove-sweep` ([prove sweep](prove-sweep.md)) runs a fixed
tactic portfolio on the frozen Challenge theorems: it searches for proofs where
this tool searches for countermodels.

## Boundaries

- The solver proposes; Lean decides. An unchecked candidate is not evidence.
- `unresolved` means that the completed search found no model within the encoded
  size bound. Unsupported vocabulary and function-table dimension or cardinality
  overflow are errors, not `unresolved` results. A bounded negative result does
  not show that the premise is needed. When the omitted premise itself holds in
  every model within the bounds (for example excluded middle), the report says
  so: no omission model of this kind can exist there.
- A countermodel is relative to the formal vocabulary. It says nothing about
  whether the interpretation is metaphysically possible or about other readings
  of the premises.
- The joint witness is the first model found. It may be trivial, for example
  with every antecedent empty. A certificate that needs a nontrivial witness
  (such as `comp false true` in `ComponentFirstness`) still needs a hand-added
  conjunct.
- Unary carrier functions must have an explicit input binder. Implicit,
  strict-implicit and instance inputs are unsupported: their binder metadata
  is not retained by the certificate renderer. Also unsupported are dependent
  functions, functions with multiple inputs, functions taking or returning
  functions, partially applied function terms, and function equality.
- Other unsupported vocabulary: structure-bundled parameters (`M.MovedIn`),
  concrete carriers in the theorem (`Nat`, `Bool`), typeclass arguments,
  quantifiers over predicates other than `Prop`, and definitions that unfold
  outside the fragment. Unary function support does not unpack shared frames
  or identify separately declared carriers or function parameters.
- The solver is exhaustive over the bound and has no symmetry breaking. A size 3
  search over ternary relations can be slow. At fixed carrier sizes, a function
  `A → B` contributes `|B|^|A|` interpretations; multiple functions multiply
  these counts. Lazy enumeration avoids storing all interpretations at once,
  but does not remove this search cost.

## Rediscovered examples

CI (the `corpus-and-lean` job, after `lake build`) has `truth countermodel
--all` rediscover and Lean-check the omission models and joint witnesses of
`SelfOperationLife`, `PerfectionOfBeing`, `NecessaryBeingInAct` and
`ComponentFirstness` (`TruthCore/Results/Causality/*/Solution.lean`), plus
`AssertionRetorsion.existenceFromOccurrence` in its separately specified
`TruthCore.Results.Logic.AssertionRetorsion.Solution` module. The
solver's unit tests and golden replays (`truth/src/countermodel/tests.rs`,
recorded skeletons in `truth/src/testdata/countermodel/`) run offline in the
`truth-cli` job. `scripts/test_countermodel_lean.py` exercises the actual Lean
extractor on explicit nested functions and unsupported implicit inputs, binary
functions, function equality and structure parameters; the existing Python
suite discovers it and metadata-only jobs skip Lean execution.
For function-free skeletons, the search order is the one the retired
`scripts/countermodel.py` used, so models it found and that Lean files cite
are found again.

### Unary-function coverage checked on 2026-11-24

The baseline extractor stopped at `represent : Episode → Being` when asked
for an omission model of
[`existenceFromOccurrence`](../TruthCore/Results/Logic/AssertionRetorsion/Solution.lean).
That was an unsupported parameter, not a completed negative model search.
The explicit unary-function extension supersedes that refusal for this case;
the other unsupported fragments listed above remain outside its coverage.

Reproduce through the existing CLI:

```bash
target/release/truth --json countermodel \
  TruthCore.Results.Logic.AssertionRetorsion.existenceFromOccurrence \
  --module TruthCore.Results.Logic.AssertionRetorsion.Solution --all --size 2
```

The actual run produced exactly three `lean-checked` reports. Each uses
`Episode = Fin 1`, `Being = Fin 1` and `represent := fun _ => 0`:

| Report | `Occurs` | `ExistsIn` | Checked conjunction |
| --- | --- | --- | --- |
| Omit `hOccurs` | Always false | Always false | Occurrence fails; the representation bridge holds vacuously; the conclusion fails |
| Omit `hRepresents` | Always true | Always false | Occurrence holds; the representation bridge and conclusion fail |
| Joint witness | Always true | Always true | Both premises and the conclusion hold |

The `hRepresents` report recovers the existing
[`OccurrenceWithoutExistenceControl`](../TruthCore/Logic/AssertionRetorsion.lean),
already proved by `AssertionRetorsion.controls`. Occurrence alone does not
entail `SomeExistent ExistsIn` in this vocabulary: the representation bridge
is an explicit premise. Membership in the model's `Being` carrier does not
assert `ExistsIn`. The omission models establish those formal non-implications;
they do not make the bridge false or philosophically doubtful. The joint
witness establishes satisfiability of this encoded bundle, without establishing
metaphysical coherence or the actual occurrence or existence of anything.
This is a gain in known-control coverage, with **no novel philosophical
consequence and no change in premise warrant**.

The singleton reports exercise constant function tables. A separate public-API
probe exercised a nonconstant table: no size-1 model satisfies
`∀ x, f x ≠ x` together with `∀ x, f (f x) = x`; size 2 produced the swap
`f = [1, 0]`. The generated certificate used
`fun x => if x = 0 then 1 else 0` and Lean accepted both properties by `decide`.
This checks rendering and reuse of a nested function application; it is a
synthetic implementation control, not a corpus discovery.

Validation also passed all 24 Rust countermodel tests, including eight unary
function tests and the unchanged function-free goldens, and all five durable
Lean extraction tests. The latter accept explicit nested cross-carrier
functions and reject implicit inputs, binary functions, function equality and
structure parameters. The measured change is one demonstrated extraction
refusal becoming three checked reports; it is not a general performance or
agent-effort comparison.
