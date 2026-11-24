# Omission countermodel finder

An omission countermodel for premise k of a theorem
`thm (carriers) (predicates) (functions) (h₁ : P₁) … (hₙ : Pₙ) : C` is a finite
interpretation in which every Pᵢ with i ≠ k holds and C fails. It shows that the
remaining premises do not entail C under the encoded vocabulary. Workers used to
write these models and their `Control.Certificate` proofs by hand.
`truth countermodel` (the Rust CLI, `truth/README.md`) searches for them.

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
`ComponentFirstness` (`TruthCore/Results/Causality/*/Solution.lean`). The
solver's unit tests and golden replays (`truth/src/countermodel/tests.rs`,
recorded skeletons in `truth/src/testdata/countermodel/`) run offline in the
`truth-cli` job. `scripts/test_countermodel_lean.py` exercises the actual Lean
extractor on explicit nested functions and unsupported implicit inputs, binary
functions, function equality and structure parameters; the existing Python
suite discovers it and metadata-only jobs skip Lean execution.
For function-free skeletons, the search order is the one the retired
`scripts/countermodel.py` used, so models it found and that Lean files cite
are found again.
