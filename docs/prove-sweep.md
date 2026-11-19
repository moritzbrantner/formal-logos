# Proof-discovery sweep

`truth prove-sweep` cheaply checks whether a fixed tactic portfolio already
proves a frozen Challenge theorem (a `theorem … := by sorry` in a
`Challenge.lean`). It also flags goals that a single premise application
closes. It is advisory and writes no corpus record. A closed goal still needs
a real Solution, Comparator and the usual gates. A failure is `unresolved`,
never a refutation (AGENTS.md, "Proof-seeking stance").

```bash
flock /tmp/moenarch/truth-core-heavy.lock target/release/truth prove-sweep
target/release/truth prove-sweep --module TruthCore.Results.Causality --theorem pureActLives
target/release/truth --json prove-sweep --heartbeats 50000 --batch 20
```

## How it works

1. Every `Challenge.lean` under `TruthCore/` is read. `--module` keeps the
   Challenge modules equal to or under a prefix. `--theorem` keeps the theorems
   whose full name equals the given name or ends with `.NAME`. Both flags can be
   repeated. Lake first builds the modules the Challenges import.
2. For each target, a generated scratch file restates the statement once per
   portfolio tactic, in the Challenge's own namespace and `open` context. The
   file imports the Challenge's imports plus `Mathlib.Tactic.Tauto` and `Aesop`.
   The tactics are tried in this order: `decide`, `omega`, `tauto`, `simp_all`,
   `aesop`, `grind`, then `intros; prove_sweep_unfold; grind` and
   `intros; prove_sweep_unfold; aesop`. `prove_sweep_unfold` delta-unfolds the
   project (`TruthCore.*`) definitions in the goal and hypotheses until none is
   left, at most eight rounds. Each copy is a separate declaration under
   `set_option maxHeartbeats N in` (`--heartbeats`, default 20000, a tenth of
   Lean's default). A timeout or failure therefore affects only that copy.
3. A transcription probe and a `sorry` control follow each target. The probe
   closes the goal by `assumption`, or by applying one hypothesis and closing
   what remains with `assumption`, `rfl`, `True.intro` or one `constructor`
   split. The control must elaborate with only a `sorry` warning. A control
   error marks the statement as an `error`, and a control that never reports
   shows that Lean did not get that far.
4. One `lake env lean --json` run elaborates `--batch` Challenges at once
   (default 40), each wrapped in a `section`. Messages are mapped back to the
   copies by line. When an error falls outside every copy, or a control fails,
   that Challenge is run again on its own, so one broken Challenge does not
   spoil its batch.

Per target the report gives `closed` (with `closed_by`, the first portfolio
tactic that succeeded, or `premise-application` when only the probe did),
`unresolved` or `error`. Targets that the probe closes are flagged as
`likely_transcription`, with how the probe closed them. Invariant 16 then
applies: such a proof only transcribes "therefore" unless the structure is
formalized. `--json` adds the portfolio, the heartbeat budget and summary
counts per tactic.

## Boundaries

- Advisory only. The sweep proves nothing about the corpus. Its proofs are
  never kept, and a portfolio closure may use axioms (`Classical.choice`)
  that a Solution must not use.
- `unresolved` means only that this portfolio found no proof within the
  budget.
- The probe is a heuristic for invariant 16, not the transcription rule. It
  can flag a legitimate one-step instantiation, and it misses transcriptions
  hidden behind several applications.
- Challenge text is parsed lexically (comments and strings masked). A
  theorem whose proof is not exactly `sorry`, an attribute on its own line, or
  an `open … in` prefix is skipped or reported as an `error`.
- The registered next-test statements are not swept yet; only Challenges are.
- Run it under the heavy-job lock (docs/worker-startup.md). A whole-library
  run imports most of the library and elaborates every Challenge about ten
  times.
