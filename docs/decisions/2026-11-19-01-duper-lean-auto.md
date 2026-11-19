---
date: 2026-11-19
where: "owner decision, 2026-11-19 (#1784, invariant 14)"
---
**Duper and lean-auto Are Approved Lean Dependencies.** Invariant 14 admits
Mathlib for mathematics and requires an owner decision for any other Lean
dependency. For the automated frontier-expansion engine (#1784) the owner chose
"Duper + lean-auto": Duper (`leanprover-community/duper`, tag `v4.35.0`) is
required in `lakefile.toml` and brings lean-auto (`v4.35.0`); both match the
pinned Lean v4.35.0, and the Batteries revision Duper requires is the one
Mathlib already pins, so Mathlib's pin did not move. Duper is a superposition
prover that reconstructs a Lean proof term; the kernel checks it. Proofs
reconstructed by Duper use exactly `propext`, `Classical.choice` and
`Quot.sound`, so a result whose Solution imports Duper may permit those three
and no other axiom, as a Mathlib result may (`docs/axiom-policy.md`). lean-auto's
paths that close a goal without reconstruction (`auto.tptp.trust`, SMT without a
checked proof, native evaluation) are not proofs here: an external prover such
as Zipperposition may only select premises or give hints, and Duper must
reconstruct the proof. `truth discover` (`docs/discover.md`) checks every proof's
axioms. Measured on this machine: Duper ships a release build that Lake
downloads; lean-auto and the Batteries shared library compile in about 13 s
wall (75 s CPU); the two packages take about 0.8 GB under `.lake/packages`.
Nothing in `TruthCore` imports Duper yet, so the library build is unchanged.
