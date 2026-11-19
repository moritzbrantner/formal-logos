---
date: 2026-11-19
where: "owner approval on #1784, 2026-11-19"
---
**Parameter Sense Tags And Shared Frames.** An automated prover over the
corpus (`truth discover`, #1784) cannot compose propositions across modules:
each module declares its key relations as its own parameters
(`ConcurrentActualization` quantifies over `G.GivesAt`, `Round2Grounding` over
a `CausesIn` binder), so to the prover they are unrelated symbols even where
the definitions say they express the same sense. The owner approved three
measures. (1) **Parameter-level sense tags**: a sense record may list, under
`senses[].lean_parameters`, the binders of particular declarations that express
it, optionally applied to fixed arguments. Tags are authored after reading the
declaration's doc comment and the sense's definition, never inferred from
names; an untagged parameter is unknown. `truth check` validates them offline,
and one triple is never tagged with two senses of one term. (2) **Shared frames
for new work**: new modules in a concept family take the family's shared frame
structure (carriers and primitive relations, each field a stated primitive) as
input instead of declaring fresh parameters; senses remain distinct
declarations, so equivocation stays a type error, and bridges between fields
remain explicit premises. Older modules receive adapters gradually, with no
rewrite. (3) **A missing-bridge report** from the prover, owned by the prover
work. None of these identifies two relations, proves a bridge or changes a
binding, proof or closure rule. See `docs/corpus-model.md`, "Sense-indexed
terms".
