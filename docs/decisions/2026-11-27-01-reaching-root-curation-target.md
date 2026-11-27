---
date: 2026-11-27
where: "owner decision, 2026-11-27 (#2103)"
---
**Verified Results Must Reach The Root, Be Placed Or Be Planned.** The first
curation pass (#2084–#2097) aimed at the wrong target. `truth connectivity
--base` and the curation counted membership in the root's *undirected* typed
component, where any typed edge counts: shared generic premises such as
excluded middle, `tests` links and relations of every predicate. On `main`
about 3,960 statements were in that component, but only about 1,100 reached
the root by directed argument paths. The fusion cosmological route (hub
statement `c778a6ca`, about 20 verified derivations) and all 32
`TruthCore/Mereology/` results passed the gate while reaching nothing. The
owner approved a stronger target: every verified result is in exactly one of
five states, tried in this order.

1. **Reaching:** its argument's conclusion reaches the root by the route-aware
   walk (`frontier` `reaching_root_statements`), or the argument supports a
   verified refutation of a recorded rival of a root-path statement (the
   `orphans` "connected" notion, unchanged).
2. **Placed diagnostic:** a premise-free result (control, model, countermodel
   or consistency check) whose result or argument is the subject of a `tests`
   relation whose object is a root-path statement or an argument concluding
   one.
3. **Placed rival:** its conclusion is a typed rival of a root-path statement:
   `alternative_to` or `attacks` between the conclusion and a root-path
   statement (either direction), its argument `attacks` or `refutes` a
   root-path statement, or an argument concluding a root-path statement
   `refutes` the conclusion.
4. **Planned:** the conclusion carries a valid `connection_plan` (the shape
   `truth check` requires) whose target is a root-path statement.
5. **Unplaced:** anything else.

A root-path statement is one in state 1's sense: it reaches the root or
supports a verified refutation of a recorded rival of one. Transcriptions
(invariant 16) are counted separately; their state is computed like any
other, although a transcription does not make a path real. `truth orphans`
reports the states (`--all` lists every disconnected result with its state;
by default only unplaced ones), and `truth orphans --base REV --gate` fails
when a result that is new since the base, whose argument changed, or that was
placed at the base, is unplaced at the head. Pre-existing unplaced results are
backlog: reported, never failed. Both revisions are judged by the running
binary's rules ("head rules on base data"). The honest ways to pass are a real
derivation to a root-path node, a `tests` link for a diagnostic, a typed rival
relation, or a `connection_plan` naming the exact missing bridge. Contrived
edges and tautological bridges are not acceptable; reviewers check the meaning
of every new edge. `truth connectivity --base` stays: it judges statements,
including source readings and premises that no result concludes, which this
gate does not cover. Placement is navigation, not warrant: it closes,
supports and attacks nothing, and frontier closure is unchanged. At adoption
the backlog on `main` was 1,507 unplaced of 2,731 verified results (931
reaching, 251 placed diagnostics, 36 placed rivals, 6 planned); 254 of the
unplaced were transcriptions. The contract is in `docs/corpus-model.md`,
"Connection plans", and `truth/README.md`, "`orphans`".
