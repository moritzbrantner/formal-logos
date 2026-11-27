---
date: 2026-11-27
where: "owner decision, 2026-11-27 (#2103)"
---
**Curation Ends As The Main Activity; Recurring Review Defects Become
Mechanical; Main Requires Up-To-Date Branches.** Three owner decisions close
curation pass 2 under #2103.

First, research pivots from placement to warrant. Curation pass 2 is no longer
the main activity. The placement gate of
`2026-11-27-01-reaching-root-curation-target.md` stays in force for new and
changed results, and research turns to the warrant of the shared bottleneck
premises on the God-existence routes. Placement and "reaching the root" are
plumbing, not warrant. `truth orphans` and the gate therefore report a
provenance for every reaching result (docs/corpus-model.md, "Result
placement"). Measured against the squash base of #2156, 18 results newly
reached the root, but only one of them (`dedd529a`) through a substantive
derivation.

Progress reports keep four standings apart, and each provenance key maps to
one of them. *Established* covers the frontier's established statements.
*Conditionally supported by a substantive derivation* covers `substantive`;
`refutation_support` counts here only as support for that refutation of a
recorded rival. *Connected only* covers the rest: `transcription_closed`
carries rule (d) closure but no independent warrant, `transcription_self`
contributes at most rule (d) closure, and `transcription_open`, `loop_back`,
`registration_bare` and `unverified_route` carry no support to the root.
*Planned* covers the placement state `planned`.

Second, recurring review defects become mechanical where a check can be
precise. Independent reviews of about 25 curation PRs repeated the same
findings, usually at a cost of one or two review rounds per PR. They are now
tooling: placement provenance; a warning on new undeclared heuristic
transcriptions; `truth type-lints`, which warns on whole-argument `tests` that
do not certify a registered logical premise and on definition links that the
bound Lean type does not reach; typed contact for strength records in `truth
connectivity`; and preflight checks of batch specs on the merge with
`origin/main` and of the bundle-audit tests. A false positive that blocks
honest work is worse than a missed lint, so a heuristic check stays a
warning, and each such check reports its false-positive rate on the corpus
when it is introduced.

Third, main's required status checks are strict: a branch must be up to date
with `main` to merge. GitHub's merge queue is not available for this
user-owned repository. Workers merge `origin/main` into their branch before
the final push, as AGENTS.md "Lanes and shared files" already requires, and
expect CI to rerun after each update of a PR branch.
