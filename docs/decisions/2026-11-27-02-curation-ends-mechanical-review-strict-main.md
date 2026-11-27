---
date: 2026-11-27
where: "owner decision, 2026-11-27 (#2103)"
---
**Curation Ends As The Main Activity; Recurring Review Defects Become
Mechanical; Main Requires Up-To-Date Branches.** Three owner decisions close
curation pass 2 under #2103.

1. **Research pivots from placement to warrant.** Curation pass 2 is no longer
   the main activity. The placement gate of
   `2026-11-27-01-reaching-root-curation-target.md` stays in force for new and
   changed results. Research turns to the warrant of the shared bottleneck
   premises on the God-existence routes. Placement and "reaching the root" are
   plumbing, not warrant. In #2156, 3 of 11 newly reaching results rested on
   real new derivations; the rest reached through loop-backs, rule (d)
   closures through transcriptions, or bare-premise strength registrations.
   `truth orphans` and the gate now report this provenance for every reaching
   result (docs/corpus-model.md, "Result placement"). Progress reports keep the
   four standings of AGENTS.md apart.
2. **Recurring review defects become mechanical where they can be precise.**
   Independent reviews of about 25 curation PRs repeated the same findings,
   usually one or two review rounds per PR. They are now tooling:
   - placement provenance;
   - a warning on new undeclared heuristic transcriptions;
   - `truth type-lints`, which warns on whole-argument `tests` that do not
     certify a registered logical premise and on definition links that the
     bound Lean type does not reach;
   - typed contact for strength records in `truth connectivity`;
   - preflight checks of batch specs on the merge with `origin/main` and of
     the bundle-audit tests.
   
   A false positive that blocks honest work is worse than a missed lint, so a
   heuristic check stays a warning. Each such check reports its
   false-positive rate on the corpus when it is introduced.
3. **Main's required status checks are strict.** A branch must be up to date
   with `main` to merge. GitHub's merge queue is not available for this
   user-owned repository. Workers merge `origin/main` into their branch before
   the final push, as AGENTS.md "Lanes and shared files" already requires, and
   expect CI to rerun after each update of a PR branch.
