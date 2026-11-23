---
date: 2026-11-23
where: "owner direction, 2026-11-23"
---
**Recurring semantic defects checklist.** Over one session, independent semantic challenges reviewed a dozen research batches (#1880–#1897). Most first reviews found P1 findings, and they fell into seven recurring kinds:

- models read as refutations or as interpretations of a metaphysics;
- an asymmetric burden between rival accounts;
- citations read beyond their words, including premises the author declines;
- prose wider than the Lean type;
- undisclosed encoding artifacts (rigidity, vacuous or emptied relations);
- owner commitment labels reused across notes;
- stale "pending" process state, including a PR body that described a different PR.

Automated `@codex review` passes returned "no major issues" on PRs of the same kind, so they did not catch these.

At the owner's request:

- These kinds became a pre-push checklist in the systematic loop. Research worker briefs and the PR template reference it.
- An automated review does not replace the independent semantic challenge for research PRs.
- A repair adds new formal content only when a finding asks for it, and it reports any such addition for re-check.
- A research thread does not leave a draft without that challenge, or without a handoff naming it as pending.

Proof, binding, source and closure rules are unchanged. The checklist is in `docs/systematic-corpus-loop.md`, "Recurring semantic defects (pre-push checklist)".
