---
name: proposition-reuse
description: Find related truth-core propositions, existing arguments and previous attempts before a philosophical investigation or formalization. Use for corpus research and vocabulary reuse, rather than general repository maintenance.
---

# Proposition reuse

From the truth-core repository root, build the Rust CLI once per clone
(`cargo build --locked --release -p truth`; rebuild after Rust source or Cargo
input changes), then run:

```bash
target/release/truth related <STMT-ID> --limit 10
target/release/truth dossier <STMT-ID>
```

When the seed is an existing argument or result, first run
`target/release/truth context <ARGUMENT-OR-RESULT-ID>` (add `--json` for every
entry); then open dossiers only for the premises it reports open.

`related` ranks the loaded corpus in memory; it needs and writes no cache.
Use `--json` for complete machine-readable match evidence and attempt blockers.
If no seed ID is known, start with
`target/release/truth index search 'topic words'` and read a hit with
`target/release/truth index show <ID>`. The index is a disposable SQLite/FTS5
projection in `.cache/truth-index.sqlite` of the corpus records and the
`docs/notes/` sections (#952): note hits follow the record hits, and
`index show docs/notes/<note>.md` lists the records a note names. Each query
reuses the index while it matches the corpus and notes, and rebuilds it
otherwise.

Before judging how mature a premise's research is, or calling a theorem or
connection new, run:

```bash
target/release/truth brief <STMT-ID>          # or: brief --question "..."
target/release/truth novelty "<claim>"        # or: novelty --statement <STMT-ID>
```

Add `--issues-from FILE` with an offline `gh issue list`/`gh pr list --state all
--json number,title,body,url,state,comments,updatedAt` snapshot where available. Both are
advisory: a missing hit or snapshot is not evidence that no prior work exists.

Before proposing a derivation or reusing a proposition in a new argument,
resolve its meanings and check sense compatibility:

```bash
target/release/truth semantics <STMT-OR-ARGUMENT-ID>
target/release/truth semantics --premise <P1> --premise <P2> --conclusion <C> [--definition <DEF>] [--bridge <S>@SENSE,SENSE]
```

The first lists the definitions (with formal status), disambiguations and
senses used, and a per-term verdict for connected arguments, naming the
statement carrying each sense. The preflight judges the candidate as
`truth check` judges a new argument: split an unbridged mixing per sense, or
bridge it with an explicit `sense_bridges` premise, before formalizing.

Inspect the smallest relevant argument bundles, their exact Lean declarations,
and prior attempts before proposing another result or new vocabulary. Preserve
all displayed premises: a consequence requiring a bundle is not an implication
from any one member. Shared definitions, namespaces and words suggest research
neighbors; they do not establish equivalence or justify merging statement IDs.

Use the existing configuration commands with an explicit semantic profile for
certification. Neither a recorded result status nor a search ranking is fresh
verification evidence. Keep dossier/frontier authorities and existing rules for
persisting substantive attempts; this skill adds no new proof gate or tracker.

See `docs/notes/research-index.md` for index queries and limits, and
`docs/configuration-elimination-loop.md` for the certified investigation loop.
