# Proposition discovery index

The primary research entry point is:

```bash
target/release/truth related STMT-Q11-GOD-SUPPOSITUM-IS-NATURE --limit 10
```

It ranks the loaded corpus in memory and needs no index; it performs no Lean
preparation or verification. Add `--json` for complete machine-readable
evidence. (`python3 scripts/corpus.py related` gives the same ranking from
Python's SQLite projection until #954 R2.)

`related` returns propositions with explicit reasons and corpus paths. It ranks
recorded argument connections first (small premise bundles before broad root
arguments), recorded statement-to-statement relations next, shared definitions,
disambiguations and Lean declarations/namespaces next, and weighted paraphrase
word overlap last. Namespace matches indicate proximity, not parsed shared
predicates. Text weights reduce the influence of ubiquitous words; no embeddings
or external service are used.

Argument reasons preserve the complete premise bundle, conclusion, theorem and
recorded result status. A joint premise is never presented as a consequence, and
one member of a bundle is never presented as sufficient for its conclusion.
Known falsity-concluding bundles label their other premises as incompatible
bundle members. This does not select which premise to reject. Directly linked
prior attempts are returned with outcomes and blockers to help avoid repeating
failed investigations. The text output displays up to three reasons per match, with the full reason
count; `--json` retains every reason for each returned match. Increase the
statement limit to inspect more neighbors.

These are discovery rankings, not certified equivalence, strength or entailment.
No cross-profile composition is performed. Source passage coverage remains a
supporting feature, not the primary progress measure.

The JSON corpus remains authoritative. `truth index` (#954 slice B7) keeps a
local SQLite/FTS5 projection of every `corpus/**/*.json` file in
`.cache/truth-index.sqlite` (rusqlite with its bundled SQLite, FTS5 enabled).
No service, proof-status registry or Lean preparation is needed. It does not
change philosophical premises or frontier closure.

```bash
target/release/truth index build
target/release/truth index search 'common nature'
target/release/truth index show STMT-GOD-IS-ONE
target/release/truth index show results:<RESULT-UUID>
target/release/truth index duplicates
target/release/truth index summary
target/release/truth index bundle --case CONFIG-MEGARIAN-CAPACITY-MOTION --premise STMT-MEGARIAN-ABILITY-ONLY-WHEN-ACTING
target/release/truth index compare --case CONFIG-MEGARIAN-CAPACITY-MOTION --left STMT-MEGARIAN-ABILITY-ONLY-WHEN-ACTING --right STMT-SOMETHING-IS-MOVED-IN-THIS-WORLD
```

The index is bound to an FNV-1a digest of every indexed path and byte string
(the hash behind `input_identity`) and to the builder version. Every query
reuses a fresh index and otherwise rebuilds it first; `build` rebuilds
unconditionally. Output is JSON (indented; compact with `--json`). Errors exit
1 and usage errors 2.

The Python implementation, `scripts/research_index.py` (same subcommands plus
`related`, which `truth related` replaces), stays until #954 R2. It writes
`.cache/research-index.sqlite`, and its query commands reject a stale index
instead of rebuilding. The two databases have the same tables and rows; only
the digest differs. `scripts/truth_parity/index.py` compares every table row for
row, and every query's JSON, on the real corpus and on fixtures. Both sides run
the same FTS5 `bm25` over rows inserted in the same order, so search results
match exactly, ties included. Rust additionally resolves a legacy id or label
(optionally `kind:`-prefixed) in `show`, `--case`, `--premise`, `--left` and
`--right`; Python accepts only indexed IDs.

Search treats input as literal words joined by AND and returns corpus paths.
`show` returns the full record and reverse references, including relevant
attempts when linked by ID. Keys are namespaced by record kind (`kind:ID`), and
an ID that names several records needs that form.
Reverse references are discovery aids: they are not themselves logical edges.

`duplicates` groups exact premise-ID sets with the same conclusion ID. These
are review candidates, not established redundancy: interpretations, commitments
and inference structure can differ. It does not merge statements, identify all
logical equivalents or guarantee that no discovery is repeated.

`bundle` reuses the existing configuration engine in **registered-only** mode.
It exposes applicable registered implications, incompatible subsets and model
references within one existing semantic profile. It refuses propositions outside
that profile. `compare` reuses the existing bounded implication-support search in
both directions, with premise supports and result links. These are candidate
paths, not newly certified compositions. A missing path is unresolved, not
non-entailment, strict strength or compatibility. No cross-profile inference is
performed and no profile is invented for the simplicity–uniqueness cluster.

For actual certification, use the existing gates:

```bash
target/release/truth configurations --registered --case CONFIG-MEGARIAN-CAPACITY-MOTION
python3 scripts/corpus.py configurations --case CONFIG-MEGARIAN-CAPACITY-MOTION
python3 scripts/corpus.py configuration-report --help
```

Reuse existing fresh verification evidence where available. This index never
upgrades `solution-present` into verified. Inventory counts are not discovery
counts. Publication is atomic and a failed rebuild preserves the old database
(the query then fails with exit 1). The database is disposable and ignored by
Git.

Validation: `cargo test -p truth index` and `python3 scripts/verify_truth_cli.py
target/debug/truth TruthIndexParity` (Python's own tests:
`python3 -m unittest discover -s scripts -p test_research_index.py`). Tests
cover namespaced identity, inverse references, exact duplicate bundles, stale
refresh, profile boundaries, uncertified labels, failed rebuild preservation
and corrupt-projection detection. No Lean declaration or proof input is modified by this tooling.

## Parity baseline

`truth index parity` independently compares every corpus
JSON file's exact bytes and every top-level ID record's parsed content against
the SQLite projection. Nested passage collections are projected into individual searchable passage
records, preserving each locator alongside its shared snapshot and collection
notes. Other non-entity files, if present, are listed explicitly and preserved
byte-for-byte. This is storage/record parity,
not complete query or corpus-command parity.

`truth index export corpus/statements/god-is-one.json`
prints the original indexed bytes to stdout, preserving formatting and all
fields. Export does not overwrite the corpus. Source files are retained in the
`source_files` table independently of the searchable record projection.

Next parity work should add typed reference resolution, then compare query outputs with the existing corpus commands. Existing
proof, source, dossier and frontier authorities remain unchanged throughout.

## Research workflow integration

`AGENTS.md` places proposition discovery before new investigations and vocabulary.
The existing configuration-elimination loop uses it at the harvest step, followed
by dossiers, exact theorem inspection and established certification. The local
skill `.agents/skills/proposition-reuse/SKILL.md` supplies the same entry point;
it changes no global skill or agent configuration. No Git hook or proof gate is
installed. Discovery is not run on every commit or every diagnostic request.

For a more selective **cross-argument** investigation, `corpus.py
bridge-experiments <RESULT-ID> --profile-module <LEAN-MODULE>` reads existing
attempt blockers and exact direct Solution imports, preserving complete
argument premise bundles in `--json`. It requires both result conclusions to
be an explicit focus of the same attempt, excluding broad survey citations
that do not describe the selected semantic question. This is a read-only
research-priority aid, **not** an entailment or shared-witness proof; see the
[#953 same-profile pilot and negative controls](cross-argument-experiments-953.md).
