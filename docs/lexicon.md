# Lexicon

Owner direction (2026-11-15, #1652): "create the necessary infrastructure for
us to have a proper dictionary or glossary or something alike, so that we can
make sure that every single word we use in prose can be traced and explained."

The lexicon is `corpus/lexicon/`, one JSON record per lemma, checked by
`truth check`. It traces each word in corpus prose to an entry. It also
requires a record that uses a technical word with several senses to link
one of those senses. The schema is in [the corpus model](corpus-model.md#lexicon).

**Boundaries.** A gloss explains how the corpus uses a word. It is neither
evidence nor a source claim. Load-bearing technical terms keep their
`DEF-…`/`DISAMB-…` records under the existing definition and review rules: a
technical entry only points at them. Lexicon status never changes proof,
source or frontier closure.

## What is scanned

| Kind | Fields |
| --- | --- |
| statements | `paraphrase` |
| claims | `interpretation`, `attribution` |
| inferences, arguments | `meaning` |
| results | `description` |
| definitions | `definition`, `note` |
| disambiguations | `resolution` |
| attempts | `summary`, `blocker` |

The list is `lexicon::SCANNED` in `truth/src/lexicon/mod.rs`. Slice L4 extends
it to `docs/notes/` and Lean doc comments.

## Tokens

The tokenizer is deterministic and rule-based (`truth/src/lexicon/tokenize.rs`).
It skips the following, which are not words of prose:

- code spans in backticks and URLs;
- uuids and hex id prefixes (`7a63a3fe`);
- legacy ids (`STMT-CATHOLICISM-TRUE`);
- dotted names and locators (`Profile.grounds`, `q.104`);
- identifiers with an inner capital (`hBridge`, `TruthCore`) or a lowercase
  underscore (`definition_ids`);
- any token containing a digit or other numeric character (`#1590`, `w₀`);
- `#`/`@`/`$`/`\` references;
- single letters other than `a` and `I`.

An upper snake case token with an underscore (`PRIOR_1`, `SIMPLY_PRIOR_1`,
`WELL_FOUNDEDNESS`) is a sense or term tag. It is traced to the disambiguation
whose sense label or `term_label` it is. An unknown tag is reported as
untraced.

A dotted abbreviation (`e.g.`, `i.e.`) is one token. A hyphenated compound is
traced as a whole, or else part by part. Punctuation between two words ends a
multi-word lemma.

## Lemmas

A word resolves through these steps:

1. **Exact match.** The lowercase word is a lemma or an explicit `form` of an
   entry. Explicit forms override every rule. Irregular inflections such as
   `is`, `are` and `was` → `be` are forms.
2. **Lemmatizer candidates.** Otherwise the lemmatizer tries these rules in
   order:
   - possessive `'s`/`s'`;
   - plural `-ies`→`y`, `-s`, `-es`, `-ves`→`f`/`fe`, except after `-ss`,
     `-us` or `-is`;
   - past `-ied`→`y`, `-ed`→`e`/∅ or an undoubled final consonant;
   - participle `-ing`→∅/`e`, an undoubled consonant, or `-ying`→`ie`.

   A candidate counts only when the lexicon has it and it is at least three
   letters long. The rules therefore never invent a lemma: `being` does not
   fall back to `be`.

There are no comparative or `-ly` rules, because they mis-fire (`former` →
`form`, `only` → `on`). Such words need their own entry or a form.

A multi-word technical lemma (`per se`, `existential inertia`) traces each of
its words when they appear in sequence with no punctuation between them. The
last word may be inflected.

## The two rules

1. **Untraced word.** Every token resolves to an entry.
2. **Unlinked sense.** A word that resolves only to technical entries, one of
   which has several senses (two or more definitions, or a disambiguation),
   needs a link to one of those senses from its record. Any of these counts:
   - the record's `definition_ids` or `disambiguation_ids`;
   - those of the statement a claim reads, or the argument a result verifies;
   - for a definition or disambiguation, the record itself;
   - a sense or term tag in the record's label or scanned prose.

   Attempts have no link fields and are exempt from this rule.

A word that also has an `ordinary` or `function` entry is exempt from rule 2.
That entry must state `technical_separation`, saying how the everyday use
differs from the technical senses. This exemption is deliberate and needs
review: add such an entry only when the everyday reading is common and really
separable. The function word `one` is an example. Do not add one merely to
silence the rule for a word such as *necessary* or *being*.

## Ratchet

`corpus/lexicon-allowlist.json` is generated. It grandfathers whole fields.
Each line maps a legacy prose field (`kind/id/field`) to the `fnv1a64` hash of
its text when it was allowlisted. It lists no words (#1652 L1b).

- **An unchanged field is legacy backlog.** While the text hash matches, every
  current finding in the field counts as backlog, never as new. Findings are
  untraced words and unlinked senses, whatever the current lexicon makes of
  them, so the lexicon can grow without creating new violations in old prose.
  For example:
  - a newly traced part of a hyphenated compound (`negation-closure` → `closure`)
    can expose a multi-sense part;
  - a new multi-sense technical entry (*concrete*, *cause*) can turn ordinary
    old uses into unlinked senses.

  `truth check` reports the backlog as one `warning: lexicon: …` summary line,
  with the counts computed live.
- **A new field, or a changed field whose hash no longer matches, must be fully
  traced.** Each finding is reported per field with its count and words. In
  warn mode (below) these are `warning: lexicon: …` lines. In strict mode they
  are a `truth check` error.
- **The allowlist may only shrink, field by field.** CI runs
  `truth lexicon ratchet --base HEAD^1` on pull requests. It fails when a field
  is added or listed again with a different hash. Fields only disappear:
  - when they are fully traced and `truth lexicon allowlist --write` removes
    them;
  - when their text changes. A changed field is never re-listed.

  This mirrors the sense-index allowlist (#1233).
- **Regenerate with `truth lexicon allowlist --write`.** When the file exists,
  regeneration keeps only listed fields with an unchanged hash that still have a
  finding. It seeds the file only when it is absent. Stale entries are harmless,
  and `truth check` counts them as removable. After a merge conflict in the
  file, take either side and rerun the generator. The ratchet reads the older
  schema-1 file (with word lists) for its hashes.
- **Live worklists.** Coverage numbers and the `untraced` worklist are
  computed from the current scan, not from the allowlist.

## Enforcement: warn now, strict later

The owner's decision on #1652 is "warn now, strict later". The switch is
`corpus/lexicon-config.json`:

```json
{"schema_version": 1, "strict": false, "strict_token_coverage": 0.95, "note": "…"}
```

- **`strict: false` (warn mode, the current setting).** Untraced words and
  unlinked multi-sense terms in new or changed prose fields are warnings,
  printed per field with counts and words. This holds during the ordinary
  backfill (L2). Without the file, the lexicon is in warn mode at the default
  threshold.
- **`strict: true`.** The same reports are `truth check` errors.
- **Enforced in both modes.**
  - Schema and config validation errors.
  - The allowlist ratchet: the allowlist may never grow.
- **The plan.** Set `strict` to true once **token coverage reaches
  `strict_token_coverage`**, proposed at 95% of the scanned tokens.
  - `truth lexicon coverage` prints the progress: the current share, the
    threshold, and the number of tokens still to trace.
  - The `truth check` summary says when the threshold is reached.
  - The flip is a deliberate one-line change, not automatic.

## Commands

```bash
target/release/truth lexicon show WORD [--limit N]     # entries, senses, uses
target/release/truth lexicon untraced [--limit N]      # worklist by frequency (L2)
target/release/truth lexicon coverage [--limit N]      # token/type coverage
target/release/truth lexicon check                     # the lexicon part of check
target/release/truth lexicon bootstrap [--write]       # generated entries
target/release/truth lexicon allowlist [--write]       # shrink-only regeneration
target/release/truth lexicon ratchet --base REV        # CI shrink check
```

`--json` gives machine-readable output.

**Bootstrap.** `bootstrap` is in Rust, not Python, so that it normalizes lemmas
with the same code the check uses. It creates two kinds of entry:

- **Function entries** come from the reviewed closed-class list
  `truth/src/lexicon/function_words.txt`. Edit the list, not the generated
  records.
- **Technical entries** come from short definition and disambiguation terms:
  - parentheticals are dropped and the term is lowercased;
  - a term of at most three words, each of two or more letters, qualifies;
  - definitions are grouped by that lemma;
  - the entry links the disambiguations that name the term, or whose senses
    all fall in the group.

It keeps ids and hand-added fields and only adds links. It never deletes an
entry and never writes an ordinary gloss: ordinary glosses are slice L2,
authored in frequency order from `untraced`.

The lexicon check runs only in `truth check`. `scripts/corpus.py check` does
not run it, and the parity test ignores its summary line.
