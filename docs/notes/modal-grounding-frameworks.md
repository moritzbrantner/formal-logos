# Modal grounding frameworks at the foundational case; Pruss's route (2026-11-23)

Issue #1887, tests 4 and 5 (slice A), God-existence stage of the #143 root.
Batch `specs/modal-grounding-frameworks.toml`, vocabulary module
`TruthCore.Modal.ModalGrounding`, results module
`TruthCore.Results.Modal.ModalGrounding`, attempt
`5ee2cbef-95cc-49aa-9009-a18d0318a9ee`. Analyst formulations, attribution
deferred (logic first). The locators are navigation only: no source claim is
made and nothing was materialized in this slice. The assessment of tests 1–3
is `docs/notes/foundational-absence-warrant.md` (the parallel slice), and the
C2 background is `docs/notes/contingency-receptivity-c2.md`.

**Graph destination.** STMT-NECESSARY-CONCRETE-AT `b19ffd92`. This batch
reaches it by two new routes that pass through neither C2 nor the First Way
endpoint `f9208664`:

- the foundational verdict `666f06a4` with a concrete foundational being
  `c5da5e62` (result `b27c88b0`);
- the Pruss conclusion `84d02356` (result `2a3a3f09`).

It also adds a support bundle for #1870's B6 `96971e31`.

## 1. Matching scope and fixed meanings

All accounts are framework inputs on the one `CausalityFrame` of #1784.
Contingency is `ContingentAt F.history.ontic` (MODAL_CONTINGENCY_1); necessity
is `NecessaryAt` (NECESSARY_2, de re, relative to accessibility).

**The foundational case**, `FoundationalAt` (DEF `7fcf846e`), states that `f`:

- exists at `w`;
- has represented esse equal to its represented essence;
- has no matter and form;
- has esse received in no principle;
- is first in SIMPLY_PRIOR_1;
- has no CAUSE_2 of its esse;
- is incorruptible simply (no POSSIBLE_NOT_TO_BE_1);
- is under no POWER_OVER_ESSE_1.

Every conjunct is non-modal.

**New primitives** (stated meaning, examples, non-examples and no assumed
structure, per AGENTS.md "Semantic grounding"):

- `Essential x φ` (DEF `7cf63236`): it lies in the nature of `x` that `φ`,
  Fine's `□ₓ`.
- `PowerFor w y p` (DEF `bf7eddca`): at `w`, `y` could initiate a causal chain
  issuing in `p`.

**Defined helpers:**

- `EntailsExistence` and `ExistenceConditionalEssences` (DEF `54bdb2f0`);
- `NoContingentConcreteIn` (DEF `6ecf24d5`): DEF-NO-CONTINGENT-CONCRETE-AT
  restated on the frame's `Ontic`.

## 2. Framework verdict table

"Uses" lists the conjuncts of the foundational profile that the verdict
consumes.

| Account | Formal input | Verdict at the foundational being | Extra commitments (exact) | Uses | Evidence |
|---|---|---|---|---|---|
| Power-grounded (PGP, Aristotelian) | `ContingencyPowerGrounded` `20d5fecd` (reused) | **necessary** | excluded middle | actuality, incorruptibility, no power | `1e6174ab` |
| Esse-identity (B6) | `ContingentHasDistinctEsse` `96971e31` (reused) | **necessary** | excluded middle | actuality, esse = essence | `39df9612` |
| Unconditional essentialism | `EssenceGroundsNecessity` `54bafc9f`, `EsseEssenceIsEssentialExistence` `565ccd6c` | **necessary** (through B6) | the two premises (constructive), then B6's verdict | esse = essence | `f9b26559` → `39df9612` |
| Existence-conditional essentialism (Fine/Lowe reading) | `ExistenceConditionalEssences` `857654fe`, `EssentialExclusionAccount` `9d8a8d2e` | **possibly absent** | `FoundationalExistenceUnrequiredByOthers` `38200db5`, `FoundationalAbsenceRepresentable` `d1af2b06` (constructive) | actuality only; esse = essence idle | `872a3832`; omission models 1–4 |
| Combinatorial (Humean) | `UnrestrictedRecombinationAt` (reused, `13c0abe7`) | **possibly absent** | a distinct possible concrete companion | concreteness, actuality | existing `recombinationGivesContingency`; law 2 here |
| Primitivist | no grounding requirement | **neither fixed** | the modal fact itself is primitive | — | `PrimitivistSilence`: same profile, necessary in one frame and contingent in another |
| Hybrid (powers for change, non-power modality for existence) | ST I q.2 a.3 `MovedOnlyAsInPotencyReading` + recombination; PGP's subject half | **possibly absent** (from its existence component) | as combinatorial or primitivist | — | `HybridFirstWayModel`; law 11 |

**Labels.**

- *Definitional.* The combinatorial verdict is close to definitional:
  recombination's instance at a companion is the possible absence.
- *Instantiations.* `b27c88b0` and `2a3a3f09` are labelled as instantiation and
  assembly respectively.

The other verdicts are derivations: no premise mentions the verdict.

**Which profile features matter.**

- **PGP:** only incorruptibility and the no-power clause matter. Simplicity,
  unreceivedness and firstness are idle for PGP's verdict. They matter
  upstream: under correlation the no-power clause follows from
  uncausedness and incorruptibility (law 1). At the First Way's mover it
  follows from unreceivedness, firstness, correlation, passive→receptive,
  `b62a64ab` and B3 (law 10).
- **Essentialist accounts:** only esse = essence matters, and its modal force
  depends entirely on whether existence can belong to an essence (laws 3–4).

## 3. Joint incompatibilities and laws (`Model.Laws`, in controls `ef54f023`)

1. Correlation, an uncaused esse and simple incorruptibility give no power
   over the being's esse.
2. PGP, unrestricted recombination and companions exclude any concrete
   foundational being (constructive). This is **recombination against a
   necessary concretum**, at matching scope.
3. Existence-conditional essences together with the unconditional reading of
   esse = essence give False, for any being with esse = essence whose absence
   is representable.
4. Under existence-conditional essences, a being's own essential truths never
   entail its existence once its absence is representable. So esse = essence
   is modally idle there.
5. Pruss's P1 and P4, Euclidean access and the transfer bridge give: every
   concrete contingent being is under some POWER_OVER_ESSE_1 (constructive).
6. The same premises with excluded middle make every concrete foundational
   being necessary.
7. Aristotelian grounding of "nothing concrete", initiator presence and
   concrete holders give: ¬ PossiblyNoConcrete, wherever something concrete
   exists. Pruss-style grounding contradicts the subtraction conclusion.
8. PossiblyNoConcrete implies P4. The subtraction rival accepts Pruss's
   possibility premise.
9. **F1, conceivability parity.** On a Euclidean frame, #248's `StrongBridge`
   with both C(□E n) and C(¬E n) gives False.
10. **F3.** At a first unmoved mover, unreceivedness, firstness, correlation,
    passive→receptive, `b62a64ab` and B3 give incorruptibility and no power
    over its esse (constructive). With PGP and excluded middle it is then
    necessary if it exists at `w`. That correlation and `b62a64ab` are needed
    is shown by the existing C2 models `selfAnnihilator` v1/v2. Neither exposes
    "no power" separately, so this law is new.
11. **F2.** With excluded middle, PGP ↔ (PGP for existentially receptive
    beings) ∧ (PGP for subjectless beings).

## 4. Models (structural satisfiability, not metaphysical possibility)

| Model | What holds | What fails | Shows | Admissible on |
|---|---|---|---|---|
| `TheistModel` | foundational God, PGP, correlation, both essentialist premises, B6, every Pruss premise, transfer, both conclusions, the node | — | nonvacuity of every argument | classical theism |
| `PrussWithoutPGPModel` | every Pruss premise and its conclusion | PGP, C2, transfer | Pruss's route needs neither PGP nor C2 | none (a separation: on theism the transfer bridge holds) |
| `BruteFoundationalModel` | a contingent foundational being; the unconditional bridge (variant 1) or essence-grounds-necessity (variant 2) | PGP, B6, necessity verdict; essence-grounds-necessity (variant 1) or the bridge (variant 2) | omission models of PGP, B6 and each essentialist premise | the hybrid, primitivist, combinatorial or existence-conditional views (the C2 note's `bruteSimple`) |
| `ConditionalEssenceModel` | esse = essence, conditional essence, essentialist account, both foundational clauses, verdict "possibly absent" | unconditional bridge | **F4(i)**: esse = essence with the being contingent | Fine/Lowe existence-conditional essentialism |
| `ConditionalEssenceOmissions` 1–4 | all but one premise | the omitted premise; the verdict | each premise of `872a3832` is needed | — |
| `PrimitivistSilence` | the same foundational profile and First Way premises in two frames | necessity in one, contingency in the other | the profile without a grounding principle fixes no verdict | modal primitivism |
| `HybridFirstWayModel` | first unmoved mover, B0, firstness, pure act, q.2 a.3, unrestricted recombination, companions, PGP's subject half (nonvacuous at a corruptible composite), foundational and contingent first mover | PGP's subjectless half, PGP, B4, necessity verdict | **F2**: the hybrid is jointly consistent with the First Way's act and potency premises with a contingent first mover; strictness of law 11's split | the hybrid |
| `PrussOmissions` 1–6 | all Pruss premises but one | the omitted premise; the conclusion | each non-logical premise is needed; omission 2 is a contingent all-annihilating holder (fails initiator presence); omission 4 has S2 at `w` without P4 (Van Cleve) | — |
| `ConceivabilityOneSided` | bridge with only C(¬E n), `n` contingent; bridge with only C(□E n), `n` necessary | the other conceiving | **F1**: law 9's inconsistency needs both conceivings | — |

Excluded middle is never omitted: every model is built in Lean, which is
consistent with it.

## 5. Test 5: Pruss's Aristotelian-modality argument

### Reconstruction (result `f90934ad`)

The analyst reconstruction (attribution deferred) has these premises:

- EM (excluded middle);
- Euclidean access (STMT-EUCLIDEAN-FRAME);
- **P1** `94393b5b`: if no contingent concretum is possible and not actual,
  some being at `w` has a power for it;
- **P2** `fffa0693`: initiator presence (tenseless);
- **P3** `2d2be120`: holders are concrete;
- **P4** `0dc833c1`: possibly no contingent concretum;
- **P5** `c76b6e2c`: some concrete being is contingent at `w`.

The conclusion is `84d02356`: some concrete being exists at `w` and at every
accessible world, and has a power for there being no contingent concretum.
The projection to `b19ffd92` is result `2a3a3f09`.

### Is it independent of the C2 crux?

**Formally, yes.** The route does not need PGP at the foundational being, nor
PGP for contingent subjects, nor C2 (`PrussWithoutPGPModel`). It shares only
excluded middle with the C2 route. It uses Aristotelian grounding for one
**global** possibility whose subjects are all contingent, together with a
global-possibility premise.

**Dialectically, no.** P1 is power-grounded modality applied to a global
possibility. With the transfer bridge (a power for "no contingent concretum"
is a power over the esse of each concretum it excludes), P1 yields PGP's power
channel for every concrete contingent being. It also yields PGP's verdict at
every concrete foundational being (laws 5–6). So P1 plus the transfer bridge
is not weaker than PGP on concreta.

The combinatorial, primitivist, hybrid and existence-conditional rivals deny
P1 on the same general ground on which they deny PGP at the foundational
being: possibilities of existence need no power. One package denies both, so
this is convergence on a shared crux, not independent corroboration.

**What changes is the datum.** The rival does accept P4: law 8 shows that the
subtraction conclusion implies it, and the existence-conditional and
primitivist rivals have no essence or primitive fact excluding it. At the
foundational being the only datum was the disputed possibility of its absence
(C2 note §5). Here the possibility is common ground. The power theory's
grounding demand is applied to a possibility both sides accept, so the "too
few potentialities" objection now has a datum. The power theory answers it
with the necessary holder; the rival answers it by denying P1. The
disagreement stays in the general theory of modality for existence.

### Exact premises the rival might contest beyond P1

- **P2 (initiator presence).** It holds on the frame's tenseless existence,
  where a chain's initiator exists in the world of the chain. On a tensed
  reading ("no contingent concretum at the end") a self-annihilating holder
  falsifies it (omission 2).
- **P2 compared with Pruss's own premise.** P2 is close to Pruss's "x cannot
  start any chain of causes that can lead to actuality's not including x"
  (the assessment slice's reading of "The Actual and the Possible").
  "Actuality" there is the whole world, so the tenseless reading matches.
- **P2 compared with C2's premises.** P2 is **not** the same as `b62a64ab`
  plus correlation. Those concern a power over a thing's *own esse*: if it
  has such a power, it is corruptible or causes its own being. P2 concerns
  the *world* issuing from a chain the thing starts. Neither implies the other
  as typed. Correlation bears only on the transfer bridge's consequence
  (laws 5–6), not on the core route.
- **P4 (Van Cleve's point).** "Each actual concretum possibly absent" does
  not give "possibly all absent". Pruss omission 4 has S2 at `w` while P4
  fails. So P4 is an independent premise. Its support is the subtraction
  argument (`6aba0bb4`, which needs S1, S3 and transitivity) or direct modal
  intuition, not the contingency of each concretum.
- **P3 (concrete holders)** and **Euclidean access** are each needed
  (omissions 3 and 6).

**Reaches `b19ffd92`: yes**, through `2a3a3f09`.

**Not reached:**

- the C2 route's endpoint `f9208664`;
- the selected-grounding closure `c71c068c`.

The exact missing bridges are a link from the Pruss holder to firstness or
to the First Way's mover (nothing identifies them), and a selected-grounding
reading of the holder's power for `c71c068c`, which would need an explicit
bridge from `PowerFor` to `grounds`. Neither was built. Treating a power as
grounding by name is excluded by AGENTS.md.

## 6. Coordinator requests F1–F5

- **F1:** built (law 9, `ConceivabilityOneSided`). The bridge is applied to
  `Box` over the route's own existence valuation. It is not reused through
  `necessary-if-existent-symmetry-437`: the Euclidean step is direct.
- **F2:** built as a factorization with excluded middle (law 11). Strictness
  comes from `HybridFirstWayModel`, which extends `bruteSimple` to a
  combinatorial hybrid with a nonvacuous subject half. Two things were not
  built:
  - a registered `strength_comparison` relation (#1598). The factorization
    is premise-free only with excluded middle, so the comparison would need
    excluded middle as background. Left as a next test.
  - the requested disambiguation of "power" into change-power and
    POWER_OVER_ESSE_1. The hybrid's change component is the existing
    `MovedOnlyAsInPotencyReading` (POTENCY_1), not a new power relation, so
    no new sense was needed.

  "Restricted half with `8bfc4ab7` forces power-grounding for every
  corruptible": not built as a separate law. Every corruptible already
  satisfies PGP's first disjunct, and with `8bfc4ab7` it is in POTENCY_1,
  which is `8bfc4ab7` itself. No content beyond the existing C2 law 6.
- **F3:** built (law 10).
- **F4:** covered.
  - (i) is `ConditionalEssenceModel`.
  - (ii) is `f9b26559` → `39df9612` (essential existence and essence-grounds-
    necessity give B6, hence necessity).
  - The deciding question is formalized as laws 3–4: on existence-conditional
    essentialism, esse = essence cannot be read as existence belonging to the
    essence once the being's absence is representable.
- **F5:** already exists (attempt `03e1f49f`), not rebuilt.
  - The exempted dictum is `ContingentRecombinationAt`, which holds in the
    theist S5 model.
  - The unexempted dictum with companions excludes a necessary concretum
    (subtraction law 9; `recombinationGivesContingency` with
    `necessaryConcreteExcludesContingencyPremise`). Law 2 here adds the same
    at the foundational case.
  - The parthood clause ("except by parthood") is not modelled: the profile
    has no parts.

## 7. Claim versus type

| Record | Prose | Lean type | Check |
|---|---|---|---|
| `666f06a4` | every foundational being at `w` exists at every accessible world | `∀ f, FoundationalAt … f → NecessaryAt F.history.ontic w f` | universal; asserts no foundational being exists |
| `fe8c3a1d` | every foundational being at `w` is contingent | `∀ f, FoundationalAt … f → ContingentAt …` | same scope |
| `c5da5e62` | some concrete foundational being | `∃ f, concrete f ∧ FoundationalAt … f` | non-modal |
| `565ccd6c` | esse = essence → existence in the nature | `∀ x, esseOf x = essenceOf x → Essential x (fun v => ExistsAt v x)` | unconditional proposition; not attributed |
| `857654fe` | essential truths hold where the bearer is absent | `Essential x φ → ∀ v, ¬ ExistsAt v x → φ v` | over all points of `W`, not only accessible ones |
| `d1af2b06` | some point lacks each foundational being | `∃ v, ¬ ExistsAt v f` | not accessibility; does not by itself give contingency |
| `94393b5b` | P1 | `(∃ v, access w v ∧ p v) → ¬ p w → ∃ y, ExistsAt w y ∧ PowerFor w y p` | one global `p` only; not PGP |
| `fffa0693` | P2 | `PowerFor w y p → ∃ v, access w v ∧ p v ∧ ExistsAt v y` | tenseless existence |
| `84d02356` | necessary concrete holder of a power for `p` | `∃ y, concrete y ∧ ExistsAt w y ∧ NecessaryAt … y ∧ PowerFor w y p` | no uniqueness, firstness or God |
| `f9b26559` | unconditional essentialism gives B6 | conclusion `ContingentHasDistinctEsse` | constructive; B6 not established |

All hypotheses of each theorem are listed premises (bind-check: 8 bound, 0
mismatch). No source is attributed.

## 8. Objections, applied symmetrically

**Against the necessity verdicts.** No substantive objection is identified to
the inferences. The premises PGP, B6 and the unconditional bridge are
contested by the developed rival theories recorded in the C2 note §8. Their
mechanism is that possibilities of existence need no power, or that essences
are existence-conditional. Their independent justification is that general
modal theories hold this, and the assessment slice rates the
existence-conditional theory strongest at the foundational being.

**Against the "possibly absent" verdicts.** These are contested by PGP, by
unconditional essentialism, and by the PGP-side reply that the possibility
datum at the foundational being has no independent support (C2 note §5;
assessment test 1).

**Against Pruss's route.** The recorded mechanisms are denial of P1 (as
above) and a tensed reading of P2. No objection has been identified to P3 or
to Euclidean access beyond their need (omission models). Those models are not
evidence against the premises.

## 9. Remaining gaps and next tests

1. Whether "existence never belongs to an essence" applies to an esse-essence
   identity. This decides between laws 3–4 and `f9b26559`; it is the
   assessment slice's decisive question.
2. A tensed initiator-presence variant over the frame's `IsAt`.
3. The warrant for the transfer bridge (laws 5–6).
4. A registered strength comparison for PGP's two halves.
5. A bridge from the Pruss holder to firstness, the First Way endpoint or
   `c71c068c`.
6. Pruss's iterated powers (a power to produce a power-holder), which
   one-step `PowerFor` does not represent.
7. `truth countermodel` does not handle `CausalityFrame` parameters; all
   models are hand-written.
