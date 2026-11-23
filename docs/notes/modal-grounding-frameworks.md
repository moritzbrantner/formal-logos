# Modal grounding frameworks at the foundational case; Pruss's route (2026-11-23)

Issue #1887, tests 4 and 5 (slice A), God-existence stage of the #143 root.
This note was repaired after the independent semantic challenge of head
`44f70bff`.

**Batches.**

- `specs/modal-grounding-frameworks.toml` (framework comparison; results
  module `TruthCore.Results.Modal.ModalGrounding`);
- `specs/modal-grounding-actual-absence.toml` (Pruss's own possibility
  premise; results module `TruthCore.Results.Modal.ModalGroundingActualAbsence`).

Both use the vocabulary module `TruthCore.Modal.ModalGrounding`. The attempt
is `5ee2cbef-95cc-49aa-9009-a18d0318a9ee`.

**Evidence level.** Analyst formulations, attribution deferred (logic first).
Locators are navigation only, and no source claim is made. Pruss's wording
quoted in §5 was read by the semantic challenge (plain-HTTP copy of "The
Actual and the Possible"), not in this slice.

**Related notes.** The assessment of tests 1–3 is
`docs/notes/foundational-absence-warrant.md`. The C2 background is
`docs/notes/contingency-receptivity-c2.md`.

**Graph destination.** STMT-NECESSARY-CONCRETE-AT `b19ffd92`. Three new
routes reach it, none of them through C2 or the First Way endpoint
`f9208664`:

- the foundational verdict `666f06a4` with a concrete foundational being
  `c5da5e62` (result `b27c88b0`);
- the global Pruss variant `84d02356` (result `2a3a3f09`);
- the route with Pruss's own premise `b90ee2de` (result `ad42c376`, see §5).

The batch also adds a support bundle for #1870's B6 `96971e31`.

## 1. Matching scope and fixed meanings

All accounts are framework inputs on the one `CausalityFrame` of #1784.
Contingency is `ContingentAt F.history.ontic` (MODAL_CONTINGENCY_1).
Necessity is `NecessaryAt` (NECESSARY_2, de re, relative to accessibility).

**The foundational case**, `FoundationalAt` (DEF `7fcf846e`): the being

- exists at `w`;
- has represented esse equal to its represented essence;
- has no matter and form;
- has esse received in no principle;
- is first in SIMPLY_PRIOR_1;
- has no CAUSE_2 of its esse;
- is incorruptible simply (no POSSIBLE_NOT_TO_BE_1);
- is under no POWER_OVER_ESSE_1.

Every conjunct is non-modal.

**New primitives.** Each has a stated meaning, examples and non-examples, and
no assumed structure.

- `Essential x φ`, wrapped by `EssentialTruth` (DEF `7cf63236`; sense
  ESSENCE_5 of DISAMB-ESSENCE): it lies in the nature of `x` that `φ`, Fine's
  `□ₓ`.
- `PowerFor w y p` (DEF `bf7eddca`): at `w`, `y` could initiate a causal chain
  issuing in `p`. Its load-bearing use here is a power for a tenseless
  negative state. The only available example is an abstention, a free agent's
  power not to produce anything. This is principled: "non-existence has no
  direct cause" (ST I q.104 a.3 ad 1, navigation only).
  *Later scoping* (`docs/notes/pruss-power-premises.md` §3; amendment in
  DEF `bf7eddca`'s note): for the global target this holds on both readings
  of `PowerFor`; for the actual-indexed target it holds on the causal reading
  only, since on the thin reading a replacement producer is also an example.

  There is a trade-off. Pruss's own direction avoids the abstention problem:
  his holder sits in the non-actual world with a positive power for the actual
  world's being actual. But it then needs the grounding principle at a
  non-actual world, and S5.

**Defined helpers.**

- `EntailsExistence` and `ExistenceConditionalEssences` (DEF `54bdb2f0`);
- `NoContingentConcreteIn` (DEF `6ecf24d5`; the global, world-relative
  version);
- `NoActualContingentConcreteIn` (Pruss's, indexed to the actual world `w`).

## 2. Framework verdict table

| Account | Formal input | Verdict at the foundational being | Extra commitments (exact) | Profile clauses used | Evidence |
|---|---|---|---|---|---|
| Power-grounded (PGP, Aristotelian) | `ContingencyPowerGrounded` `20d5fecd` (reused) | **necessary** | excluded middle | actuality, incorruptibility, no power | `1e6174ab` |
| Esse-identity (B6) | `ContingentHasDistinctEsse` `96971e31` (reused) | **necessary** | excluded middle | actuality, esse = essence | `39df9612` |
| Unconditional essentialism | `EssenceGroundsNecessity` `54bafc9f`, `EsseEssenceIsEssentialExistence` `565ccd6c` (the ESSENCE_3 → ESSENCE_5 bridge) | **necessary** (through B6) | the two premises (constructive), then B6's verdict | esse = essence | `f9b26559` → `39df9612` |
| Existence-conditional essentialism (Fine/Lowe reading) | `ExistenceConditionalEssences` `857654fe`, `EssentialExclusionAccount` `9d8a8d2e` | **possibly absent** | `FoundationalExistenceUnrequiredByOthers` `38200db5`, `FoundationalAbsenceRepresentable` `d1af2b06` (constructive) | actuality only; esse = essence idle | `872a3832`; omission models 1–4 |
| Combinatorial (Humean) | `UnrestrictedRecombinationAt` (reused, `13c0abe7`) | **possibly absent** | a distinct possible concrete companion | concreteness, actuality | existing `recombinationGivesContingency`; law 2 here |
| Primitivist | no grounding requirement | **neither fixed** | the modal fact itself is primitive | — | `PrimitivistSilence`: the same non-modal profile, necessary in one frame and contingent in another |
| Hybrid (powers for change; non-power modality for existence) | ST I q.2 a.3 `MovedOnlyAsInPotencyReading`, plus its existence component | **inherited**: possibly absent with a combinatorial component (recombination plus companions); none with a primitivist component | as its existence component | as its existence component | `HybridFirstWayModel` shows **consistency only** (not entailment); law 11 |

**How to read the verdicts.**

- *Schema instances.* Each verdict instantiates its account's schema at the
  foundational case. The derivation shows which profile clauses discharge it.
- *Near-definitional.* The combinatorial verdict is close to definitional:
  recombination's instance at a companion is the possible absence.
- *Labelled projections.* `b27c88b0`, `2a3a3f09` and `ad42c376` are labelled
  instantiation or assembly.

**Which profile features matter.**

- Under PGP only incorruptibility and the no-power clause matter.
- Under correlation, the no-power clause follows from uncausedness and
  incorruptibility (law 1).
- At the First Way's mover, the no-power clause follows from unreceivedness,
  firstness, correlation, passive→receptive, `b62a64ab` and B3 (law 10).
- On the essentialist accounts only esse = essence matters, and its modal
  force depends entirely on whether existence can belong to an essence
  (laws 3–4).

## 3. Laws

### Framework controls `ef54f023` (`Model.Laws`)

1. Correlation, an uncaused esse and simple incorruptibility give no power
   over the being's esse.
2. PGP, unrestricted recombination and companions exclude any concrete
   foundational being (constructive).
3. Existence-conditional essences, together with the unconditional reading of
   esse = essence, give False for any being with esse = essence whose absence
   is representable.
4. Under existence-conditional essences, a being's own essential truths never
   entail its existence once its absence is representable. So esse = essence
   is modally idle there.
5. The global P1 and P4, Euclidean access and the transfer bridge put every
   concrete contingent being under some POWER_OVER_ESSE_1 (constructive).
6. The same premises with excluded middle make every concrete foundational
   being necessary.
7. Aristotelian grounding of "nothing concrete", initiator presence and
   concrete holders give ¬ PossiblyNoConcrete wherever something concrete
   exists.
8. PossiblyNoConcrete implies the **global** P4. That P4 is the stronger
   analyst variant, not Pruss's premise.
9. **F1.** On a Euclidean frame, #248's `StrongBridge` with both C(□E n) and
   C(¬E n) gives False.
10. **F3.** At a first unmoved mover, unreceivedness, firstness, correlation,
    passive→receptive, `b62a64ab` and B3 give incorruptibility and no power
    (constructive). With PGP and excluded middle the mover is then necessary
    if it exists at `w`.
11. **F2.** With excluded middle, PGP is equivalent to (PGP for existentially
    receptive beings) ∧ (PGP for subjectless beings).

### Actual-absence controls `6cf3a8ce` (statement `0367a005`) (`Model.ActualAbsenceLaws` and models)

- **Law.** With Euclidean access, the global P4 implies Pruss's P4′. The
  converse fails (`swappedFrame`).

## 4. Models (structural satisfiability, not metaphysical possibility)

| Model | What holds | What fails | Shows | Admissible on |
|---|---|---|---|---|
| `TheistModel` | foundational God, PGP, correlation, both essentialist premises, B6, every global Pruss premise, transfer, both conclusions, the node | — | nonvacuity of every framework argument | classical theism |
| `PrussWithoutPGPModel` | every global Pruss premise and its conclusion | PGP, C2, transfer | the global route needs neither PGP nor C2 | none (a separation; on theism the transfer bridge holds) |
| `BruteFoundationalModel` | a contingent foundational being; the unconditional bridge (variant 1) or essence-grounds-necessity (variant 2) | PGP, B6, necessity verdict; the other essentialist premise | omission models of PGP, B6 and each essentialist premise | the hybrid, primitivist, combinatorial or existence-conditional views |
| `ConditionalEssenceModel` | esse = essence, conditional essence, essentialist account, both foundational clauses, verdict "possibly absent" | unconditional bridge | F4(i): esse = essence with the being contingent | Fine/Lowe existence-conditional essentialism |
| `ConditionalEssenceOmissions` 1–4 | all but one premise | that premise; the verdict | each premise of `872a3832` is needed | — |
| `PrimitivistSilence` | in two frames: the same foundational profile, `ThereIsAFirstUnmovedMover` and `PureAct` of the first mover | necessity in one, contingency in the other | the non-modal profile, with no grounding principle, fixes no verdict | modal primitivism |
| `HybridFirstWayModel` | first unmoved mover, B0, firstness, pure act, q.2 a.3, unrestricted recombination, companions, a foundational and contingent first mover; PGP's subject half has a nonvacuous antecedent (a corruptible composite) satisfied by corruptibility, with no power occurring | PGP's subjectless half, PGP, B4, necessity verdict | F2: the hybrid is consistent with these First Way premises and a contingent first mover; strictness of law 11's split | the hybrid |
| `PrussOmissions` 1–6 (global variant) | all premises but one | that premise; the conclusion | each premise is needed. Omission 2 is a contingent all-annihilating holder that fails initiator presence. Omission 4 is replacement: the one actual concretum is possibly absent, while a non-actual being is contingent at the other world. Omission 6 (Euclidean) is an artefact of the global P4 | — |
| `ConceivabilityOneSided` | the bridge with only C(¬E n) (`n` contingent); the bridge with only C(□E n) (`n` necessary) | the other conceiving | F1: law 9 needs both conceivings | — |
| `SiblingNonvacuity` | every premise of the route with Pruss's premise and its conclusion, on the theist frame and on a non-Euclidean frame | Euclidean access (second frame) | nonvacuity; Pruss's own route needs no Euclidean premise | classical theism (first frame) |
| `SiblingOmissions` 1–5 | all premises but one | that premise; the conclusion | each non-logical premise of `42da6b2d` is needed | — |
| `ReplacementVersusJointAbsence` | `swappedFrame`: S2 at `w` and P4′; `vanCleveFrame` (Euclidean): S2 at `w` | `swappedFrame`: the global P4; `vanCleveFrame`: P4′ and the global P4 | replacement separates P4′ from P4. Van Cleve's point: each actual contingent is possibly absent, yet never all jointly, so P4′ is an independent premise | — |
| `ConceivabilityS4Bundle` | on a reflexive, transitive, non-Euclidean frame, the unrestricted bridge with both C(□E n) and C(¬E n) | Euclidean access | the #1888 F1 request: law 9's inconsistency depends on Euclidean access | — |
| `ConceivabilityS4Actual` | the same bundle on a reflexive, transitive, non-Euclidean frame with `n` actual at the reading world | Euclidean access | as above, for an actual `n` (re-check N3) | — |

Excluded middle is never omitted: every model is built in Lean, which is
consistent with it.

## 5. Test 5: Pruss's Aristotelian-modality argument

### Pruss's premise compared with the first reconstruction

Pruss ("The Actual and the Possible", read by the semantic challenge) declines
the global premise. He writes that "we are talking here not about the
controversial possibility that there should exist no contingent beings, but
about the much less controversial one that those contingent beings that exist
might not exist, though perhaps other ones might then exist in their stead".
His `w1` is a world in which no member of the set of actual contingent beings
exists.

The first reconstruction (`f90934ad`, P4 `0dc833c1`) uses the global
possibility. It is therefore a **stronger analyst variant that Pruss
declines**. Its Euclidean premise and omission 6 are artefacts of that
variant: the holder is shown non-contingent at the contingent-free world, not
at `w`.

### The route with Pruss's own premise (results `42da6b2d` and `ad42c376`)

The direction stays mirrored relative to Pruss's (see the P2 comparison below
and gap 6), so this is the route *with Pruss's own premise*, not Pruss's
route.

**Premises:**

- EM;
- **P1′** `95bf8780`: if the joint absence of the actual contingent concreta
  (one accessible world lacking them all) is possible but not actual, some
  being at `w` has a power for it;
- **P2′** `906f5c39`: initiator presence for that joint absence (tenseless);
- **P3′** `a6906cab`: holders are concrete;
- **P4′** `18e5bd4e`: some accessible world lacks every concrete being contingent at `w`;
- **P5** `c76b6e2c`: some concrete being is contingent at `w`.

**Conclusion** `b90ee2de`: some concrete being exists at `w`, is necessary at `w`, and
has a power for that joint absence.

**Restriction to concreta.** P4′ restricts Pruss's S (all actual contingent
beings) to the concrete ones. This is a harmless weakening: absence of every
actual contingent being implies absence of the concrete ones, and P3′ makes the
restricted proposition sufficient, since the holder is concrete.

**Why no Euclidean premise is needed.** P1′ puts the holder `y` at `w`, and
P2′ puts `y` at a P4′-world. Were `y` absent at some world accessible from
`w`, it would be a concrete being contingent at `w`, and so absent from the
P4′-world. Hence `y` is not contingent at `w`. Each premise is needed
(`SiblingOmissions`), and the conclusion holds on a non-Euclidean frame
(`SiblingNonvacuity`). The projection to `b19ffd92` is `ad42c376`.

**Disclosure.** Neither NECESSARY_2 nor `b19ffd92` assumes Euclidean access
(#1888 §2.1b point 2). Only the global variant needed it. On Euclidean frames
the unrestricted conceivability bundle of law 9 is inconsistent, but on an S4
frame it is satisfiable, including with `n` actual (`ConceivabilityS4Bundle`,
`ConceivabilityS4Actual`). The global route therefore carried a cross-route
dependency on Euclidean access that the route with Pruss's premise removes.

### P2 compared with Pruss's principle

The typed P2 and P2′ are close to Pruss's "x cannot start any chain of causes
that can lead to actuality's not including x", with two differences:

1. **Quantifier.** His principle is universal over chains. The typed premises
   are existential, and they build in that the power's outcome is an
   accessible world.
2. **Direction.** His direction is mirrored: his holder is in `w1` with a
   power for `w0`'s actuality, and he invokes S5 for `w1` to reach `w0`.

P2 is **not** the same as `b62a64ab` plus correlation. Those concern a power
over a thing's own esse; P2 concerns the world issuing from a chain the thing
starts. Neither implies the other as typed. On a tensed reading ("no
contingent at the end"), a self-annihilating holder falsifies P2
(omission 2).

### Is the route independent of the C2 crux?

**Formally, yes.** Neither route needs PGP at the foundational being, PGP for
contingent subjects, or C2 (`PrussWithoutPGPModel`; the route with Pruss's
premise has no PGP or C2 premise either). They share only excluded middle with the C2 route.

**Dialectically, no.** P1 and P1′ are power-grounded modality applied to a
joint absence. For the global variant there is an exact formal link: P1 with
P4, Euclidean access and the transfer bridge yields PGP's power channel for
every concrete contingent being, and PGP's verdict at every concrete
foundational being (laws 5–6). This link holds only under the transfer
bridge, whose warrant is open (gap 3); without it the routes merely share a
general theory. Combinatorial, primitivist, hybrid and existence-conditional
rivals deny P1′ on the same general ground on which they deny PGP at the
foundational being. So this is a shared crux, not independent corroboration.

### Is the possibility premise common ground?

This was scoped after the semantic challenge.

**The global P4.** It is accepted by the theist (it holds in `TheistModel`)
and by rivals who accept the subtraction conclusion (law 8). It is contested
by Lowe-style views: #1888 records Lowe's reported conclusion that "there
necessarily exists at least one contingent being", and if that being is
concrete, the global P4 fails. A theist who applies Aristotelian grounding to
"nothing concrete" denies the subtraction conclusion (law 7). So the global P4
is **not** shown to be common ground.

**Pruss's P4′** is much weaker and more defensible. It needs only that the
actual contingents could all have been absent, with others perhaps in their
stead:

- A Lowe-style view that some contingent being must exist is compatible with
  P4′ (replacement; `swappedFrame` has P4′ without the global P4).
- The theist accepts it (it holds in `TheistModel`; and on Euclidean frames
  the global P4 implies it, by the unnumbered law under `6cf3a8ce`). For the
  subtraction rival it follows from PossiblyNoConcrete directly, without
  Euclidean access: a world with no concretum lacks every actual contingent
  concretum.
- It is not given by the contingency of each actual concretum taken singly
  (`vanCleveFrame`).

No recorded rival view is shown here to deny P4′. Its support is the
ordinary modal judgment that this particular collection of contingents need
not have existed. The judgment is not derived from the contingency of each
member.

**Where this leaves the crux.** With P4′, the datum is far more plausibly
shared than the foundational being's possible absence (C2 note §5). The power
theory's grounding demand then applies to a possibility the rivals have no
recorded reason to reject. They answer by denying P1′: possibilities of
existence need no power. This is the "too few potentialities" objection, now
at a datum no recorded rival is shown to reject. The disagreement remains in the general theory of
modality for existence. The route changes where the burden sits, not who
wins.

### Reach

**Reaches `b19ffd92`: yes**, through `2a3a3f09` (global variant) and
`ad42c376` (Pruss's own premise).

**Not reached:**

- the C2 route's endpoint `f9208664`;
- the selected-grounding closure `c71c068c`.

The exact missing bridges are a link from the holder to firstness or to the
First Way's mover (nothing identifies them), and a selected-grounding reading
of the holder's power for `c71c068c` (an explicit bridge from `PowerFor` to
`grounds`). Neither was built; treating a power as grounding by name is
excluded.

## 6. Coordinator requests F1–F5

- **F1:** built.
  - Law 9 and the one-sided models.
  - The S4 satisfying model of the bundle requested by #1888, twice:
    `ConceivabilityS4Bundle` (where `n` is not actual at the reading world)
    and `ConceivabilityS4Actual` (where `n` is actual at the reading world, as
    #1888's point requires).
  - The bridge is applied to `Box` over the route's own existence valuation;
    the Euclidean step is direct rather than reused through
    `necessary-if-existent-symmetry-437`.
- **F2:** built as a factorization with excluded middle (law 11), with
  strictness from `HybridFirstWayModel`.
  - #1888 §8 requested, with excluded middle (or decidable `CanFailToBe`) as
    an explicit premise: "PGP ↔ (∀x, ContingentAt x ∧ ¬CanFailToBe x esse →
    ∃y, PowerOverEsse y x)", i.e. PGP's substantive content as its
    completeness over incorruptibles. That equivalence was **not built**. It
    was replaced by the receptive/subjectless split (law 11), whose halves
    are "receptive" in the C2 batch's sense (`ExistentiallyReceptive`:
    received esse in a receptive principle, or matter and form) and its
    negation. The requested form is listed as next test 9. It is a
    propositional triviality given excluded middle: a corruptible being
    satisfies PGP's first disjunct.
  - Not built: a registered `strength_comparison` relation (it would need
    excluded middle as background) and a "power" disambiguation (the hybrid's
    change component is the existing `MovedOnlyAsInPotencyReading`).
  - The "corruptibles forced" clause adds nothing beyond `8bfc4ab7` and C2
    law 6.
- **F3:** built (law 10).
- **F4:** covered.
  - (i) is `ConditionalEssenceModel`.
  - (ii) is `f9b26559` → `39df9612`.
  - The deciding question is formalized as laws 3–4. `Essential` is now
    registered as ESSENCE_5, and `565ccd6c` is `f9b26559`'s sense bridge.
- **F5:** already exists (attempt `03e1f49f`; `ContingentRecombinationAt` in
  the theist S5 model; subtraction law 9). Law 2 here adds the same at the
  foundational case. The parthood clause is not modelled.
- **#1888 gap 4 (Pruss's joint-absence premise against Van Cleve):** answered
  formally. Pruss's P4′ is not entailed by each actual contingent's possible
  absence (`vanCleveFrame`). Its warrant is the modal judgment about the
  collection.

## 7. Claim versus type

| Record | Prose | Lean type | Check |
|---|---|---|---|
| `666f06a4` | every foundational being at `w` exists at every accessible world | `∀ f, FoundationalAt … f → NecessaryAt F.history.ontic w f` | universal; does not assert that any foundational being exists |
| `fe8c3a1d` | every foundational being at `w` is contingent | `∀ f, FoundationalAt … f → ContingentAt …` | same scope |
| `c5da5e62` | some concrete foundational being; admissible on theism and on the brute-first rival | `∃ f, concrete f ∧ FoundationalAt … f` | non-modal; the models show admissibility only |
| `565ccd6c` | esse = essence puts existence in the nature | `esseOf x = essenceOf x → Essential x (fun v => ExistsAt v x)` | unconditional; the ESSENCE_3 → ESSENCE_5 bridge |
| `857654fe` | essential truths hold where the bearer is absent | `Essential x φ → ∀ v, ¬ ExistsAt v x → φ v` | over all points of `W` |
| `d1af2b06` | some point lacks each foundational being | `∃ v, ¬ ExistsAt v f` | not accessibility |
| `94393b5b` | if the absence of every contingent concretum is possible but not actual, a being has a power for it | `(∃ v, access w v ∧ p v) → ¬ p w → ∃ y, ExistsAt w y ∧ PowerFor w y p` | one global `p`; not PGP |
| `0dc833c1` | the global possibility (stronger than Pruss's) | `∃ v, access w v ∧ NoContingentConcreteIn F concrete v` | contingency at `v` |
| `fffa0693` | P2 | `PowerFor w y p → ∃ v, access w v ∧ p v ∧ ExistsAt v y` | existential; tenseless |
| `84d02356` | necessary concrete holder (global variant) | `∃ y, concrete ∧ exists ∧ NecessaryAt ∧ PowerFor …` | no uniqueness, firstness or God |
| `18e5bd4e` (P4′) | some accessible world lacks every concrete being contingent at `w` | `∃ v, access w v ∧ ∀ x, concrete x → ContingentAt w x → ¬ ExistsAt v x` | indexed to `w`; others may exist |
| `b90ee2de` | necessary concrete holder of a power for the actual contingent concreta's joint absence | same shape as `84d02356` with `NoActualContingentConcreteIn … w` | no Euclidean premise used |

Sibling statement IDs: P1′ `95bf8780`, P2′ `906f5c39`, P3′ `a6906cab`, P4′
`18e5bd4e`, conclusion `b90ee2de`, controls `0367a005`. Every hypothesis of each theorem is a listed premise
(bind-check: 11 bound, 0 mismatch). No source is attributed.

## 8. Objections, applied symmetrically

**Against the necessity verdicts.** No substantive objection is identified to
the inferences. PGP, B6 and the unconditional bridge are contested by
developed rival theories (C2 note §8): possibilities of existence need no
power, or essences are existence-conditional.

#1888 finds **parity** between existence-conditional essentialism and PGP at
the foundational being. EC's standing there is "no / open, as for PGP", and
"no relative standing is claimed". EC's concrete/abstract cut and PGP's
completeness over incorruptibles have the same status.

**Against the "possibly absent" verdicts.** These are contested by PGP, by
unconditional essentialism, and by the reply that the possibility datum at
the foundational being has no independent support (C2 note §5; #1888
test 1).

**Against Pruss's routes.** The recorded objections are:

- denial of P1/P1′;
- a tensed reading of P2/P2′;
- for the global variant only, Lowe-style denial of the global P4.

No substantive objection is identified to P3/P3′ or P4′. The omission models
show only that these premises are needed.

## 9. Remaining gaps and next tests

1. Whether "existence never belongs to an essence" applies to an esse-essence
   identity. This decides between laws 3–4 and `f9b26559`.
2. A tensed initiator-presence variant over the frame's `IsAt`.
3. The warrant for the transfer bridge (laws 5–6). Without it the formal link
   between the Pruss routes and PGP does not hold.
4. A registered strength comparison for PGP's two halves.
5. A bridge from the Pruss holder to firstness, to the First Way endpoint or
   to `c71c068c`.
6. Pruss's iterated powers (a power to produce a power-holder), and his own
   direction (a power in `w1` for `w0`'s actuality, with S5). One-step
   `PowerFor` at `w` represents neither.
7. Whether a power to abstain counts as a power in Aristotelian modality's
   sense (DEF `bf7eddca`; q.104 a.3 ad 1).
8. `truth countermodel` does not handle `CausalityFrame` parameters; all
   models are hand-written.
9. #1888's F2 equivalence, PGP ↔ (∀x, ContingentAt x ∧ ¬CanFailToBe x esse →
   ∃y, PowerOverEsse y x) with excluded middle: not built (replaced by the
   receptive/subjectless split). It is a propositional triviality given
   excluded middle, worth registering only as a certified difference
   (completeness over incorruptibles).

## 10. Cross-lane edits (for the coordinator)

- `corpus/disambiguations/essence.json`: sense ESSENCE_5 appended, with parameter tags on the `Essential` binder of four premise definitions, plus one
  resolution sentence.
- The three bundle audits that pin it by hash
  (`docs/notes/classical-attributes-migration.json`,
  `docs/notes/classical-attributes-all-migration.json`,
  `docs/notes/naming-first-mover-migration.json`): the pin was updated, with a
  re-review finding. No audited statement or argument links DEF `7cf63236`.
- `corpus/definition-status.json`: only this module's four entries were
  added; other modules' stale entries were not refreshed.
