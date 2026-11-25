# Two-relation possibility control (#438)

The missing bridge is now explicit: for every carrier D, pair of frames E/M
and origin w, `(∀ P, Dia E P w → Dia M P w) ↔ IncludedAt E M w`.
The box direction is `(∀ P, Box M P w → Box E P w) ↔ IncludedAt E M w`.
`diamond_transfer_iff` tests singleton predicates for necessity;
`box_transfer_iff` tests the M-successor predicate. Sufficiency transports
accessibility. These are constructive consequences, not transcriptions of an
assumed bridge. Full predicate quantification matters; no claim is made for a
restricted language without separating predicates.

The omitted-inclusion control uses two candidate descriptions (Bool), universal
E, identity M, origin false, and P(v) := v = true. Both frames are reflexive,
symmetric and transitive. P has a satisfying description and an E-witness, but
no M-witness at false. M-box-not-P holds and E-box-not-P fails. This is a
nonempty-accessibility control. It does not call the excluded candidate a
genuinely metaphysically possible world, or turn semantic satisfiability into
syntactic consistency. No theorem interprets absence of a proof as possibility.
Logical, conceptual and nomological possibility are not identified with these
stipulated E/M profiles.

Reuse: `TruthCore.Modal.Frame`, the existing `GoedelGod.MProp/Box/Dia`, and
`Models.FiniteSupport`. The #248 `Conceivability.StrongBridge` instead has an
arbitrary conception operator; its theorem does not characterize two-relation
inclusion. The #262–268 research controls concern individual modal frame
conditions, collapse, extensionality and propagation, not this cross-relation
bridge. No geometry, modal-duality, or collapse matrix was repeated. No Hume
claim was added; its source-specific conception and withholding reading remain
separate. Existing dossier `STMT-HUME-CONCEIVABILITY-TESTS` was inspected.

Premise comparison: no premises retained, added, removed or discharged at the
corpus argument boundary. The closed theorem quantifies over profiles and
contains conditional laws; it does not establish inclusion for actual knowledge
or metaphysical possibility. Root-path open-premise change is exactly zero.
Actual epistemic adequacy and metaphysical fidelity remain open research
obligations. [`ATTEMPT-MODAL-POSSIBILITY-TRANSFER`](../../corpus/attempts/modal-possibility-transfer.json) records the result and rejected
interpretations; the generated dossier is not an independent authority.

Challenge frozen before solution: SHA256
`cb22f876bd3f58392488f47fe43873aec5383439456f369d17321627c7c410ef`.
Self-sweep: statement, argument, result description and comments all describe
`Checks = TransferLaws ∧ OmissionControl`; no unlisted nonemptiness condition,
actual metaphysical conclusion, historical attribution or proof-search result.
All load-bearing terms link the stipulative definitions and E/M disambiguation.

Local service: coordinator workspace
`/home/brantner/privat/truth-core-sprint-proof`, preview HEAD
`49b4589aa6744c91a6bc9adec13215d0e7245c9d`, persistent session
`causal-harvest`, virtual path `Scratch/issue438/PossibilityTransfer.lean`.
The client held `flock /tmp/truth-core-lean.lock` and POSTed full concatenated
module/solution text (omitting the solution's local import) to
`http://127.0.0.1:8765/lean/diagnostics`; no preview files/imports were changed.
An initial `decide` needed explicit unfolding of the control definitions;
the corrected version had no diagnostics. A repeated edit adding `#print axioms`
reported no axioms, content SHA256
`dc58eb7310e6da45e7d55eb22b49fed6f44533181ddca983ba3c4c431a8e32f3`,
version 3. A goal lookup at line 62 returned null at that position; no goal
claim is based on it. The response reports the preview dirty state and diff
SHA256 `660a0c8ebd32fec39115624b54b7ad33ab84bc3a9f5a747f309f92e4ee27556c`.
This is interactive proof feedback, not canonical Comparator/NanoDa evidence;
final CI verifies canonical modules. Retain the service for repeated proof
edits; no CLI performance comparison was run in this lane.


## Plantinga-style compatibility application (#1864, 2026-11-22)

**Current conditional analysis (not a new root conclusion).** The existing
[necessary-if-existent](../../TruthCore/Modal/NecessaryIfExistent.lean)
profile and its [proved matrix](../../TruthCore/Results/Modal/NecessaryIfExistent/Solution.lean)
already establish under K5: if `□(G → □G)` and `◇G`, then `□G`.
Reflexivity additionally yields `G` at the designated actual world. The
separate reverse `◇¬G` still needs its own substantive reason. This is a
truth-functional modal comparison, not an independent proof of either premise.

**Possibility as absence of impossibility.** Within a *fixed classical*
modal interpretation, the precise claim is
`◇G ↔ ¬□¬G`. The added helper
`absence_of_impossibility_iff_possible` makes excluded middle explicit
rather than presupposing a nonconstructive operator conversion (formula-local
double-negation elimination would suffice, as the existing
`TruthCore.Modal.PossibleImpossibility.LocalClassical` records). Consequently
`s5_not_impossible_actual` composes the existing positive modal theorem
with reflexivity and gives actual `G` from `¬□¬G`. None of this turns
`not yet proven impossible` into `¬□¬G`: the former reports evidence or
our incomplete proof search, whereas the latter denies that **all**
admissible alternatives lack G. A mere absence of an identified contradiction
may provide **defeasible** support for a positive recombination policy, but
it is not the theorem's antecedent.

**Incompatibility is not repaired by a word.** For the *same bearer* at the
*same world*, if `P(v,x) → ¬Q(v,x)` at every world, no accessible world can
instantiate `P(v,x) ∧ Q(v,x) ∧ tag(v,x)`, for any extra predicate `tag`.
The helper `incompatible_bundle_not_possible` proves this on arbitrary
frames, not only S5. `P` and `Q` are arbitrary predicates with no essence
marker or respect parameter: an application to essential attributes in one
respect must build essentiality and the respect into them. Set `Q := ¬P` for
a strict contradiction. A genuine
square/circle application would have to establish from the FIXED geometric
definitions that both features are incompatible in the same respect; a square
inscribed in a circle is not a counterexample to that fixed claim. An adjective
“possible” does not alter the inconsistent conjunction or yield a witness.
Conversely, simply identifying a syntactically coherent description does not
establish its metaphysical realizability.

**The bearer and the attributes matter.** The analyst's
`MaximalProfile F ExistsAt Excellent x v` has one fixed candidate `x`,
existing at `v` and existing plus excellent at every world accessible from
`v`. `PossibleMaximalProfile` is an accessible **joint instantiation**
of that complete profile. Under S5, the helper
`possible_maximal_profile_same_bearer` obtains the **same x** existing and
excellent at the actual root and all its accessible successors. It uses
symmetry to return from the possible profile world to the root and
Euclideanness to transport the profile across siblings. Its result is not
the false quantifier shift from `□∃x` to `∃x□`. "The same x" is relative to
the signature's semantics: one bearer type across worlds (constant domain,
possibilist inner `∃`) with world-relative existence, so identity across
worlds is identity in that type. Actualist or counterpart semantics would need
a transworld-identity premise, which stays OPEN; the counterpart-essentialism
rival in [the Kant inference investigation](../kant-cosmological-inference.md)
is untouched. The transport is not new: the existing
`NonlimitingConcreteExistence.necessaryAtOrigin` (and
`ActualEuclidean.necessaryAtOrigin`) gives it for one `Ontic` individual from
Euclidean accessibility plus reflexivity at w, so S5 is more than this step
needs. The new content is carrying the excellence conjunct with existence.

These are **analyst interfaces**, not Plantinga source attributions. Actual
`Excellent` still needs appropriately interpreted omnipotence, omniscience
and moral perfection; `ExistsAt` needs the same rigid bearer, GOD_4 naming
and the real-world `Ontic` vocabulary. Neither this theorem nor the
word “maximal” supplies the GOD_4 attributes. A world predicate `G`
already used by #437 cannot be silently identified with
`GodExists sigma.IsGod`. Moreover, the S5 accessibility component is
a stipulated model, not automatically *all metaphysical possibilities*.

**The exact open bridge.** Logical joint satisfiability is one type of
evidence for possible instantiation, but a proof of satisfiability in
candidate descriptions does not guarantee an M-accessible witness. The
existing #438 `epistemic` (universal) versus `metaphysical` (identity)
Bool control shows that S5 frame conditions alone do not entail that
unrestricted transfer: both frames satisfy S5. It is a structural surrogate
(a model-relative filter), so it shows non-entailment, not that the transfer
principle is false. A sufficient route can target the **particular complete divine
profile** and show why its realizing world is admissible from the actual
standpoint, instead of assuming `IncludedAt E M w` for *all* descriptions.
That witness-specific principle remains OPEN and requires philosophical
warrant. The stronger conditional system is still useful: it identifies
precisely what must be defended.

**Positive warrant and rival.** The prima-facie policy argued in
[the Kant inference investigation](../kant-cosmological-inference.md)
provisionally recombines features when no identified essential condition
excludes their union, noting its limits when inferring unreceived concrete
subsistence. A supported incompatibility of divine features, or a principled
restriction on what counts as an admissible essence, would revise that
provisional assessment. Mere withholding of assent and unspecified
“hidden contradictions” do not themselves supply an incompatibility proof.
The reverse modal possibility claim likewise requires a real modal
witness/argument; these are distinct *evidential burdens*, despite
the formal symmetry of the conditional deductions.

**Status and graph connection.** The unchanged #437/#438 results are
verified. The #1864 helper declarations are a scoped mathematical
checkpoint, Lean-checked in CI (#1865); they are not new bound corpus results
or a claimed source reading, and they change no root premise or establish
divine possibility. Graph destination: the actual de re necessary concrete
bearer `b19ffd92` and, through GOD_4, `STMT-GOD-EXISTS`. Exact blockers: the
GOD_4 attribute mapping of `Excellent`, and the metaphysical admissibility of
the particular profile's realizing world. The
substantive acceptance work in [#1864](https://github.com/moritzbrantner/formal-logos/issues/1864)
is fixed divine attributes, real-world modal admissibility, an actual
same-witness GOD_4 consumer, source fidelity and reviewed premise warrant.
Issue #437 still owns the separate Collin 2022 symmetry-breaker reading.

## Research attempts citing this note

- [Plantinga-style possibility helpers: non-impossibility, incompatible bundles, same-bearer profile](../../corpus/attempts/0719c77a-3bae-48dc-afa8-f9f36cbf848e.json)
