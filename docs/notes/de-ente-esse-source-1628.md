# De ente c.3: from received esse to one first being whose esse is its essence (#1628)

## Current reviewed assessment (2026-11-17)

The assembled case positively supports one necessary actual source conditional on the complete fixed-dictionary packages, and can carry that same source into the existence-only God consumer. The connected source reconstruction preserves positive constitutive support and the exact conditional source, composition, ascent and naming bundles. Root access, common ancestry, unique actual root and all-world underivedness remain distinct. Joint metaphysical applicability remains unresolved; separate controls do not supply a joint divine model.

Reviewed scope: Connected actual-source and uniqueness reconstruction with full foundation and GOD_4 interfaces. Worker `aa5dbf4`; independent reviewer `ac0ef321`
reported no findings on delivered head `03ec6bbbb18a8dbcae3e9451d18c6a55179b9e69`.
[PR #1741](https://github.com/moritzbrantner/formal-logos/pull/1741) is merged;
final CI passed. Review accepts the qualified synthesis only, with no premise
establishment or new formal validity claim. The review detail and integration
disposition remain in that PR body and existing #143.

Next test: Consume a defended same-relation foundation/source-access or uniqueness application from its existing owner, then reassess the complete same-witness attribute/naming route without upgrading actual rootness to all-world underivedness.

This current disposition supersedes the **pending review/publication** wording
for group #1729 below. Those passages are preserved as historical worker
handoffs, not outstanding integration work. It does not supersede arbitrary
earlier judgments, unresolved philosophical questions, or deferred owner scopes.
The canonical attempt's `current_assessment` carries this same bounded scope.

<!-- Historical research and worker handoff evidence follows. -->


**Status:** conditional formal results, one new root connection, and a
provisional judgment. Sibling of the #1629 note
[de-ente-extrinsic-source-1629.md](de-ente-extrinsic-source-1629.md), whose
step this note consumes. Source: Thomas Aquinas, *De ente et essentia*, pinned
Corpus Thomisticum witness `AQUINAS-DE-ENTE-C3-4` (passage `7070ccdd`), anchor
[69874]: c.3 in the Baur/Koch numbering of the witness, c.4 in the Leonine
numbering the issue cites (§§77–81 of the linked English translation). The
materialized text of capp. 3–4 was read in full before the claims were made.

Formal home: `TruthCore/Latin/Aquinas/DeEnte/EsseSource.lean`, results in
`TruthCore/Results/Aquinas/DeEnte/EsseSource/`, spec
`specs/de-ente-esse-source-1628.toml`, attempt `9f771edb`.

## The passage's order

After arguing that a quiddity can be understood without knowing whether it
exists ("possum enim intelligere quid est homo vel Phoenix et tamen ignorare an
esse habeat"), the passage concludes that esse is other than essence "nisi
forte sit aliqua res, cuius quiditas sit ipsum suum esse". It then argues that
such a thing "non potest esse nisi una et prima", from an inventory of the
ways anything is multiplied; concludes "in qualibet alia re praeter eam aliud
sit esse suum et aliud quiditas"; gives the extrinsic-source step (#1629); and
closes: "quia omne, quod est per aliud, reducitur ad illud quod est per se
sicut ad causam primam, oportet quod sit aliqua res, quae sit causa essendi
omnibus rebus, eo quod ipsa est esse tantum. Alias iretur in infinitum in
causis".

## The reconstruction (all zero-axiom; Comparator and NanoDa checked locally)

One profile (the shared q.3 a.4 `Profile`: `InAct`, `CausesIn` at `esse`,
`essenceOf`, `esseOf` in one `Principle` sort) and one witness throughout.
"A thing whose quiddity is its esse" is the represented identity
`esseOf x = essenceOf x`. The cause of being is `CausesIn` at esse, mode of
causing unspecified, tenseless (DEF-CAUSE-OF-PERFECTION); nothing here says
it is efficient.

| Stage | Result | Theorem | Inputs | Conclusion |
|---|---|---|---|---|
| (b) at most one | `860eae63` | `atMostOneEsseIsEssenceFromPlurification` | inventory `2495a71d` (sourced), shared nature `75b5b027` (OPEN), no difference `f13d1cdd` (sourced), no matter `38ed105c` (sourced), existing reception premises `6dfe01ab`, `7fcfcee8`, `14325c83` | at most one actual being whose esse is its essence `a576300f` (also sourced as stated) |
| (c) regress | `0807e653` | `distinctEsseHasEsseIsEssenceSource` | #1629 step `457698e4`, no infinite regress `fd12ad3d` (OPEN), excluded middle | every actual distinct esse descends from a being whose esse is its essence `3d01134d` |
| (a)+(b)+(c) | `5c904cf6` | `commonEsseIsEssenceSource` | `3d01134d`, `a576300f`, two actual beings `33f3c4c5` (OPEN, ordinary), `fd12ad3d`, excluded middle | one such n has no actual cause of its esse and heads a finite chain of actual causes of being to every other actual being `c35b1a5c` |
| (d) root, purity | `e6337182` | `rootPurityFromDeEnte` | the root-purity inputs of `dcea77db` with `457698e4` in place of the q.3 a.4 pair `be639b3f`/`61bd42e5` | existing `3b39e0ba` (on root routes) |
| (d) root, uniqueness | `c056ad5c` | `atMostOneActualRootFromDeEnte` | `457698e4`, `a576300f`, existing-in-act `0436de86`, esse-cause bridge `cb1cdea9`, excluded middle | any two actual concrete roots are the same (new statement, not on a root route) |
| controls | `04212a3f` | `esseSourceControls` | none | four interpretations, below |



**Stage (a), real distinction.** The intellectus-essentiae argument is not
formalized. It establishes, at most, that existence is not part of what is
understood in understanding a quiddity, i.e. a distinction in concept. In the
passage, the universal real distinction for "every other thing" is drawn
*from* stage (b). The composition follows that order: from at most one being
whose esse is its essence, every actual being other than it has
`esseOf ≠ essenceOf` (inside `commonEsseIsEssenceSource`). That is a real
distinction only if equality of the profile's represented principles is read
as real identity, as the q.3 a.4 profile does.
This does not use the circular route rejected in
[necessary-simple-plurality.md](necessary-simple-plurality.md#strongest-rival-and-the-exact-missing-defense):
stage (b) is not derived from the all-other-things distinction.

**Targeted challenge to the conceptual-to-real step** (Wippel's lead,
pp. 50–51 in the issue; not read for this note, attribution deferred). Target:
reading the intellectus-essentiae paragraph as by itself establishing a real
distinction. Mechanism: a quiddity's being intelligible without its existence
shows that existence is not included in the concept; it does not show that
esse is a principle really other than essence in the thing, since one reality
can be grasped under two concepts. Independent justification: the
concept/reality gap is the general one that blocks inferring real from
conceptual distinctness (the q.3 a.4 reply ad 2 likewise separates the act of
being from the truth that something exists). Relevance: if the real
distinction rested on that paragraph alone, `DistinctEsseAt` would be
unsupported as an input to stage (c). Status: accepted as stated, and avoided
rather than refuted: in this reconstruction the real distinction for all but
at most one being comes from stage (b), whose own open input is the shared
nature premise. The challenge therefore relocates the burden to `75b5b027`
rather than leaving a hidden conceptual-to-real inference.

**Stage (b).** The inventory, the exclusion of an added difference and of
matter are the passage's. The inventory is encoded only at the instance the
passage applies it to, two actual beings each of whose esse is its essence;
there the nature is esse, so the third mode, "one absolute and another
received in something", is the reception of esse. (A general version over
every nature with received esse in place of a received nature would be
stronger than the sentence and is not used.) It is excluded with three existing open
reception premises: a received esse is received in its own essence
(`6dfe01ab`, used on the strong version because the weak identity-scoped
version `b9316115` lives on a different Frame), a receiver is in receptive
potency to what it receives (`7fcfcee8`, sourced from the same chapter), and
nothing is in receptive potency to itself (`14325c83`). For a being whose
essence is its esse, a received esse would put that esse in potency to
itself. The indispensable analyst premise is `75b5b027`: two beings each of
whose esse is its essence share one nature. That is exactly the #697
`UNRECEIVED-ESSE-INDIVIDUATION-BRIDGE` gap: the passage treats "esse tantum"
as one nature without arguing it.

**Stage (c).** The reduction principle "omne quod est per aliud reducitur ad
illud quod est per se" is derived, not assumed. Here "per se" means only "not
having esse from another", read as a being whose esse is its essence; it is
none of the three senses of the per se disambiguation `002f42cb` (per se
ordered series, necessary per se, per se notum), and no record uses it as a
term. The derivation is by well-founded induction on
actual causes of being, a distinct esse has another actual cause (#1629's
`457698e4`); if that cause's esse is its essence it is the source, otherwise
the chain is extended. The two substantive inputs are the #1629 step and
`fd12ad3d`, well-foundedness of "c, in act and other than x, causes the esse
of the actual x". The passage presupposes a no-regress principle ("alias
iretur in infinitum in causis") for some order of causes of esse without
saying which; this unrestricted version is the analyst's. It ranges over every
cause of being, not only essentially ordered or simultaneous ones, so it is
stronger than an essentially-ordered regress premise.

**The composition.** From two different actual beings, at most one has esse
equal to essence, so some actual being has distinct esse and a source n. Any
actual being other than n has distinct esse (at most one), hence a source,
which at most one identifies with n. So one n whose esse is its essence heads
a finite chain of actual causes of being to every other actual being. An
actual cause c of n would itself be another actual being, hence descend from
n, closing a cycle that well-foundedness excludes; so n has no actual cause of
its esse. This is the passage's "causa essendi omnibus rebus" read as *first*
cause in that order (uncaused, heading every chain); that n directly causes
every esse is not derived. Without the uncausedness clause the chain
statement would not make n first: a being whose esse is its essence could be
caused in a cycle.

## Controls

- **Infinite regress** (Nat, n+1 causes the esse of n): the #1629 step holds,
  0 has distinct esse, well-foundedness and the regress conclusion fail.
- **Uncaused distinct esse** (Bool, no causes): well-foundedness holds, the
  #1629 step and the regress conclusion fail.
- **Two sources** (four beings; a and b each have esse equal to essence, a
  causes c, b causes d): every input of stage (b) except the shared-nature
  premise holds; every input of the regress and composition except at most one
  holds; at most one and the common source fail.
- **Nonvacuity**: a has esse equal to essence and causes the esse of b, c, d,
  whose esse is received in their essence; every input and conclusion holds.

These show which premises the conclusions need under the encoded predicates;
they are not evidence that an infinite regress, brute esse or two first beings
is possible. Excluded middle is not tested by a control.

## Root connection (computed)

`truth frontier-diff --base origin/main`: open premises reaching the root
477 → 480; distinct verified support alternatives 469 → 473. The purity
sibling gives `3b39e0ba` a support option through `457698e4`, so the #1629
chain now reaches the root: `457698e4` ← `d1f3ffcc` + `b62a64ab` + `4ccb319f`,
and `d1f3ffcc` ← `8592601e` + `a2800f45`, `8592601e` ← `75919560` + the OPEN
efficiency bridge `600f91cb` (newly reaching, bare). The new statements of
stages (b) and (c) do not reach the root.

**Interfaces** (1–3 built in #1635; see the next section).

1. *Root uniqueness.* Registered as `uniqueActualRootFromDeEnte` (`ef632140`).
2. *First source to actual root.* Registered as
   `deEnteFirstSourceIsActualRoot` (`ca5403a6`) with two explicit OPEN
   bridges, and composed into `7ab0ddcb` (`6e89d528`).
3. *Necessary concrete being.* Reached through the existing argument
   `70adaf7c` (`7ab0ddcb` + `c71c068c` + excluded middle → the unique
   necessary actual root `91b085c4`). The profile itself has no modal field;
   n's identity of esse and essence says nothing modal.
4. *Classical attributes.* Not touched. An underived first being of esse is
   not yet the classical God: simplicity, infinity, intellect, will and the
   divine name are separate routes; intrinsic adequacy (#1621) and
   conservation (#1616) are not assumed.
5. *Efficiency.* Nothing here concludes or feeds `33ad148b` or advertises an
   efficient cause. That route still waits on #1633.

## Rivals (Substantive Objection Standard)

| Account | Target | Mechanism and independent justification | Price under its own commitments |
|---|---|---|---|
| Brute actual esse (#312/#746) | `d1f3ffcc` under `457698e4` | An actual composite whose esse is not its essence has no cause of its esse; explanation stops there. Justification offered in the corpus: unrestricted PSR has recorded costs, and explanation must stop somewhere. | Stops at a composite rather than at a being whose esse is its essence, and owes a stopping criterion selecting it (#746). No internal contradiction shown (uncaused control). |
| Infinite or global derivative order (#311/#750) | `fd12ad3d` | Every actual distinct esse is caused by another distinct-esse being without end, or the whole order is explained structurally. Justification: infinite series are mathematically consistent, and grounding-structure explanations are used elsewhere. | Each member's esse is accounted for by another. The price that nothing then accounts for the obtaining of the whole order's esse holds only given the open local-to-global bridge (#311 EXP-LOCAL-TO-GLOBAL), not from the rival's own commitments; with that bridge, the rival must say what does, or accept the whole as brute (brute row at the level of the whole). Unpaid, not refuted (regress control). |
| Accidentally ordered infinite series | the scope of `fd12ad3d` | `fd12ad3d` covers every cause of being. Aquinas himself allows an infinite series of causes ordered per accidens (ST I q.46 a.2 ad 7), so the unrestricted premise is stronger than what his own regress arguments need. Relevance: if causes of being include accidentally ordered ones, an infinite chain of them is not excluded by Aquinas's own lights. | Not a rival account but a scope objection. Addressed in #1635 (next section): `fd12ad3d` is now derived from its per se version and a per se bridge; the objection moves to that bridge. |
| Two first sources (#697) | `75b5b027` | Two beings each identical with its esse differ as wholes, by primitive identity or two different whole essences, without being a multiplication of one nature. Justification: primitive numerical distinctness is a coherent position in individuation theory; the inventory's exhaustiveness is asserted, not proved. | Must say what distinguishes two pure esses that admit no addition (De ente c.4 [69875]: "per ipsam suam puritatem est esse distinctum ab omni esse"), and why that distinguishing factor is not an addition. The #697 audit records this as unresolved (two-sources control). |
| Merely conceptual distinction | `DistinctEsseAt` as input | See the targeted challenge above. | Rejects the antecedent of stage (c) when the real distinction is taken from the intellectus-essentiae argument alone; does not bite when it is drawn from stage (b). |
| Existential inertia (#1616) | none here | It concerns present sustaining. The relation is tenseless and covers originating causes; the first-source conclusion does not claim conservation. No separate objection identified. | — |
| Modal necessity of composites | none separately | A necessary being with distinct esse still falls under the #1629 step (or rejects it, brute/intrinsic rows). No separate mechanism identified. | — |

## Overall provisional judgment (2026-11-14)

**Claim.** If at least two beings are actual, there is one actual being whose
esse is its essence, with no actual cause of its esse, from which, through
finite chains of actual causes of being, the esse of every other actual being
descends.

**Judgment.** The inference from the passage's three stages is valid with
these inputs: the #1629 causal coverage of distinct esse (`d1f3ffcc`, with no
self-causation and the actuality of causes), no infinite regress of actual
causes of being (`fd12ad3d`), the shared-nature premise (`75b5b027`), the
inventory's exhaustiveness and the difference/matter exclusions (sourced, the
exhaustiveness contested), the three open reception premises (`6dfe01ab` in
its strong version, `7fcfcee8`, `14325c83`), at least two actual beings
(`33f3c4c5`) and excluded middle. The three contested ones are causal
coverage, the regress premise and the shared nature (with the inventory's
exhaustiveness); the claim is provisionally supported to the degree that they
are. Causal coverage and the regress premise carry the existence of a first
source; the shared-nature premise carries its uniqueness and, through it, the
universal real distinction. The strongest standing rival to the existence of
a first source is the global/infinite order, whose price is to account for
the obtaining of the whole derivative order or accept it as brute; the
strongest rival to its uniqueness is the two-sources account, whose price is a
non-additive distinguishing factor between pure esses. No rival is refuted
here; no premise is established.

**Would revise.** Downward: a worked account of a non-additive individuator of
pure esse; an account of the whole derivative order's esse that is neither a
first source nor brute. Upward: a derivation of the regress premise from a
weaker essentially-ordered regress principle, or of the shared-nature premise from an
account of esse tantum independent of uniqueness.

**Boundaries.** No efficiency, conservation, necessity, concreteness at a
world, divine attribute or God identification follows. An underived first
being of esse is not the classical God.

## Semantic challenge

An independent reviewer challenged the staged diff (not these conclusions).
Accepted and repaired: (1) "first cause" said more than the chain type (a being
whose esse is its essence could head a chain and still be caused in a cycle);
the common-source statement now includes that n has no actual cause of its
esse, derived from the regress premise, now an input of the composition. (2)
The inventory reading substituted received esse for a received nature over
every nature, which is stronger than the sentence; it is now encoded only at
pairs of beings whose esse is their essence. (3) "Per se" in the reduction
principle is now stated as "not having esse from another", outside the
existing per se disambiguation, and the regress premise's prose uses
"essentially ordered" instead. Also: "real distinction" is qualified as the
represented inequality; the "esse tantum" reading choices are stated in both
claims; the regress premise is the analyst's unrestricted version of a
presupposed principle; the infinite-order price is conditioned on the
local-to-global bridge; the judgment lists every input; the cause
disambiguations are linked on the stage (c) and composition arguments. No
disagreement was left unresolved.

## #1635: the root interface and a per se regress

Formal home: `TruthCore/Latin/Aquinas/DeEnte/RootInterface.lean`, results in
`TruthCore/Results/Aquinas/DeEnte/RootInterface/`, spec
`specs/de-ente-root-interface-1635.toml`, attempt `f41bcb00`. All results are
zero-axiom; Comparator and NanoDa checked locally.

### Sense links repaired (#1524 in part)

`5c898d24` (`WholeRosterNotTrapped`) and `7ab0ddcb` (`UniqueActualRootAt`)
linked definitions whose constants their Lean types do not contain
(`NecessaryAt`, `ContingentAt`, `NonnecessaryRootAt`, `GroundAncestor`,
`IsNecessaryPerSe`, the maximum, grade and `Escape` predicates, and others),
so every argument using them "used" both senses of NECESSARY, NONNECESSARY,
WELL_FOUNDEDNESS and INTRINSIC. Their `definition_ids` now name only the
constants of their types: `5c898d24` keeps its own definition, the Ontic
signature, `Groups`, `Graph`, CONCRETE_6 and the source-backed application
`f825624c` (INTRINSIC_2: the type instantiates `Trap`'s intrinsic parameter
with the graph `Source` predicate, the application that defines that sense);
`7ab0ddcb` keeps its own definition, `ActualRoot` and the Ontic signature.
The generic `Supply` definition `c9d479bb` (INTRINSIC_1, intrinsic *not*
graph sourcehood) is dropped from `5c898d24`; its `Trap` clause is now its own
definition `a8172538` (Codex review), linked instead. The two GOD_4 grades-at-being routes
(`fc46b7f9`, `3367bf93`) lose their bookkeeping bridges citing `5c898d24`;
91 argument allowlist entries that no longer fail are removed (30 of them were
already removable on main). The two legacy MAXIMAL senses stay listed although
`sense_index.py ratchet` calls them removable: the full bind-check uses them to
excuse a known IsMaximumIn/IsMaximalIn alias. The allowlist only shrank.

### Results

| Result | Theorem | Inputs | Conclusion |
|---|---|---|---|
| `ef632140` | `uniqueActualRootFromDeEnte` | population `56f68b40`, whole roster `5c898d24`, excluded middle, `0436de86`, `cb1cdea9`, #1629 step `457698e4`, at most one `a576300f` | root uniqueness `7ab0ddcb` |
| `ca5403a6` | `deEnteFirstSourceIsActualRoot` | first source `c35b1a5c`, `0436de86`, concreteness bridge `ad2b3ffc` (OPEN), ground bridge `17350d52` (OPEN), no self-causation `b62a64ab` | the first source is an actual root at w `ce7edf53` |
| `6e89d528` | `uniqueActualRootFromDeEnteSource` | `ce7edf53`, at most one actual root `49fdec01` | `7ab0ddcb` |
| `3e7d77b1` | `perSeRegressOfUnrestricted` | `fd12ad3d` | per se regress `ea251340` (strength order, relation `ed411e36`) |
| `a20cb04c` | `unrestrictedRegressFromPerSe` | per se regress `ea251340` (OPEN), per se bridge `e74de400` (OPEN) | `fd12ad3d` |
| `96c022f9` | `rootInterfaceControls` | none | controls `0b847841` |

**Interface 2, the two bridges.** The q.3 a.4 profile is world-free and
orders causes of being; `ActualRoot m w` is world-relative and orders
grounds. Both bridges are restricted to beings whose esse is their essence,
the only instances the route uses:

- `ad2b3ffc`: such a being in act is concrete and exists at w (a restricted
  converse of `0436de86`, with concreteness added). Because `InAct` does not
  depend on the world, accepting this bridge at every world rather than only
  at the selected w would make such a being exist at every world; that modal
  reading is not asserted, and necessity still comes only through
  `c71c068c` below. On the CONCRETE_6 reading of concreteness (having esse in
  re, `InAct x esse`) the concreteness half is close to definitional; the
  main content is existence at w.
- `17350d52`: an actual concrete ground at w of such a being causes its esse
  (a restricted converse of `cb1cdea9`). Given the first source's
  uncausedness, existing-in-act and no self-causation, this bridge at the
  source is equivalent to the source having no actual concrete ground at w,
  so it carries most of the weight of the rootness clause; the derivation is
  not a transcription, but its content is close to that clause.

The issue's further premise, "a being whose esse is its essence has no other
cause of its esse", is not needed: the first source's own uncausedness (in
`c35b1a5c`, derived from `fd12ad3d`) excludes every other actual cause, and
no self-causation `b62a64ab` excludes a self-ground. Neither bridge holds by
definition: `AbsentSourceControl` falsifies the first and
`NonCausalGroundControl` the second while every other input holds, and
`SelfGroundControl` shows no self-causation is needed. These are
interpretations of the encoded predicates, not evidence that such cases are
possible.

**Route effect.** `7ab0ddcb` now has a De ente support option with no
population or whole-roster premise: `c35b1a5c` (from `3d01134d`, `a576300f`,
`33f3c4c5`, `fd12ad3d`, excluded middle) with the two bridges, `0436de86`,
`b62a64ab`, and `49fdec01` (from `457698e4`, `a576300f`, `0436de86`,
`cb1cdea9`, excluded middle). The existing argument `70adaf7c` carries
`7ab0ddcb` with `c71c068c` to the unique necessary actual root `91b085c4`,
which reaches the root. So the whole #1628 stack (stages (b) and (c), the
shared-nature premise, two actual beings) now reaches the root:
`truth frontier-diff --base origin/main` gives open premises reaching the
root 480 → 489 and distinct verified support alternatives 473 → 482.

### The per se regress

ST I q.46 a.2 ad 7 (pinned passage `a34be6a3`, materialized and read) holds,
of efficient causes, that "impossibile est procedere in infinitum per se; ut
puta si causae quae per se requiruntur ad aliquem effectum, multiplicarentur
in infinitum", as with stone, stick and hand, or if "generatio huius hominis
dependeret ab hoc homine, et a corpore elementari, et a sole, et sic in
infinitum". A per accidens infinite series "non reputatur impossibile": the
causes "non teneant ordinem nisi unius causae", as with successive hammers,
or with men generating, who "habent gradum unum in causis efficientibus";
"accidit huic homini, inquantum generat, quod sit generatus ab alio". The
passage's criterion is that the causes are per se required for the effect,
at different grades, as against a multiplication of causes at one grade
whose being caused is accidental to their causing; the "inquantum generat"
clause is its gloss on the generation case. It speaks only of efficient
causes, and does not itself say that a generator causes coming to be rather
than esse.

Encoding: the per se link is a primitive `AsCaused c x` (c causes the esse of
x only as its own esse is caused; DEF `4bca086d`, appended to DISAMB per se
as PER_SE_5, with its relation to PER_SE_1 left open). It takes the
"accidental to its causing" side of ad 7's criterion and applies it, as an
analyst analogue, to causes of esse of unspecified mode. Two inputs replace
`fd12ad3d`:

- `ea251340`: no infinite chain of per se actual causes of being. It is
  weaker than `fd12ad3d`, which implies it for every per se link; strictness
  is witnessed by `PerAccidensRegressControl`, with an empty per se link. With
  `AsCaused` everywhere true it coincides with `fd12ad3d`, so how much weaker
  it is depends on the intended meaning of the primitive.
- `e74de400`: a caused actual cause of being causes being as caused, i.e. no
  actual cause of esse is accidentally ordered.

`fd12ad3d` follows by per se induction (`a20cb04c`); no matching restriction
of the #1629 step `457698e4` is needed, because the bridge transfers
well-foundedness back to every actual cause of being, so every consumer of
`fd12ad3d` keeps its form. The alternative, a #1629 step restricted to per se
causes ("every actual distinct esse has another per se actual cause"), would
be stronger than `457698e4` and is not stated. `PerAccidensRegressControl`
(n+1 causes the esse of n on `Nat`, no link per se) satisfies the per se
regress and `457698e4` while `fd12ad3d` and stage (c)'s conclusion fail: the
per se regress alone does not give the first source.

**Can a cause of esse be accidentally ordered?** That is now exactly the
content of `e74de400`. Two records pull in different directions. DEF
`8163859b` says `ActualEsseCause` is tenseless and "not a cause of coming to
be", so ad 7's generator, taken as a cause of the son's coming to be, is not
an `ActualEsseCause`. The #1628 existential-inertia row above says the same
relation "covers originating causes". An originating cause of x's esse that
was itself originated is the natural per accidens candidate, and nothing in
the encoding separates originating esse from causing coming to be. The bridge
holds if a cause of esse is one on whose own being its causing depends while
it causes (the cause-of-esse versus cause-of-becoming distinction of ST I
q.104 a.1, not pinned and not read for this note, attribution deferred): then
a caused cause of esse causes as caused. The tenseless encoding does not say
this, so the bridge stays OPEN and its warrant runs through that reading,
which is close to the conservation question of #1616.

### Rivals (Substantive Objection Standard)

| Account | Target | Mechanism and independent justification | Price under its own commitments |
|---|---|---|---|
| Per accidens causes of esse | `e74de400` | Some actual cause c of x's esse is itself caused, yet causes x's esse in virtue of what it is, not as caused; an infinite chain of such causes satisfies the per se regress and the #1629 step (`PerAccidensRegressControl`). Justification: the #1628 reading of the tenseless relation covers originating causes, and an originated originator is the per accidens shape ad 7 describes for generators; the encoding does not make causing esse depend on the cause's present being. Ad 7's own examples are efficient causes of making and generation, so they do not by themselves transfer to causes of esse. | Must name a cause of esse, not of coming to be (which DEF `8163859b` excludes), whose being caused is accidental to its causing: an originating cause of esse distinct from a cause of coming to be. On the cause-of-esse reading above, a cause whose causing does not depend on its own being while it causes. No such example is recorded; not refuted, since the reading that excludes it is not encoded. |
| Non-causal ground of the first source | `17350d52` | No substantive objection identified. `NonCausalGroundControl` shows only that the encoded predicates do not force the bridge; no specific non-causal ground of a being whose esse is its essence, with a mechanism, is recorded. Encoding gap: the grounding relation and `CausesIn` are separate primitives. | — |
| First source absent from the selected world | `ad2b3ffc` | No substantive objection identified. `AbsentSourceControl` shows only that the two profiles are separate signatures linked by `0436de86` in one direction. Encoding gap: `InAct` is world-free. | — |
| Infinite or global derivative order (#311/#750) | `fd12ad3d`, now `ea251340` and `e74de400` | As in the table above. | Unchanged; with the per se split, an infinite order of causes of being must either be per accidens (deny `e74de400`) or per se (deny `ea251340`, the analogue for causes of esse of what ad 7 rejects for efficient causes). |
| Two first sources (#697) | `75b5b027` | As above. | Unchanged; it now also denies `7ab0ddcb`'s uniqueness on the De ente route. |

### Provisional judgment (2026-11-14)

**Claim.** If at least two beings are actual, there is a unique actual
concrete root at w, and it is the being whose esse is its essence, which has
no actual cause of its esse and from which a finite chain of actual causes of
being reaches every other being in act.

**Judgment.** Valid with the #1628 inputs, three new OPEN bridges
(`ad2b3ffc`, `17350d52`, `e74de400`) and the per se regress `ea251340`. The
two root-interface bridges are restricted to the one kind of being whose
essence is to be, can each fail in the encoding, and face no recorded
substantive objection; their warrant is what one grants to the readings that
a ground of the existence of such a being would be a cause of its esse, and
that it exists at the world where it is in act. The bridge `17350d52` does
most of the work of the rootness clause. The per se split is positive
progress on the regress premise: the regress denial now rests on the per se
claim, which ad 7 supports only by analogy (it states it for efficient
causes), plus the explicit claim that causes of esse are never accidentally
ordered. That claim carries the weight the unrestricted premise carried and is
as strong as the cause-of-esse reading behind it; the support of `fd12ad3d`
through `ea251340` adds warrant only insofar as `ea251340` is held on its own,
not through its derivation from `fd12ad3d`. Strongest standing rival: per
accidens causes of esse (an originated originator of esse), price above. No
premise is established.

**Would revise.** Downward: an example of an actual cause of esse, distinct
from a cause of coming to be, whose being caused is accidental to its
causing; a non-causal ground of a being whose esse is its essence. Upward: a
pinned source and encoding of the cause-of-esse reading (causing that
depends on the cause's own present being) that would derive `e74de400`.

**Boundaries.** No efficiency (#1633), conservation (#1616), divine attribute
or God identification follows. Necessity at accessible worlds comes only
through the existing `c71c068c` argument. An underived first being of esse is
not the classical God.

**Next tests.** Derive `e74de400` from an explicit encoding of the
cause-of-esse reading, which also requires reconciling `8163859b` ("not a
cause of coming to be") with the "covers originating causes" reading; relate
PER_SE_5 to PER_SE_1 and `AsCaused` to the secunda via's `CausesAsCaused` once
#1633 supplies efficiency; finish
#1524 for the remaining arguments that carry over-broad definition links.

### Semantic challenge (#1635)

An independent reviewer challenged the staged diff. Accepted and repaired:
(1) the per se link was tagged PER_SE_1, whose definition and relations are
the prima via's sustained mover series and the secunda via's efficient
`CausesAsCaused`; it is now its own sense PER_SE_5 with its relation to
PER_SE_1 open. (2) The per se regress was called "the esse instance" of ad 7;
ad 7 speaks only of efficient causes, so it is now an analyst analogue, and
the passage's criterion (per se required, different grades) is stated in
full rather than narrowed to the "inquantum generat" gloss. (3) The rival
rows for the two root-interface bridges gave only non-analyticity as
justification; they are now recorded as "no substantive objection
identified", with the encoding gaps named. Also: `17350d52` is said to carry
most of the rootness clause; the latent modal content and near-definitional
concreteness half of `ad2b3ffc` are flagged; the tension between `8163859b`
and the "covers originating causes" reading is stated and feeds the per
accidens rival; the degenerate strictness witness is flagged; "heads every
chain" and "so provisionally plausible" were reworded; the module doc no
longer reads the controls as possibilities. The reviewer found the Lean
proofs, the controls, the strength order, the sense-link trimming
(INTRINSIC_2 only for `5c898d24`) and the removal of the bookkeeping bridges
correct. Codex review (P2) asked for a definition of `Trap` after `c9d479bb` was dropped: added as `a8172538`.

## Current source-selection judgment: identity and the nature being multiplied (2026-11-17)

**Target and registered route.** `75b5b027-21f1-400a-8b21-775bb6d47983`,
with the six companion inputs of argument `07b1fac4` / result `860eae63`,
supports at-most-one identity bearer `a576300f`, then common ancestor `c35b1a5c`,
fixed-esse maximal causality `da09703b` (argument `f4df2153`), and GodExists
(consumer `c98328f1`, result `d8cb586a`). The final connection is retained in
[maximum-definition-fork.md](maximum-definition-fork.md#current-existence-bundle-judgment-select-the-cause-before-identifying-the-maximum-2026-11-17).
This continuation changes none of those propositions or proof inputs.

**Reuse.** Required related/dossier/brief/novelty retrieval and context for
`860eae63` were inspected. Retained De ente/q11 source readings and exact
individuation, multiplication, reception, q7, pure-thisness and narrower
indiscernibility findings are in
[necessary-simple-plurality.md](necessary-simple-plurality.md#independent-individuation-audit-the-unresolved-exhaustive-step)
and its **Act limitation follow-up**, **Can primitive thisness distinguish two
pure acts?**, and **Narrower bridge** sections. No historical witness was
reacquired or freshly attributed. No recorded argument concludes `75b5b027`;
that is not an objection to accepting a primitive on its merits.

**Exact meaning.** `p.esseOf x = p.essenceOf x` identifies represented principles
within x; its real-identity application requires faithful maps. It entails no
cross-individual equality by logical form. `q.SharesNature x y` places both
candidates under one nature for the real multiplication account. This primitive
is not defined as essence-value equality, common predication, or x=y. Q11's
`ProperGodInstancesHaveCommonNatureReading` instead explicitly supplies
`essenceOf g = deity`; suppositum/nature agreement and an incommunicable
individuating basis are further inputs. Naming the candidates God cannot supply
those q11 premises or substitute that dictionary for the De ente relation.

**Strongest positive rationale.** On the substantive addition-excluding reading
of **esse tantum**, the whole what-it-is is its own subsistent act of being.
It is not merely a determinate nature that happens to exist. There is no
further quidditative content determining it to be one kind of existent rather
than another. Two such candidates therefore have the same what-it-is in the
relevant respect: subsistent esse itself. Their alleged plurality calls for a
multiplication account. The subsequent inventory/reception argument still does
work: shared nature alone does not exclude several instances.

This rationale explains why the account treats received natures differently.
A determinate essence explains why its actuality has one range rather than
another; on the act/reception account that essence determines the act it
receives, whereas esse actualizes it. If the whole essence is esse itself, a
different determinate kind needs an account of how esse is so determined without
a recipient or further quidditative content. This gives shared nature a
substantive prima facie rationale and permits its direct primitive acceptance.
It need not await an endlessly prior proof of every commitment. Its warrant
comes from the act/determination account, not the equality symbol.

**Application and provisional judgment.** The rationale favors `75b5b027` when
these same candidates instantiate addition-excluding unreceived esse. The
identity maps alone do not encode that whole-nature determination must arise
from reception or addition. The sourced no-difference reading `f13d1cdd`
excludes a differentia added to esse; it does not identify every difference of
whole natures with an added constituent. The existing q7 audit tested the
missing converse from whole-nature difference to real reception; its
received-created-form account does not supply it. Thus retain shared nature as
a positively motivated primitive within this account, without claiming its
application has been derived from the companion premises. The equality-only
argument is insufficient. No substantive defeat of the stronger
addition-excluding account has been established by this continuation.

**Distinct-whole-nature reply.** A proposes an intrinsic act of one kind and B
an intrinsic act of another, neither receiving a common act in a distinct
subject. Their intrinsic characters explain different causal powers and the
recipients they support. This is a distributed-source explanation schema,
challenging the step from qualitative determination to a further receiver or
added constituent. It has a specific positive basis against the *generic*
composition shortcut: the source account itself allows immaterial species whose
genus and differentia are taken from the whole quiddity, not separate actual
parts. Whole difference does not automatically exhibit an added real part.

The relevant difference matters: those immaterial natures have esse other than
essence in the same account. Their mechanism does not independently establish
intrinsically typed **unreceived** esse. The inspected records supply no such
application. The rival is therefore a targeted challenge to that inference and
an unfinished alternative ontology, not evidence of actual distinct identity
bearers or a metaphysical possibility proof. Its proponent owes a positive
account of intrinsic determination compatible with esse tantum; the defender
must justify excluding that account rather than appeal to the absence of a
worked rival. TwoSourcesControl establishes omission dependence only. The
older rival table's appeal to coherent primitive individuation is not additional
evidence for its extension to unreceived esse.

**Bare thisness and natural sources.** A proponent can accept common nature but
posit two instances without differentia, matter or reception. That challenges
inventory `2495a71d`, rather than automatically negating `75b5b027`. Denying that
qualitative sameness places them under a genuinely shared nature challenges
this premise's application instead. Keep the replies distinct. The predicate
"is identical with A" supplies no real individuating mechanism. Existing
pure-thisness/indiscernibility results already test the real-determination and
bare-difference options; no independently supported bare-thisness counterexample
to addition-excluding unreceived esse was identified. Its absence is not proof.

Naturalism does not decide this dispute. Several intrinsic basic natures would
need the differentiated-act account above; one fundamental natural supporter
could satisfy source selection. Neither a naturalist label nor a finite graph
establishes the relevant actual ontology. The coherence of a common-nature
metaphysics is positive comparative evidence, but its conditional consequences
are not independent corroboration through a proof cycle.

**Preserved dependencies.** Shared nature supplies no existing bearer or causal
coverage. Keep the multiplication inventory, no-difference/no-matter readings,
own-essence reception, receiver-to-act potency and no-self-reception inputs.
Common ancestry retains its source/coverage, numerical-selection, population
and no-regress inputs. The maximal bridge retains composition, ascent and
explicit logic. The twelve-input consumer retains all its actuality, grounding,
priority, grading, transfer, component and nominal interfaces. The profile is
tenseless and mode-unspecified: present productive support, conservation,
necessity, intellect, further divine attributes and Catholic identification are
not supplied by this investigation.

**Resolved scope and reopening.** Equality-only and genus/difference composition
shortcuts are exhausted by the retained evidence. An implication assuming all
identity bearers lack different whole natures, a common numerical esse, or
complete unrestricted perfection would relocate this gap; the corpus already
retains those frameworks. Another model or equivalence certificate would not
test their real application, so none is added. Reopen on a positively warranted
intrinsically differentiated unreceived-act account, or a general argument
that such determination requires real reception/addition answering the
whole-quiddity reply. Bare multiplicity accepting common nature belongs to
`2495a71d` and the existing indiscernibility investigation.

Recommended next allocation: existing causal-ascent input `cffad050`. Its
reception-limit argument `fa1d11a9` / result `d9958e2c` moves from the cause's
not being limited **by this recipient** to exceeding the recipient in esse.
Test that inference when the cause is limited through another recipient, and
whether the selected respect supplies the comparison. This is a concrete
warrant question for the source-first identification, distinct from common
nature; do not infer global unlimitedness from absence of one recipient.

**Self-sweep and evidence.** Proposition, Lean interpretation, definitions,
senses, proofs and frozen Challenges are unchanged. The statement paraphrase
now links this positive assessment and distinguishes rival mechanisms from
controls. No source claim, attribution, status, new primitive or warrant axiom
is created. Reuse accepted build/binding/Comparator/NanoDa evidence; no unchanged
proof was reverified. This is non-proof work: exact premise change **none**.
Affected final checks are offline corpus/attribution validation and the computed
God-root frontier comparison against `059009b39d2e4665a4d9ab3c898850ba3b89271d`.
Live convention source revision: `15f348b072188255da837578eaafc8a98f12fdf0`.
Fresh independent semantic review of the complete proposed judgment precedes
publication; this worker has not pushed, opened a PR or watched one.

Final affected checks passed: `target/release/truth check`, offline
`target/release/truth attribution-check --base 059009b39d2e4665a4d9ab3c898850ba3b89271d`
(no changed stating claims), and `git diff --check`. Computed with
`target/release/truth frontier-diff --base 059009b39d2e4665a4d9ab3c898850ba3b89271d --frontier-root STMT-GOD-EXISTS`:
**no change**; 404 open premises (283 bare, 76 supported, 45 stated), 415 distinct
verified alternatives, zero added alternatives, cheapest expanded diagnostic
cost 6, all unchanged. These counts describe the formal comparison, not the
merit of the current warrant judgment.

### Q11 allocation reconciliation (2026-11-17)

Read the accepted intellect-lane stopping recommendation at `85159977`
(`docs/immaterial-intellect-reception.md`) and retrieved related/dossier/brief/
novelty/context for its suggested `0730d46f-4604-5750-9a64-de664f064b31`.
The exact existing consumer `Q11NatureUniqueness.godIsOneFromNature`, result
`841e7c81`, uses numerical common nature, suppositum/nature identity and
incommunicable individuation jointly. Its at-most-one conclusion supplies no
existence. The q11 premise has an existing whole-case consumer `d6e5072d`;
it is not presently a support input to the GodExists route selected here.

This is **overlapping warrant, different propositions**, not a distinct new
source-selection argument. Q11 says `IsGod g → essenceOf g = deity`; `75b5b027`
says actual esse–essence identity bearers stand in primitive `SharesNature`.
Each individual's `esseOf = essenceOf` is neither cross-individual numerical
nature equality nor suppositum/nature identity. Q11's source reading and
conditional proof are retained, without treating common predication as one
numerically real nature or repeating the accepted individuation audit above.

To use q11 for `75b5b027`, one would need to place the same actual identity
candidates under the proper IsGod predicate, align their essence representations,
and justify nature-value equality implying the multiplication relation. The
first step would import the pre-naming source-identification obligation being
investigated here. Conversely `75b5b027` does not supply q11's one deity value:
it needs proper-God-to-actual-identity applicability and a bridge from the shared
multiplication relation to numerical essence equality. Choosing a deity value
from an already existing candidate would not prove such a candidate exists.
No logical equivalence or global strength order between the two is inferred.

The intended full God-description could provide additional content for a
numerical-common-nature defense, but no new discriminatory content or bridge
was delivered by the intellect stopping recommendation. Its own provisional
scope is respected. Until such content answers the retained different-whole-
nature/individuation question, q11 is not independent corroboration of this
source-selection premise. Do not dispatch a duplicate investigation of the
accepted shared-nature assessment on this recommendation alone. Reopen on a
newly warranted candidate-domain or real-nature bridge; keep the current
ascent/degree test as the distinct next input. Director descent/termination
still supplies no new cognition inference, and no intellect/UI record is edited.

## Unreceived esse and the two questions about plurality (2026-11-17)

**Target and scope.** Shared nature `75b5b027-21f1-400a-8b21-775bb6d47983`,
multiplication inventory `2495a71d-81b6-47b7-8394-b37d3308fcda`, and their
existing uniqueness result `860eae63` to `a576300f`.
The owner's proposed argument concerns the way a determinate essence receives
or limits esse. It should be retained as a positive metaphysical argument,
not dismissed because `esseOf x = essenceOf x` lacks a logical equality rule
between x and y. Conversely, the claim that essence numerically individuates
every thing is too broad: the same human nature is shared by several humans
in Aquinas's account, with designated matter accounting for their numerical
multiplication. Qualitative determination and numerical multiplication require
separate treatment.

**Reuse.** Re-read `EsseSource.Plurification` and its uniqueness inputs,
[necessary-simple-plurality.md](necessary-simple-plurality.md), especially
its whole-quiddity, q7, pure-thisness, narrow indiscernibility and whole-power
sections, and the q11 reconciliation immediately above. The existing result
`860eae63` supplies the De ente conditional; no replacement theorem is needed.
Public Latin *De ente* [69872], [69874], *SCG* I.17 nn.6–7 and I.24 nn.2–4,
and *ST* I q.3 a.4 ad 1 / q.11 a.3 were also read as orientation. The added
I.24 comparison is an analyst reconstruction, not a newly attributed corpus
claim or newly verified proof.
Canonical context for `860eae63`, related/dossier/brief for `75b5b027`,
dossiers for the multiplication and broad reception premises, and a combined
novelty search were inspected at baseline `c1037682`. This is retrieval and
reuse, not a new certification. No missing issue-snapshot hit is evidence that
an investigation is new.

### 1. Could the two candidates have different whole natures?

The strongest version starts from **addition-excluding subsistent esse**:
the whole what-it-is is its unreceived act of being, not a finite kind with
the further property of existing. This is the first sense of no-addition in
*ST* I q.3 a.4 ad 1. It differs from the abstract concept of being, which
leaves further determinations unspecified. Treating God as an indeterminate
universal would therefore miss the argument.

On the act/reception account, an essence that makes an act one determinate
kind supplies the recipient or limit of that act. If this determinant is
really other than the esse, the candidate does not satisfy the proposed
identity. If it is just that same unreceived esse, naming it “essence A”
has supplied no additional differentiating content. The question for “esse
of kind A” versus “esse of kind B” is what makes either act contracted to
its kind while preserving the claim that nothing other than unreceived esse
constitutes it.

*SCG* I.24 [23733–23735] gives supporting reasoning, rather than merely
restating no difference: an added essential determinant would be required
for the candidate's actuality; an intrinsic determinant belongs to the whole
essence or to a part of it. Given esse–essence identity, a **further**
determinant cannot be the whole essence; as a part it introduces composition.
The chapter also invokes the already argued absence of dependence and potency.
This supports the addition-excluding reading under those commitments. It
does not derive simplicity from the identity equation, and it does not silently
turn every difference between whole natures into an added part.

That restriction is source-sensitive. *SCG* I.17 nn.6–7 explicitly distinguishes
diversity of wholes from difference through further differentiae. Likewise,
the De ente treatment of immaterial species does not require genus and
differentia to be separate actual parts. These are genuine objections to a
generic composition shortcut. They are not a worked account of multiple
unreceived acts: the immaterial species in *De ente* still have received esse
distinct from their essence. The adequate extension would explain how a whole
is intrinsically a restricted kind of esse without a recipient, added essence
or dependence. Neither a two-value essence map nor the word “primitive”
supplies that explanation.

**Judgment on `75b5b027`:** the owner's proposal supports the strong
esse-tantum reading already favored above. Its warrant is the general account
of act, determination and reception; it may be accepted on those merits as a
primitive. No inspected substantive rival defeats it at the intended domain.
The current Lean identity by itself still does not express all of that content,
so no existing premise has silently acquired a stronger definition or a new
proved status.

### 2. Could there be two numerically distinct instances of that same nature?

Shared nature leaves this second question. The retained De ente argument
has a complete conditional answer:

1. A multiplication of the relevant nature requires an added difference,
   distinct matter, or reception (`2495a71d`).
2. A candidate whose whole nature is subsistent esse admits neither an added
   difference (`f13d1cdd`) nor matter (`38ed105c`).
3. On `6dfe01ab`, any recipient of its esse is its own essence. On
   `7fcfcee8`, that recipient is in receptive potency to the received act.
4. Essence–esse identity would make such reception potency to itself,
   excluded by `14325c83`.
5. The inventory therefore leaves no way to multiply two such candidates;
   `860eae63` proves that they are one under these same inputs.

**Reception-scope qualification.** The existing theorem retains the broad
all-bearer own-essence premise `6dfe01ab`. Its dossier includes the specific
united-soul/body interpretation challenge, not an unconditionally certified
refutation: see [esse-reception-definition-fork.md](esse-reception-definition-fork.md).
That investigation already supplies the strictly weaker identity-scoped law
(`9882d958`) and an infinity consumer. Here the local reasoning also applies
own-essence reception only to candidates whose esse is their essence. This
gives a principled scope for the philosophical defense; it does not make the
broad law true or silently replace it in `860eae63`. A formally checked
De ente consumer of the scoped law would be a separate narrow follow-up,
not additional warrant for the law itself. The known soul/body case must be
answered on its selected reception sense, not arbitrarily excluded by a label.

This shows exactly where the owner's point does work: a genuinely distinct
receiving/individuating principle is incompatible with the chosen identity,
and calling that principle “the essence” does not repair the incompatibility.
The positive reason for the inventory is that duplication of a received act
has distinct recipients, while qualitative contraction has a determining
principle. Nothing in an unreceived act supplies either kind of multiplication.
Rejecting this general account is a substantive option; presenting two
unconstrained names is not independent evidence for it.

The inventory carries the anti-bare-multiplicity commitment. The existing
pure-act routes display this explicitly rather than using universal identity
of indiscernibles unnoticed. `REAL-THISNESS-FIRST-MOVER-UNIQUENESS`
(`ef204e94`) excludes a **real** individuating determination when strict pure
actuality makes it pure and unrestricted perfection makes it common to every
candidate. `PERFECT-BEINGS-FIRST-MOVER-UNIQUENESS` (`890c1ef2`) instead uses
the scoped SCG I.42 perfect-being identity principle. The narrow
indiscernibility route allows ordinary cases of located, received things;
it still needs a general account of why bare multiplicity cannot occur among
unrestricted acts. These are existing conditional alternatives with explicit
applicability burdens, not proofs that “different” entails “composite” in
every ontology. They neither produce a bearer nor automatically discharge
De ente's different shared-nature premise.

**Relational safeguard.** The target is several subsisting acts of being or
absolute first substances. It is not the denial of every real distinction
within one numerical nature. A relational distinction must keep its relata
and its mode of subsistence explicit; neither a bare extrinsic description nor
the mere word “relation” establishes two independently subsisting esses.
The Thomistic treatment of subsistent relations therefore cannot be erased
by an unrestricted “all real difference is an added absolute part” rule.
Nor does it by itself furnish plural divine substances. This continuation
introduces no new such rule and does not change the candidate carrier.

### Overall provisional judgment, route and stopping point

The source-backed essence/reception argument is stronger than the earlier
question's wording suggested. Under the substantive esse-tantum and
multiplication account, different essential kinds would require a determination
incompatible with unreceived esse, and numerical duplication would require a
recipient or another allowed multiplication basis. The existing proof then
establishes uniqueness **conditionally**. The controls locate the encoded
premises it uses; they do not give an equally supported ontology of two pure
esses. No independently warranted application of bare thisness or intrinsic
whole-kind diversity to this domain was found in the inspected evidence.
That absence is not a proof of impossibility, and primitive acceptance of
the act/reception account does not require a further independent proof of
every commitment.

The distinction from the intrinsic-necessity reply matters. Essential or modal
necessary existence is weaker than addition-excluding unreceived esse;
granting a necessary being alone does not activate this uniqueness argument.
If an alternative grants the stronger characterization, it should be tested
against this bundle, not protected by retreating to the weaker description.

Keep the route visible: `75b5b027` with its six companion inputs gives
`a576300f`; existence and causal coverage with no-regress `fd12ad3d`
(`5ab6cc2b`) or closed-collection CCR (`3de4bd49`) then give common source
`c35b1a5c`. Existing composition/ascent with explicit logic gives fixed-esse
maximal causality `da09703b`, consumed by `c98328f1` / `d8cb586a` on the
GOD_4 existence route (main also has the witness-retaining consumer
`d9ee967a`; see [#1731 slice 2](#a-god_4-consumer-that-keeps-the-de-ente-witness-1731-slice-2-2026-11-18)).
The classical-root identity `8e3b89c9` takes its uniqueness from the
fixed-esse maximum, not from `860eae63`; see
[same-witness identities](#same-witness-identities-for-1731-2026-11-18) and
[uniqueness packages](#uniqueness-packages-on-the-same-candidate-roots). Neither shared nature nor this at-most-one result
supplies population, universal causal scope, the nominal bridge or later
divine attributes. Do not derive unrestricted perfection through an already
unique universal source and then cite it as independent support for selecting
that source.

**Next test / stop:** any continuation must specify a positive mode of
intrinsically differentiated unreceived esse, or defend the general
determination/reception or multiplication account at precisely that domain.
The two numerical and qualitative questions must remain separate. A further
equality lemma, a label-only two-source model or repetition of the same source
sentence will not settle real application. The distinct causal-ascent/degree
question already allocated above remains the next nonduplicative route input.
No definitions, interpretations, statements, graph edges, source claims or
proofs are changed here. Existing proof evidence is retained; the new source
comparison and provisional judgment are prose, not certification.

**Integration review (2026-11-17):** fresh independent semantic challenge of
this dated continuation and the coordinator conclusions found no substantive
defects; no repair round was required. This supersedes the pending-review
wording of this section only; main's #1729 and #1731 dispositions are
unaffected. See the [integration record](unique-feedback-explanation-311.md#reviewed-owner-reply-integration-2026-11-17)
for verification, source scope and unchanged formal status.

## CCR transfer (issue #1639)

**Complete proposed outcome for fresh semantic challenge (2026-11-17).**
The fixed actual esse-cause order admits a weaker conditional route to the
existing `CommonEsseIsEssenceSource` (`c35b1a5c`). It uses closed-collection
rootedness (new application `20babef7`), distinct-esse causal coverage
`457698e4`, identity-bearer uniqueness `a576300f`, one actual bearer
`78cffb8e`, and explicit excluded middle `ee4ab504`. It needs neither
unrestricted well-foundedness `fd12ad3d` nor global asymmetry. The existing
well-founded route, direct assumption options and source-scoped ascent route
remain available. No philosophical premise is established by this transfer.
Verification results and the computed God-root delta are recorded below;
independent semantic challenge and integration remain coordinator-owned.

### Fixed dictionary and exact reuse

Baseline: `766c3c08fa0bbf1486b9ff277f5870ecbaa94c95`. The issue and comments
were reconciled with main: #1635's interfaces are already delivered in
`RootInterface.lean`, including `ca5403a6` and `6e89d528`; its remaining
caused-cause/per-se application is explicit. This slice changes none of those
interfaces, the accepted foundation judgment, or the shared CCR library.
Required context/dossier/related/brief/novelty retrieval reused the existing
De ente attempts `9f771edb` and `f41bcb00`, CCR attempts `14fb7669` and
`4da08bd8`, and the recent `5c898d24` assessment in
[the foundation note](unique-feedback-explanation-311.md#current-foundation-judgment-on-the-existence-only-case-2026-11-17).

Fix **one** q3a4 profile p, bearer domain, esse respect and represented essence
and esse functions. Write `r c x := ActualEsseCause p c x`: c differs from x,
both are in act as to this same esse, and c causes x's esse. This remains the
tenseless, mode-unspecified cause of being. The adapter `esseCauseGraph p`
places exactly r in the existing graph's supplier-to-recipient `grounds`
field; both its existence and concrete guards are exactly `InAct x p.esse`.
Its single index is bookkeeping. This gives no equality with any independently
supplied world-grounding profile, present sustaining, efficient cause, or
constitutive explanation. Structural reuse of the graph API is not warrant
for such an identification. Definition `23ae8d63` records this application.

The key reusable theorem is
`TruthCore.Results.Causality.ConcreteRootAccess.accessOfClosed`
(result `7637c090`), already on main. It derives finite directed root access
from CCR and explicit EM. Its `RootAccess` retains actual endpoint guards and
supplier-to-recipient direction; it does not use undirected components.
`sourceOfAccess` in the new De ente Solution only interprets that existing
witness in p's esse dictionary. No generic graph, set, component, root-existence
or ancestry machinery is added.

### Why each local source is the same uncaused source

For any actual x, its **full finite-predecessor cone** is the predicate
`Sx y := InAct y esse ∧ (y = x ∨ TransGen r y x)`. “Finite” qualifies each
path, not the cone's cardinality. It contains x. If y belongs and r c y,
then c is actual and belongs: use the single edge when y = x and prefix
that edge to the existing finite path otherwise. Thus it is closed under
**every** actual esse predecessor, not only one chosen chain. CCR and EM
force an uncaused actual n inside this cone. The imported universal-access
theorem gives exactly this root-reaching consequence, using the equivalent
closed predicate of actual bearers without finite root access, rather than
rebuilding the cone construction here.

If n had distinct represented esse, `457698e4` would give another actual
cause of its esse, contradicting roothood. EM therefore makes n an identity
bearer. For distinct-esse x the zero-edge case n = x is impossible; this
recovers `EveryDistinctEsseHasEsseIsEssenceSource` (`3d01134d`) in result
`109e22e1`, without uniqueness or population. For the common-source result
`c6d92415`, select one actual bearer and its root n. Apply the same access
result to **each** other actual bearer y. Coverage makes its root n' an
identity bearer, and `a576300f` identifies n' with n. With y different from
n the resulting path is nonempty. The initial root witness already makes n
uncaused; the old composition's well-founded cycle-exclusion argument is
unnecessary. Dependent cycles can remain below n.

Only one actual bearer is needed. Result `51d52108` derives this population
from the old two-bearer input as its sole premise; a registered strength
comparison retains both. Result `044974e5` likewise imports
`ClosedGroundingRoots.closedRootedOfWF` after restriction to actual bearers,
registering `fd12ad3d` as stronger than the new CCR application. The existing
`commonEsseIsEssenceSource` and `distinctEsseHasEsseIsEssenceSource` Challenges
are unchanged. The new route concludes their existing endpoints directly.

### Exact controls and rejected shortcuts

Control result `b49b53e7` reuses the existing `limitGrounder`, `rootedCycle`
and `mediateFoundation` **relations**, interpreting them in the same q3a4
form throughout each control: every bearer is actual, only `none` has esse
identical to essence, and actual cause adds the existing nonidentity guard.
These are interpretations of the predicates, not metaphysical possibilities.

- A root directly causing every `some n`, alongside the edges
  `some (n+1) → some n`, satisfies CCR, causal coverage, identity uniqueness,
  population and the common-source endpoint while unrestricted WF fails.
  There is a finite path from the root to each bearer despite an infinite
  backward path that never chooses the root. Source existence prohibits
  neither every infinite path nor every infinite branch.
- A root directly causing two mutually causing dependents satisfies the
  same input bundle and endpoint. CCR permits this dependent cycle. It
  does not permit a cycle containing the unique identity root under the
  retained coverage/uniqueness bundle: the selected identity root is uncaused.
- An **isolated** identity root beside a pure successor regress has a root
  somewhere, causal coverage, identity uniqueness and two actual bearers,
  but lacks CCR and common ancestry. The regress's full predecessor cone
  contains no root. This defeats the shortcut from whole-roster root
  existence to a common source. It is not a foundation through infinitely
  many intermediaries: that interpretation needs additional structure.
- A singleton has one actual bearer without two distinct actual bearers.
  It witnesses strictness of the population weakening, not a populated
  nontrivial derivative order.

Rejected: substituting undirected connectivity for directed ancestry;
assuming the whole roster's root lies in every local cone; reusing the old
common-source theorem with only its WF premise deleted (its proof uses WF
a second time to exclude a cycle through the source); excluding every
infinite path; and adding a per-se or borrowedness flag as though its name
supplied application warrant. The new proof instead uses the existing exact
root-access theorem and the root's actual incoming-edge exclusion.

### Applicability and overall provisional judgment

The strongest positive rationale is the existing borrowed-actuality account:
if each supplier's actual existential contribution is genuinely received,
merely organizing those contributions does not originate their collective
availability. This motivates a nonborrowed source, and supports applying the
same demand to a closed local predecessor collection when **all** relevant
suppliers of its members are included. It is a defensible direct primitive
option and need not await an endlessly prior independent proof. CCR avoids
WF's extra ban on root-backed infinite paths and cycles; the controls show
why that surplus is unnecessary for this endpoint.

The actual application remains substantive. `457698e4` says distinct esse
has another actual cause; it does not by itself say that each cause supplies
its recipient's complete existential actuality, that its exercise is
borrowed, or that the selected relation lists every relevant supplier. The
adapter excludes self-causes and nonactual relata exactly as `ActualEsseCause`
does. Applying a principle over **all** suppliers requires explaining why
omitted self, non-bearer, nonactual or differently typed explanations do not
supply the actuality at issue, or how the chosen supplier relation covers
them. The existing no-self-cause and actual-cause arguments can contribute
to that defense; no extra exclusion is inferred from the adapter. Within
this graph the supplier-concreteness side condition of
`closedRootedOfBorrowed` is automatic from the actual-bearer guards. That
formal fact does not establish real supplier completeness.

If the borrowed-actuality argument is defended only for **per-se** causes,
its transfer needs a faithful relation/coverage bridge at that scope.
#1635's `AsCaused` and `CausedEsseCauseCausesAsCaused` record the distinction:
a cause's being caused is essential to its causing, rather than accidental.
They are not assumed here, and neither efficiency nor present sustaining is
silently imported. A proof only about a restricted per-se subrelation must
also explain how it yields an uncaused source and coverage in the retained
full actual esse-cause relation. The existing per-se-WF-plus-bridge route
remains one explicit option; this CCR result does not independently warrant
its bridge. The attenuation route is also unchanged: uniform loss and a
common bound are not independently justified for this mode-unspecified esse
relation by the present evidence.

The strongest matched rival is the existing complete distributed infinite
order: actual distinct-esse bearers obtain through a uniform constitutive or
productive organization, each fully supported in that same existential
respect, without a finite path to an independent r-source. A global
obtaining fact is either explained by an independently specified structure
or retained primitively. Uniform explanation and the existing fixed-point
controls give a positive reason to investigate this account; mathematical
consistency or unique determination alone does not realize actual esse.
Conversely the foundation account owes an obtaining source and an actual
support account, not merely a root label. The rival's primitive global
actuality cannot be rejected just for being primitive when the source account
also retains primitives. Its precise burden is its same-relation realization
and global explanation, not an assumed contradiction of CCR. An irreducibly
actual natural whole in the selected roster can itself be a root and satisfy
this foundation step; whether it satisfies identity-bearer coverage,
uniqueness and the later divine-naming bundle is a further question. No
artificial theism/naturalism equivalence or rival defeat follows.

**Proposed judgment:** modestly favorable **conditional** support for CCR in
a genuinely exhaustive, existentially supplying per-se interpretation,
reusing the earlier borrowed-actuality assessment. The successful transfer
removes unnecessary structural demands and improves the available support
options for `c35b1a5c`. It supplies no independent new corroboration of the
collective-availability premise, and the broader mode-unspecified tenseless
application remains OPEN. Neither the complete-order rival nor the positive
primitive is defeated. Reopen application on an independently specified
full-support realization at this exact relation/scope, or a positive argument
for collective non-generation and supplier coverage here. Reopen a per-se
restriction on a checked restricted-to-full causal bridge. Another equivalent
cut/source/borrowing presentation alone would not discriminate those options.

### Root connection, claim/type sweep and verification

The new common-source argument retains the existing endpoint and onward
bundles: `c35b1a5c → f4df2153 → da09703b → c98328f1 → 8626f8a5`.
Each arrow names an existing argument or endpoint, **with all its companion
premises**. The source-scoped ascent sibling remains an alternative. No
transfer from CCR in some unrelated world-grounding profile is asserted.
Causal ascent, composition, maximum existence/firstness, remoteness and the
GOD_4 naming bridge retain their own content and warrant burdens. Historical
Catholic evidence is deferred.

Self-sweep: the new CCR statement expands to the existing closed-collection
predicate on the exact guarded adapter; the population statement is one
actual bearer; all five common-source hypotheses bind explicitly. Finite
access permits zero steps only at the root, and `TransGen` to any distinct
target is nonempty. Uncausedness excludes exactly distinct actual esse
causes, not all explanations or self-causation in another relation. The
identity is represented `esseOf = essenceOf`, with the inherited real-identity
application; no necessity, efficiency, conservation, direct universal cause
or divine attribute is smuggled into it. Strength comparisons have one
premise each. Controls witness exactly their stated interpretations. No
source, passage or attribution claim is introduced or expanded. Their
philosophical application and the proposed warrant judgment remain separate
from formal verification.

Computed comparison (running CLI rules on base data; no hand-reconstructed delta):

```text
premise delta for GOD_4 exists: there is something that is GOD_4, in the sense of the GOD_4 of classical theism [8626f8a5]: 766c3c08fa0bbf1486b9ff277f5870ecbaa94c95 -> working tree
open premises reaching the root: 413 (284 bare, 78 supported, 51 stated) -> 414 (285 bare, 78 supported, 51 stated)
expanded-route diagnostic (lowest cost): GOD_4 exists: there is something that is GOD_4, in the sense of the GOD_4 of…, from prima via [ed7c588a] (cost 6) -> GOD_4 exists: there is something that is GOD_4, in the sense of the GOD_4 of…, from prima via [ed7c588a] (cost 6)
distinct verified support alternatives: 423 -> 426
verified support alternatives added: 3
  Closed actual esse collections contain an uncaused bearer [20babef7] <- There is no infinite descending chain of actual causes of being [fd12ad3d]
  Every actual distinct esse descends via actual causes of being from one whose esse is its essence [3d01134d] <- Closed actual esse collections contain an uncaused bearer [20babef7], Every actual distinct esse is caused by another being in act, mode of causing unspecified [457698e4], Excluded middle as a general principle: every proposition either holds or does not hold [ee4ab504]
  One being whose esse is its essence is a first cause of being of every other actual being [c35b1a5c] <- Closed actual esse collections contain an uncaused bearer [20babef7], Every actual distinct esse is caused by another being in act, mode of causing unspecified [457698e4], At least one actual esse bearer [78cffb8e], At most one actual being has its esse identical with its essence [a576300f], Excluded middle as a general principle: every proposition either holds or does not hold [ee4ab504]
bare premises added: 1 (listed for visibility; not a regression, owner decision 2026-11-07)
  At least one actual esse bearer [78cffb8e]
added (bare): 1
  At least one actual esse bearer [78cffb8e]
```

This adds conditional support options, with one-bearer population explicitly
visible. It establishes no premise and changes no root-closure rule.

Focused Solution and new frozen Challenge builds pass under the shared heavy
lock. Binding reports **5 bound, 0 pinned, 0 mismatch**. Comparator and the
independent NanoDa kernel accept all five results (`51d52108`, `109e22e1`,
`c6d92415`, `044974e5`, `b49b53e7`) with **no permitted axioms**. The four
transfer/strength proofs passed unchanged; the controls initially introduced
`propext` through simplifier proof terms and were repaired with direct case
proofs, after which their zero-axiom verification passed. The Solution has no
`sorry`; only the new Challenge's five expected placeholders remain. No old
Challenge changed.

Offline corpus/source validation, attribution check (no changed stating
claims), bundle audit, spec regeneration, module-format and whitespace checks
pass. The new definition's ungenerated formal-status entry and the existing
lexical backlog remain warnings; shared imports and formal-status generation
are coordinator-owned. No source bytes were reacquired. Live convention
`sourceRevision`: `15f348b072188255da837578eaafc8a98f12fdf0`.
Prepared dependencies were supplied by the coordinator; no cold project build
or worker preflight was run. Fresh independent semantic challenge of this
complete outcome and required final integration CI remain pending. No push,
PR, watch, merge or issue-state change was performed.

## Connected actual source and uniqueness reconstruction (#1729, 2026-11-17)

**Complete proposed outcome for fresh semantic review.** At baseline
`ebaab0aa17356354ea9b90147b4f3a8108421c58`, the delivered results support a
connected conditional assembly, rather than another foundation theorem.
Choose the CCR/De ente bundle below: it gives one actual esse source n,
identifies that same n as the unique actual concrete root at w under the
explicit root bridges, and makes n necessary under contingent-grounding.
The existing fixed-esse God consumer can name that same n with its full
companion bundle. No component of this assembly establishes its open premises.
The maximum and pure-indiscernibility packages are genuine alternatives for
root uniqueness, not automatic replacements for De ente identity uniqueness.
This completes the proposed integration scope subject to independent review;
#1724 retains the foundation-warrant investigation and its canonical account.

### One dictionary, one populated route, one witness

Fix p, B, represented principle type P, respect type R and p.esse exactly as
in the [CCR dictionary](#fixed-dictionary-and-exact-reuse). Fix one grounding
profile m on the **same B**, selected world w, and the same p.InAct,
p.CausesIn and p.esse at every downstream use. These profiles are not equal
by definition. Keep MoreIn, PriorSimply, ComponentOf and IsGod fixed when
invoking the naming consumer. Their applicability is a commitment, not a
change of witness hidden in a notation change.

1. Supply one actual p-bearer (`78cffb8e`), CCR on `esseCauseGraph p`
   (`20babef7`), distinct-esse coverage (`457698e4`), identity-bearer
   uniqueness (`a576300f`) and EM (`ee4ab504`). The existing
   `TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.commonSourceOfClosed`
   ([c6d92415](../../corpus/results/c6d92415-0a65-4f5d-8d1d-147f1fe55592.json))
   selects n, actual and esse-identical, without an incoming distinct actual
   esse cause, with a finite nonempty cause path to every other actual bearer.
   It reaches **c35b1a5c**, not merely a root somewhere. The prior actual
   population work supplies a starting bearer only through its stated
   existence/concreteness-to-act dictionary; the synthetic adapter's guards
   are not evidence that a real bearer exists.
2. `TruthCore.Results.Aquinas.DeEnte.RootInterface.deEnteFirstSourceIsActualRoot`
   ([ca5403a6](../../corpus/results/ca5403a6-89d9-4c27-9840-0874cd70d776.json))
   retains n using existing-in-act `0436de86`, identity-bearer actual
   concreteness `ad2b3ffc`, ground-to-esse-cause `17350d52` and no self-cause
   `b62a64ab`. Its endpoint is `ce7edf53`. The ground bridge carries the
   substantive move from no actual esse cause to no actual concrete ground;
   absence of a substantive objection to it is not its derivation.
3. In the same m,w,p, `EsseSource.atMostOneActualRootFromDeEnte`
   ([c056ad5c](../../corpus/results/c056ad5c-458c-4cc3-8d80-3e24b5e705b6.json))
   uses `457698e4`, `a576300f`, `0436de86`, cause-to-ground `cb1cdea9` and EM
   to make every actual root an identity bearer and identify all roots.
   `RootInterface.uniqueActualRootFromDeEnteSource`
   ([6e89d528](../../corpus/results/6e89d528-e1aa-4b8c-b0ae-8128c98ed5dc.json))
   pairs that at-most-one endpoint `49fdec01` with step 2, giving **7ab0ddcb**.
   It can choose n from step 2; uniqueness equates any other chosen root to n.
4. `TruthCore.Results.Causality.ActualRootNecessityUpgrade.upgrade`
   (argument [70adaf7c](../../corpus/arguments/ACTUAL-ROOT-NECESSITY-UPGRADE.json))
   adds `EveryContingentGroundedAt` (`c71c068c`) and EM to obtain
   **91b085c4** for the same n. If n were absent at an accessible world it
   would be an actual contingent root, excluded by that added premise.
   Nothing about represented esse/essence equality supplies modal necessity.

Thus the flattened root/necessity bundle is CCR, coverage, identity uniqueness,
one actual p-bearer, EM, existing-in-act, identity-bearer concreteness,
ground-to-esse-cause, no-self-cause, cause-to-ground, and contingent-grounding.
Identity uniqueness may be accepted directly or supported by its seven-input
multiplication argument below. Repeated inputs are shared commitments, not
independent corroboration. No extra whole-roster premise is needed for this
root-existence branch. All these links already exist; no adapter or equivalent
wrapper has been registered by this consolidation.

### Foundation options at the actual-access endpoint

For one fixed profile and world, the exact namespace is
`TruthCore.Results.Causality.ConcreteRootAccess`. Its
`rootAccessEquivalence` proves CCR iff universal finite root access under EM;
`borrowedDecomposition` proves CCR iff `NoWhollyBorrowedCollection` **and**
`LocalizedBridge` under EM. The latter cannot silently drop its mixed-supplier
bridge. These equivalences locate a commitment; they add no independent
reason to accept it. They give multiple local roots, not root uniqueness.

| Option | Exact usable transition | Additional application commitment |
|---|---|---|
| CCR directly | `20babef7` on `esseCauseGraph p`, then step 1 | Exhaustive actual esse-supplier scope and the local closed-collection foundation claim |
| Unrestricted esse WF | `ClosedEsseSource.closedOfWF` (`044974e5`) gives the same CCR | Rules out every infinite descending actual esse-cause path, more than common ancestry requires |
| Per-se WF | `RootInterface.unrestrictedRegressFromPerSe` uses `ea251340` AND `e74de400`, then the WF option | A caused esse cause causes as caused; PER_SE_5 is not automatically temporal order or efficient PER_SE_1 |
| Borrowed availability | `borrowedDecomposition`, or `closedRootedOfBorrowed` with actual supplier concreteness | All relevant suppliers covered; a mixed abstract supplier needs the localized bridge, not its deletion |
| Quantitative attenuation | `TruthCore.Results.Causality.ClosedGroundingRoots.closedRootedOfAttenuation` yields CCR on the selected profile | `AttenuatedEsseReception`: countable actual domain, positive bounded P, nonnegative own supply and weights, summable rows and weighted sums, row sums at most a common q<1, reception inequality, positive weight implies this ground edge, positive own supply implies actual root |

The attenuation option is available on `esseCauseGraph p` only if that full
bridge is supplied there. Neither a numerical metaphor nor the fixed-duration
Reaper metric supplies it. The [quantitative note](contractive-borrowed-power-1378.md)
contains the loss/bound controls. An infinite supply network with no common
bound, or without uniform loss, does not meet this theorem's hypotheses.
No independently calibrated amount of esse is claimed here.

Whole-roster nontrapping is a different endpoint: with actual population and
EM it gives some actual root. It is enough for the alternative
`RootInterface.uniqueActualRootFromDeEnte` (`ef632140`) when coverage,
identity uniqueness, existing-in-act and cause-to-ground identify every root.
It does **not** itself give finite ancestry to each bearer. The isolated-root
beside rootless-regress control in the CCR section blocks that shortcut.

### Uniqueness packages on the same candidate roots

Use the same m,w and candidate predicate `ActualRoot m w` in every row.
Only the first row also obtains De ente's identity-source classification;
the other rows do not imply `AtMostOneEsseIsEssence p` for all actual
identity bearers without further coverage/root bridges.

| Package | Full joint inputs beyond the displayed root-existence base | Exact endpoint and what may be declined |
|---|---|---|
| De ente multiplication | For `a576300f`: multiplication inventory `2495a71d`, shared nature `75b5b027`, no added difference `f13d1cdd`, no matter `38ed105c`, reception in own essence `6dfe01ab`, receptive potency `7fcfcee8`, no self-receptivity `14325c83`. For actual-root at-most-one add coverage, existing-in-act, cause-to-ground and EM as in step 3. | `7ab0ddcb` via the source-root base above, or population + whole-roster + EM via `ef632140`. Does not require grades or pure-indiscernibility. |
| Fixed-esse grades/maximality | `TruthCore.Results.Causality.ActualRootUniqueness.uniqueRoot`: population, whole-roster and EM as base; fixed-esse maximal causality `da09703b`, existing-in-act `0436de86`, cause-to-ground `cb1cdea9`, fixed-esse grades `e4e6b0cd` | `7ab0ddcb`, then the same `c71c068c` + EM upgrade. De ente shared nature/multiplication can be declined for this root endpoint, but not thereby removed from a separate source-first derivation of `da09703b`. |
| Pure indiscernibility | `TruthCore.Results.Causality.PureActRoot.uniqueRootFromPureIndiscernibility`: population, whole-roster, contingent-grounding and EM as base; every root has every pure determination `fe67d766`, all its determinations are pure `3b39e0ba`, and purely determined indiscernibles are identical `bd0a956c` | `91b085c4`. Grades/genus and multiplication can be declined if these premises are independently retained. The actual-root re-indexing is not a physical-motion identification. |

The pure-indiscernibility bridge quantifies over beings, not merely roots.
Its real-thisness sibling is another support option, not an equivalent
formulation inferred here. Pure actuality alone does not supply every pure
determination; #1728's accepted [connected pure-act case](modal-spine.md#connected-pure-actuality-case-for-1728-2026-11-17)
therefore cannot be substituted for all three uniqueness inputs. That case's
passive-constitution and current-giver bridges remain visible and unchanged.
The [canonical individuation audit](necessary-simple-plurality.md#independent-individuation-audit-the-unresolved-exhaustive-step)
and [pure-root audit](necessary-simple-plurality.md#pure-act-premises-at-the-necessary-root-2026-11-07)
retain the positive arguments, controls and bare-difference boundary.

Shared nature concerns a real multiplication account for identity bearers;
MoreIn concerns comparative esse; Has/Pure concerns real determinations.
No dictionary between them is presumed. In particular, shared numerical
essence values in q11's proper-IsGod domain do not transport to all actual
De ente candidates. Accepting one package supplies its endpoint, not every
other package's internal predicates. The alternatives are not claimed
exhaustive or evidentially independent.

### Carrying n into the God consumer without dropping its companions

The source route already connects to **8626f8a5** through argument
[f4df2153](../../corpus/arguments/f4df2153-a995-40f7-99d6-3f68ed2b5cbe.json),
then [c98328f1](../../corpus/arguments/c98328f1-3c05-40ad-983f-1fee15873f12.json).
The first uses common source **plus** actual esse-cause composition `b4987085`,
causal ascent `cffad050` and EM to derive `da09703b`. Finite ancestry alone
does not give direct universal causation; composition supplies that step.
Causal ascent identifies every maximal bearer with the source; no maximum
exists just because this universal statement holds. The already delivered
[0609389b](../../corpus/arguments/0609389b-ae65-46c8-beaa-2246041e35de.json)
is the weaker sufficient alternative: common source, composition, identity-source
scoped ascent `8176a284-769b-4ed0-b90b-ff655b7fd864`, and EM give the same
`da09703b`. It can replace full `cffad050` without changing the source,
consumer or other inputs. Its positive reception/degree calibration and
remaining application are retained in the causal-perfection note, rather than
requiring the unrestricted ascent claim for this assembly.

The naming consumer's twelve inputs are recorded below, with exact canonical
statement links. This is an AND bundle, not optional background.

| Input | Canonical meaning |
|---|---|
| [56f68b40](../../corpus/statements/cogito-inhabited-concrete-world.json) | `InhabitedConcreteAt` |
| [5c898d24](../../corpus/statements/whole-roster-not-trapped.json) | `WholeRosterNotTrapped` |
| [ee4ab504](../../corpus/statements/excluded-middle.json) | `ExcludedMiddle` |
| [86efed1a](../../corpus/statements/simply-prior-is-actual-concrete-ground.json) | `SimplyPriorIsActualConcreteGround` |
| [da09703b](../../corpus/statements/maximum-in-being-causes-all-beings.json) | `MaximumInBeingCausesAllBeingsReading` |
| [0436de86](../../corpus/statements/existing-in-act-at.json) | `ExistingInActAt` |
| [cb1cdea9](../../corpus/statements/esse-cause-is-actual-concrete-ground.json) | `EsseCauseIsActualConcreteGround` |
| [6c27657f](../../corpus/statements/grades-have-a-maximum.json) | `GradesByApproachToAMaximumReading` |
| [7067553d](../../corpus/statements/actuality-only-insofar-as-being.json) | `ActualityOnlyInsofarAsBeingReading` |
| [b26c10a0](../../corpus/statements/universal-cause-transfers-perfections.json) | `UniversalCauseTransfersPerfections` |
| [09c6d5f0](../../corpus/statements/no-component-is-first-being.json) | `NoComponentIsFirstBeingReading` |
| [1ec205ed](../../corpus/statements/god-names-the-fully-described-principle.json) | `GodNamesTheFullyDescribedPrinciple` |

`TruthCore.Results.Causality.MaximalFromEsseSource.sameWitnessGodAtBeing`
retains its chosen root through firstness, maximum identification and naming.
When supplied this same m,w, uniqueness from step 3 identifies its chosen root
with n. Thus `IsGod n` and step 4's necessity concern one being. This is a
transparent composition of existing proofs, not a newly certified stronger
consumer statement. The registered GodExists consumer itself asserts neither
necessity nor uniqueness. Its whole-roster/population inputs remain explicit;
the already available root supports them through its actual presence and
`WholeRosterRootEquivalence.wholeRosterOfRoot`. That reuse does not supply
any new foundation warrant. The consumer retains global grades `6c27657f`,
even though the root-uniqueness alternative uses fixed-esse `e4e6b0cd`.
No weakening of the registered consumer has been claimed.

The source-first derivation of maximal causality and the naming consumer
share causal/actuality commitments. In particular a grades uniqueness route
using `da09703b` *from this source route* still depends on that route's
identity uniqueness. It is an independent alternative to multiplication
only when maximal causality has another retained warrant or is accepted
directly. Counting the round trip as another proof of source uniqueness
would add no warrant. Intellect, will, eternity, infinity and the full
classical description remain their separate #1731 bundles; GOD_4 naming is
not historical or Christian identification.

### Modal support alternative and exact joins that remain OPEN

Groups #1726–28 are consumed as delivered in #1738–40, not reimplemented.
The [necessary-concrete comparison](conceptual-existence-boundary.md)
retains atomic and atomicity-free actual-cover producers of `b19ffd92`.
Their necessary witness need not be the cover, cause, original actual bearer
or this n. A necessary actual being provides no underivedness for free.

The separate exact namespace
`TruthCore.Results.Causality.UnderivedCommonSource` offers `from_union`:
`NecessaryBeing`, `ActualReflexive`, `NoContingentGroundOfNecessary`,
`WellFoundedUnionNecessarySupport`, EM, weak connectedness and upstream
confluence of **the same actualSupportGraph m R w**. It preserves the
necessarily-underived witness supplied by `NecessarilyUnderived.PositiveUnion`;
that witness may differ from the necessary being used as its starting input.
`exists_support` starts with `NecessarilyUnderived` instead of those five
producer premises. `causal_from_union` additionally needs
`ActualCauseSupportsEsse` and places connectedness/confluence on actualGraph;
there is no definitional identity of Causes, R and grounds.

`TruthCore.Results.Causality.SourceWitness.rooted_from_source` takes weak
connectedness, upstream confluence and HasSource on one graph and returns
unique-source finite access. Its graph paths must be read with that library's
edge convention, not substituted directly for De ente supplier-first TransGen.
This generic argument does not require a shared nature; conversely De ente's
identity uniqueness is not evidence of generic confluence on an unrelated
relation. The plural-root control below shows why connectedness alone fails.

The scope difference is consequential. `91b085c4` says n exists at every
accessible world and has no actual **concrete** ground at w. It says neither
that no abstract ground exists at w nor that no supplier exists at another
world. `NamedNecessarilyUnderived` excludes existing R-suppliers at every
world in its definition, as well as retaining necessary existence. Upgrading
the former to the latter is **OPEN** without same-supplier scope and world
transport. #1725's [support-path continuation](conceptual-existence-boundary.md#computed-god-root-delta-for-the-support-path-continuation)
provides standing-support coverage and union-WF only under its explicit
all-concrete-source or necessary-source transport policies. Necessary-source
transport alone does not cover every contingent supplier. These results may
support the union branch when their dictionaries match; they do not remove
its policy inputs or identify its selected witness with n. A justified
root/support dictionary and actual-root uniqueness could identify witnesses
at w; it still would not manufacture all-world underivedness.

**Next test for that join:** inspect an explicitly selected R and ontic
profile, check every possible supplier's concreteness and actual/world
transport conditions from #1725, and then apply the existing union theorem.
Where only necessary suppliers transport, retain the contingent-supplier
exclusion as an additional assumption. No equivalent transport wrapper is
needed and no new foundation investigation is assigned here.

### Joint supply, temporal routes and controls that reject false joins

The [joint-group record](joint-causal-groups-733.md#sufficiency-exercise-and-completeness)
keeps contributors **and enablers**, admitted versus exercised groups, allowed
scenarios, and event-to-bearer mapping separate. A group index is not a new
substantial supplier. Its actual graph uses occurrence, not substantial esse.
To feed an esse/CCR route, an application must justify the bearer map, actual
exercise, complete contributor/enabler union, direction and same-existential-
respect supply. Projected membership alone proves none of these. Omitting an
enabler can destroy joint sufficiency, and individually redundant contributors
do not justify individual strict but-for dependence. This is why the
foundation account must be applied to complete supply rather than rewritten
as “each dependent contributes nothing.”

The [temporal/Reaper comparison](../causal-regress-and-grim-reapers.md)
and #1722's delivered metric interfaces concern histories, duration, populated
past and modal arrangement/patchwork conditions. The temporal-branch
comparison selected in open issue #1736 retains the continuing-dependence
question for a beginningless history; it is not treated here as a completed
eternity integration. Neither an infinite past nor a finite past by itself
settles same-world esse support. A conversion needs explicit time/world and
bearer maps, same-respect esse supply and any per-se bridge. Thus declining
temporal beginning does not withdraw this CCR conditional route, and accepting
a Reaper argument does not supply CCR or underivedness for it.

The existing controls discriminate the proposed joins without new models:

| Existing control | What it checks here | Boundary |
|---|---|---|
| `ClosedEsseSource.Control.rootedInfinite` and `rootedCycle`, result `b49b53e7` | CCR, coverage, identity uniqueness and common ancestry coexist with root-backed infinity or dependent cycles | Not a refutation of CCR or evidence for actual metaphysical realization; WF is the extra rejected requirement |
| `ClosedEsseSource.Control.rosterOnly` | An isolated root does not serve a detached rootless component | Whole-roster existence cannot replace universal access in step 1 |
| `PluralRootConfluence.Control`, [plural-root attempt](../../corpus/attempts/plural-root-confluence.json) | Same connected support graph has two sources with a common effect; even WF holds, confluence fails | Blocks connectedness + source ⇒ unique common source; does not defeat De ente's different uniqueness premise |
| Joint fixture `a ∧ (b ∨ c) ∧ enabled` | `{a,b}` without the enabler is not sufficient; alternative complete bundles can coexist | Blocks omitted-enabler/individual-sufficiency projection into esse coverage |
| `RootInterface` absent-source, noncausal-ground and self-ground controls | The actual-world converse, ground/cause bridge and self-cause exclusion cannot be silently dropped | Formal interpretation boundaries, not independently justified objections to the retained bridges |

### Cumulative provisional assessment and next distinct question

The positive case is a coherent explanatory route: actual being, received-esse
coverage, a nonborrowed-availability commitment at exhaustive supplier scope,
and the addition-excluding esse account provide real prima facie warrant.
CCR improves that route by requiring only finite root access, not a ban on
every infinite branch. Multiplication, comparative maximality and pure
indiscernibility provide meaningfully different support options for the
common root endpoint when their own full packages are retained. This breadth
is useful conditional support; direct primitive acceptance remains legitimate.
No premise must acquire an endlessly prior proof to be considered warranted.

For foundation, carry forward the [canonical current assessment](unique-feedback-explanation-311.md#current-foundation-judgment-on-the-existence-only-case-2026-11-17)
and #1724's [owned comparison](https://github.com/moritzbrantner/formal-logos/issues/1724).
The modestly favorable nonborrowed-availability rationale applies when the
relation exhaustively supplies the relevant existence. The serious rival is
an actually obtaining organized constitutive order whose constituents and
arrangements jointly account for the same member without a foundation member.
Its positive mechanism distinguishes constitution from productive activity;
local causal non-self-production does not refute it. Its remaining burden is
same-explanandum realization and adequacy, not mere graph consistency. The
source account likewise owes actual obtaining and supply. This note changes
neither the canonical assessment nor the live comparison and does not declare
all infinite or constitutive variants refuted. A fundamental natural whole
may satisfy foundation; the later identity, universal-scope and naming inputs
must then be assessed, rather than treating naturalism as rootlessness.

For uniqueness, the [current shared-nature assessment](#current-source-selection-judgment-identity-and-the-nature-being-multiplied-2026-11-17)
supports addition-excluding unreceived esse as a motivated primitive. Equality
of represented principles alone does not supply real shared nature. The
intrinsically differentiated whole-nature proposal targets the extra
whole-nature/reception inference; its extension to unreceived esse remains
unwarranted on this record, not a refutation of that stronger account.
Bare numerical difference targets the multiplication/indiscernibility
principles; the finite plural controls only locate those inputs. Grades and
pure-determination bridges have their own application burdens and cannot be
credited as independent support when derived from the disputed source route.

**Overall provisional judgment:** the assembled case positively supports one
necessary actual source **conditional on** the complete fixed-dictionary
packages above and can carry that same source into the existence-only God
consumer. Formal transport is already available; substantive concentration
lies in exhaustive existential-supply application, the selected uniqueness
account, modal contingent-grounding, composition/ascent and divine naming.
The present assembly does not settle these applications or defeat the standing
constitutive rival. It also supplies no new adverse evidence merely because
a premise is open. Repetition of cut, borrowing or chain vocabulary adds no
corroboration. Revision upward requires warranted same-relation supply and
uniqueness/identification applications; revision downward requires a concrete
failure of one retained bridge or a defended competing realization at the
same explanandum, not a merely conceivable alternative.

The distinct onward question for #1730 is whether THIS selected source's
intrinsic nature adequately explains its own existence and the actual order,
including the difference between constitution and productive supply. #1731
owns the selected source's attributes. #1724 retains exhaustive foundation
warrant. These allocations do not restart stopped investigations or require
the owner to choose a metaphysical winner.

### Recovery, self-sweep and issue disposition

The existing attempt `9f771edb` indexes the foundation premise, source,
actual/necessary root interfaces and God consumer together. Retrieve
`context c6d92415-0a65-4f5d-8d1d-147f1fe55592`,
`context f4df2153-a995-40f7-99d6-3f68ed2b5cbe` and
`context c98328f1-3c05-40ad-983f-1fee15873f12` for their full companion
bundles; use `dossier` and `brief` on `20babef7`, `c35b1a5c`, `7ab0ddcb`,
`91b085c4` and `8626f8a5` (full UUIDs in the linked records). The complete
integration and its boundary are linked from the same attempt, so retrieval
from either premise or consumer does not restart #1724. The rooted-infinite
and mixed-supplier boundaries above prevent “regress” from triggering a false
universal refutation. Related/novelty retrieval is advisory, not a certificate.

Self-sweep: no Lean, frozen Challenge, proposition meaning, source attribution,
batch spec, shared import or computed status changed. Each conditional arrow
retains all conjuncts. Root access, common ancestry, unique actual root,
necessary existence, all-world underivedness and God naming remain distinct.
Witness equality in this assembly follows from the retained actual-root
uniqueness, not reuse of a letter across existential eliminations. Pure act
does not entail complete perfection. Controls certify only their explicit
interpretations. The existing source and root-interface positive controls
check their stated sub-bundles; no joint realization certificate for the
whole flattened source/necessity/naming bundle is asserted here. Its joint
metaphysical applicability remains unresolved, and separate controls are not
combined as if they were one model. Foundation findings are consumed at matching scope and
application obstacles are not presented as defeats. No claim is newly
attributed and no source bytes are freshly certified.

**Historical worker handoff; publication status superseded by the [current reviewed disposition](#current-reviewed-assessment-2026-11-17).**

**Disposition proposed to the coordinator:** #1729's connected reconstruction
and exact boundaries are delivered for a fresh semantic challenge. After
acceptance and integration, record the delivered revision in #1729 and #143
and close this bounded scope; leave the named foundation/adequacy/attribute
questions with their existing owners. No issue comment, push, PR or closure
was performed by this worker.

Canonical recovery identities (full UUIDs are intentional retrieval anchors):

| Role | Statement |
|---|---|
| CCR premise | `20babef7-6ae7-4b48-b72a-f417e8e63136` |
| Common esse source | `c35b1a5c-6405-449b-993b-8196b2457e08` |
| Unique actual root | `7ab0ddcb-cf48-5457-bee7-b6ea9c13b6b1` |
| Unique necessary actual root | `91b085c4-f1c7-5ada-9848-8e7dc753313a` |
| GodExists consumer endpoint | `8626f8a5-9531-5da7-9ebd-f901e74b1129` |

### Verification and review handoff for #1729

Convention resolution reports unchanged sourceRevision
`15f348b072188255da837578eaafc8a98f12fdf0`. All corpus commands use the
coordinator's warm binary at
`/home/moenarch/moritzbrantner/truth-core/target/release/truth` with explicit
`--root` selecting this checkout; final checks and recovery use
`python3 scripts/worker_env.py -- …`. No preflight, preview, cold build or
source materialization was performed. Existing proof/binding/axiom/Comparator/
NanoDa evidence is reused: no formal input changed and no new proof is claimed.
Required integration CI and fresh semantic challenge remain coordinator-owned.

Offline `truth check` passed with advisory corpus/lexicon warnings;
`source_evidence.py check` passed for 516 passage records and 2058 formalized
claim bindings, retaining bibliographic/unavailable byte-verification exceptions.
`truth attribution-check --base ebaab0aa17356354ea9b90147b4f3a8108421c58`
reports no new or changed stating claims. Local-file links in all three edited
notes and the new section's local anchors were checked; no missing target was
found. No batch spec or generated formal record changed. Changed-research-metadata
validation passes, and `affected_results.py select` on the committed four-file
manifest selects zero results in zero shards. `git diff --check` passes.

Premise and consumer recovery were exercised with `context`, `dossier` and
`brief`: CCR result `c6d92415` and God argument `c98328f1`, CCR statement
`20babef7` and God statement `8626f8a5`, using their full identities above.
All six recover attempt `9f771edb`. Its current summary leads with the
same-witness assembly and actual-root/all-world-underivedness boundary, so
normal truncated retrieval exposes the current finding before historical
entries. Related/brief/novelty and source/root endpoint dossiers were also
inspected; novelty returned **partially-recorded**, consistent with reuse.
No absence of an issue-snapshot hit was treated as novelty evidence.

The actual computed God-root comparison, using
`truth --root "$PWD" frontier-diff --base ebaab0aa17356354ea9b90147b4f3a8108421c58 --frontier-root 8626f8a5-9531-5da7-9ebd-f901e74b1129`, is:

```text
premise delta for GOD_4 exists: there is something that is GOD_4, in the sense of the GOD_4 of classical theism [8626f8a5]: ebaab0aa17356354ea9b90147b4f3a8108421c58 -> working tree
open premises reaching the root: 420 (290 bare, 78 supported, 52 stated) -> 420 (290 bare, 78 supported, 52 stated)
expanded-route diagnostic (lowest cost): GOD_4 exists: there is something that is GOD_4, in the sense of the GOD_4 of…, from prima via [ed7c588a] (cost 6) -> GOD_4 exists: there is something that is GOD_4, in the sense of the GOD_4 of…, from prima via [ed7c588a] (cost 6)
distinct verified support alternatives: 436 -> 436
verified support alternatives added: 0
no change
```

This is no formal premise change. The counts describe the graph diagnostic,
not a ranking of warrant or a weakness of conditional support. The delivered
manifest is this note, the existing attempt `9f771edb`, and bounded inbound
links in `direct-grounding-warrant.md` and `necessary-simple-plurality.md`.
The complete proposed outcome and self-sweep above are the review target;
no independent review of this new consolidation is claimed.

## Same-witness identities for #1731 (2026-11-18)

**Proposed outcome for review.** The owner comment on #1731 asked whether the
witness identity between the classical God root `da3facd6`
(`NecessaryClassicalGodRootAt`) and the underived candidate is already
certified. It was not: the #1729
assembly above calls the source-to-God carrying "a transparent composition of
existing proofs, not a newly certified stronger consumer statement", and
`NecessaryClassicalGodRootFromUnderived.derive` says its type does not state
that its premise and conclusion witnesses coincide. Two zero-axiom results
in `TruthCore.Results.Causality.SameSourceWitness` now state the identities
as types. Vocabulary `TruthCore.Causality.SameSourceWitness` gives the
pointwise bodies of the three existing endpoints; its `…_iff` lemmas check
by `Iff.rfl` that each body is exactly the existing definition's body.

| Result | Theorem | Premises | Conclusion |
| --- | --- | --- | --- |
| [c66eead8](../../corpus/results/c66eead8-8674-4d0c-b04f-423d51c34392.json) | `deEnteSourceIsUnderived` | De ente source root `ce7edf53`, underived candidate `0bdcf366`, unique actual root `7ab0ddcb` | `630843d1`: ONE n is both the De ente source and an underived candidate |
| [8e3b89c9](../../corpus/results/8e3b89c9-2793-4263-b83c-c974328b3b3f.json) | `deEnteSourceIsClassicalGodRoot` | `ce7edf53`, classical God root `da3facd6` | `654eead1`: ONE n is both the De ente source and the GOD_4 classical root |

Typing: every endpoint is taken on ONE carrier (`σ.Being` for the classical
root), ONE grounding profile `m` and world `w`, and, for the classical root,
the SAME q.3 a.4 profile `p` (the De ente `Profile B P R` and the classical
root's `PrimaPars.Question3.Article4.Profile σ.Being P R` are the same type).
Neither proof mentions `Ontic.Causes`, an unrelated profile exemplar, or the
q.3 causal relation; they use only `ActualRoot m w`, i.e. `m.grounds`.

* **u = n.** The underived candidate has no existing concrete ground at ANY
  world, so none at `w`: it is an actual root. `UniqueActualRootAt m w`
  identifies it with the De ente root. All-world underivedness and necessity
  come from `0bdcf366`; they are not derived from roothood at `w` (the #1729
  boundary above is unchanged).
* **g = n.** `NecessaryClassicalGodRootAt` contains `PerfectRootAt`, whose
  own third clause says every actual root of `m` at `w` equals its witness.
  So De ente root EXISTENCE suffices; no multiplication, grades or
  pure-indiscernibility uniqueness package is an input. This does not remove
  uniqueness from the case: it is carried inside the classical endpoint's
  22-input bundle (its producer `UnderivedRootPerfection.derive` obtains it
  from the fixed-esse maximum identification). The bare `GodExists`
  projection forgets this witness; the new conclusion keeps it, which is why
  the argument records `strong_version_needed`.
* With both endpoints and the classical root `da3facd6`, the underived
  candidate is also g (the uniqueness clause inside `da3facd6` covers it), so u = g = n without `UniqueActualRootAt`.
  That third composition is inline in `NecessaryClassicalGodRootFromUnderived`
  and was not registered again.

Neither result proves any input: the De ente actuality, concreteness,
ground-to-esse-cause and no-self-cause bridges, all-world underivedness, the
classical root's attribute/naming bundle and GOD_4 naming all stay open.
GOD_4 is the nominal case predicate, not historical or Christian identity.
Sense-coverage gap (#216): the label of `630843d1` carries the tag
CONCRETE_6, inherited from `ce7edf53`, but no CONCRETE record has a sense of
that label. The nearest, CONCRETE_AND_ABSTRACT_6 (`HasEsseInRe`), is not the
profile's primitive `m.concrete`, so it is not linked. The same gap already
exists on `ce7edf53`.
No control was added: the existing plural-root and `RootInterface` controls
already show that without a uniqueness clause two actual roots can differ.
The conclusions have no downstream consumer yet; their connection plan is a
De-ente-retaining God consumer (the existing one consumes the bare GOD_4
predicate). Computed frontier: the two identity results add no support
alternative at either root (premise counts unchanged); see the PR job
summary for the batch's combined delta, which comes from the intellect
result recorded in
[teleology-first-mover.md](teleology-first-mover.md#same-witness-intellect-routes-and-the-will-consumer-1731-2026-11-18).
Attempt: `a1b799fe-f75c-4e3e-994a-f4bb834f3ac7`.

## A GOD_4 consumer that keeps the De ente witness (#1731 slice 2, 2026-11-18)

**Proposed outcome for review.** The identity conclusions `630843d1` and
`654eead1` had no downstream consumer, and every registered GOD_4
existence consumer (`c98328f1`, `92ab7c94` and the rest) projects to bare
`GodExists`, so the De ente witness is lost. Two zero-axiom results in
`TruthCore.Results.Causality.DeEnteSourceGod` add a witness-retaining GOD_4
consumer of the De ente source `ce7edf53`; the identity conclusions remain
unconsumed:

| Result | Theorem | Premises → conclusion |
| --- | --- | --- |
| [d9ee967a](../../corpus/results/d9ee967a-58be-43f9-a86f-72f2ef49abe0.json) | `deEnteSourceIsGod` | `ce7edf53` and the ten inputs `ee4ab504`, `86efed1a`, `da09703b`, `0436de86`, `cb1cdea9`, `6c27657f`, `7067553d`, `b26c10a0`, `09c6d5f0`, `1ec205ed` → `7a791743`: ONE n is the De ente source, a first being, and GOD_4 |
| [f3709290](../../corpus/results/f3709290-4741-44a6-bf95-5222bfac8da7.json) | `godExistsOfDeEnteSourceIsGod` | `7a791743` → `8626f8a5` (structural projection) |

`deEnteSourceIsGod` reruns the naming chain of
`MaximalFromEsseSource.sameWitnessGodAtBeing` with the De ente root as its
root. (`c98328f1` itself binds `MaximalFromEsseSource.godExistsAtBeing`, the
projection of that chain.) That proof uses its root only through `ActualRoot m w n`, so any actual
root works. Premise comparison with the existence-only consumer `c98328f1`:

* **Dropped:** population `56f68b40` and whole-roster nontrapping `5c898d24`.
* **Added:** `ce7edf53`, whose producer `03866a17` carries the De ente
  bridges: existing-in-act, identity-bearer concreteness, ground-to-esse-cause
  and no self-cause, over the common source `c35b1a5c`.
* **Kept:** the other ten inputs, and the GOD and maximality sense bridges at
  `1ec205ed` and `6c27657f`.

The conclusion keeps the source's body: esse = essence, no actual esse
cause, and finite actual esse-cause paths to every other being in act.

Compared with the De ente → classical-root chain (arguments `05541bd2`,
`70adaf7c`, `8e61d00e`, then statement `017befa2`, then argument
`80946eca`), it needs no at-most-one-root
package `49fdec01`, no contingent grounding `c71c068c`, and no intellect or
classical inputs. It also gives no necessity, uniqueness of necessary
individuals or classical attribute.

Uniqueness strength is hidden here, not removed. Any actual root that is not
a maximum would be caused by the maximum (`da09703b` with `0436de86`), and
that cause grounds it (`cb1cdea9`). So under these inputs every actual root
is the unique esse maximum, and actual roots are at most one. As with
`sameWitnessGodAtBeing`, this is a consequence of the genus and
esse-to-ground commitments, not a separate premise.

Computed delta (`truth frontier-diff --base 4f742feab`):

* **GOD_4 root `8626f8a5`:** support alternatives 440 → 441, open premises
  unchanged at 421, no bare premise added.
* **Catholicism root:** 523 → 524 alternatives, open premises unchanged at 511.

These are graph diagnostics, not a warrant ranking.

**Rejected consumers, with reasons.**

* *Derive God-to-maximality `4c79298d` from `654eead1`.* `654eead1`'s
  classical body contains IsTheOneGod and the maximum, so it would give
  `4c79298d`. However, every producer of `da3facd6` takes `4c79298d` as a
  premise, either directly or, for the Dei Filius producer `b288856d`,
  through every producer of its root input `c0f4a346`. The derivation would
  therefore close a proof cycle and add no warrant.
* *Derive God-causes-all-being `86d02b69` from `654eead1`* (with actual
  esse-cause composition `b4987085`). Strictly this is not a cycle:
  `86d02b69` has no producer, and `4c79298d` also has the producer
  `2a76d37d`. But `86d02b69` is consumed only by `4c79298d`'s producers
  `482f4ad2`/`4d1efe91`, and every route through `654eead1` already
  presupposes `4c79298d`. A derived `86d02b69` therefore adds no root support.
* *Project `654eead1` onto `8626f8a5`.* This adds nothing beyond the
  existing `92ab7c94` from `da3facd6`. `630843d1` has no GOD_4 conjunct, so
  there is nothing to project; its producer `5a9010a9` does not pass through
  `da3facd6`.

The identity results remain endpoint statements: certified consequences
that state which being the classical root is. Their content becomes usable
downstream once a root-route consumer quantifies over a SPECIFIC source
witness. Exact missing bridge: no root-route premise is stated over a
witness retaining the De ente body; every consumer takes `GodExists`
or a universal GOD_4 conditional. The new `7a791743` is the
non-circular witness-retaining endpoint for that purpose.

**Attributes at the same witness.** The universal predicates `29818edd`
(`GodHasIntellect`) and `66aecdd7` (`GodHasWill`) apply to the GOD_4
witness of `7a791743`, so under their premises the De ente source has
intellect and capacity-level will. This is a two-line instantiation with no
root consumer, so it was not registered. The intellect producers
`b8394dbb` and `26e368d3`, and the will producer `13338e9c`, use
God-to-maximality `4c79298d`. The modular will producer `571e36f0` does not
use it directly, but consumes `29818edd`. Attempt: `e5a36b24-e0f4-4d9c-8cd4-cef767078a7e`.

**2026-11-23 continuation (#1724 with #1616):** The supplier-complete
actual-esse cone warrant, its explicit primitive stopping points, rival
constitutive/holistic and past-law accounts, the finite same-r two-bearer
control, and the exact reuse boundaries are consolidated in the
[canonical existential-supply comparison](unique-feedback-explanation-311.md#complete-existential-supply-comparison-supplier-cones-and-actual-constitution-1724-1616-2026-11-23).
This adds no new premise discharge, naming bridge or world-ground equivalence.


### Supplier completeness under extension of an audited order

Fix one world, the actual bearers, one sense of giving esse and the direction from supplier to recipient. Suppose we have identified **every immediate supplier** of each bearer examined so far. How much of the foundation conclusion does that evidence support? Here an audit is an inventory of recipients together with the full incoming list for each. An actual bearer may appear on an incoming list before its own suppliers have been examined.

For any finite audit on a roster indexed by the natural numbers, choose N above all the examined recipient indices. Compare two assignments on that *same* populated roster. In both, every x below N has precisely x+1 as supplier. In the first, N has no supplier and supplies every x above N; following the suppliers of any x below N eventually reaches N. In the second, every x, including N, receives from x+1. Both are acyclic: distance to N strictly decreases when tracing suppliers in the first; indices strictly increase in the second. Both can also have an integer priority label strictly decreasing toward the supplier (distance to N in the first, minus the index in the second). The full lists at the audited recipients coincide, including the identities of suppliers. Supplied status at every inspected recipient and strict priority on the links therefore fail to distinguish the two. N depends on the audit: this does not give one rooted model agreeing everywhere with the endless one. These are assignments to a productive-relation candidate. The second gives no independent reason for its infinite positive order to obtain.

**What would discriminate?** A nonempty, genuinely finite domain independently verified to contain every actual supplier of every member, together with an independently calibrated strictly earlier priority for each such supplier, gives a sufficient test. Choose a member of least priority label in the domain. An incoming supplier would have to lie in the domain at a smaller label. The test yields a bearer with no incoming supplier *in the selected relation*. It needs no seed term, global rank into a well-order, prohibition of infinite chains elsewhere, or definition of giving by finite generation. The integer labels used below can descend forever on an infinite roster. Replacing finiteness by the mere fact that the investigation has so far examined finitely many bearers breaks the argument.

A simple physical interpretation shows how the two conditions could receive independent warrant in a narrower domain. Consider a fixed finite set of bodies with a verified insulating boundary and only passive conductive contacts. For the selected instantaneous transfer of heat, contact and positive heat flux identify a supplier; independent temperature measurements and the passive-conduction law order each such edge from hotter to cooler. A hottest member receives no heat by the specified route from another body. A body there may still have stored heat, an earlier heater and an existential giver. Neither counting bodies in a bounded apparatus nor reading a thermometer supplies an exhaustive inventory or a strict priority calibration of *esse* givers. For the existential order it would advance the case to identify an independently delimited complete cone and an independently warranted priority on its actual supply links. One finite cone yields one relative root; the collection principle `45890c84` quantifies over **every** eligible collection. The [existing localized bridge](../../TruthCore/Causality/ConcreteRootAccess.lean) and its other inputs remain necessary for the stated CCR route when nonconcrete suppliers are allowed.

**Comparison and judgment.** A collection of borrowers, each of whose exercised giving is only received, supplies a conditional explanation of transmission. If the question includes why that activity obtains at all, listing further actual borrowers can repeat the datum to be explained. This supports the existing modest preference for a nonborrowed source on the exhaustive, per se productive reading. The strongest rival can grant every audited transmission and offer a primitive fact that the whole productive pattern obtains, or a necessarily obtaining concrete whole whose constitution explains its members. The former explicitly stops at global actuality. The latter must justify the whole's actuality and the constitutive passage to concrete members; if that whole is itself an unborrowed bearer under the selected relation, the accounts agree on the narrow existence of a root. The source account likewise owes genuine productive availability and a route from it to these borrowers. The finite test excludes a wholly borrowed *closed finite* order with the stated priority; it leaves the general metaphysical commitment open. The [existing quantitative comparison](contractive-borrowed-power-1378.md) provides a separate test under independent bounds and loss. Neither local success licenses importing heat flow, attenuation or finiteness into existence.

The following local Lean checks reproduce the audit comparison and the finite sufficient condition. They add no registered argument or axiom allowance; the classical finite-minimum proof and arithmetic automation use Mathlib's standard logical background.

```lean
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic
namespace SupplierAudit
def endless (y x : Nat) := y = x + 1
def sourced (n y x : Nat) := (x < n ∧ y = x + 1) ∨ (n < x ∧ y = n)
theorem sameLists (n x y : Nat) (seen : x < n) :
    sourced n y x ↔ endless y x := by unfold sourced endless; omega
theorem endlessBorrower (x : Nat) : ∃ y, endless y x := ⟨x+1, rfl⟩
theorem oneRoot (n x : Nat) : (∀ y, ¬ sourced n y x) ↔ x = n := by
  constructor
  · intro h
    by_cases lt : x < n
    · exact False.elim (h (x+1) (Or.inl ⟨lt,rfl⟩))
    · by_contra ne
      exact h n (Or.inr ⟨by omega, rfl⟩)
  · rintro rfl y
    unfold sourced
    omega
-- Integer labels permit infinite descent on the full roster.
theorem finiteAudit {B : Type} (S : Set B) (r : B → B → Prop) (level : B → Int)
    (finite : S.Finite) (present : S.Nonempty)
    (closed : ∀ x ∈ S, ∀ y, r y x → y ∈ S)
    (drop : ∀ x ∈ S, ∀ y, r y x → level y < level x) :
    ∃ x ∈ S, ∀ y, ¬ r y x := by
  obtain ⟨x,hx,least⟩ := S.exists_min_image level finite present
  exact ⟨x,hx,fun y hy => (not_lt_of_ge (least y (closed x hx y hy))) (drop x hx y hy)⟩
#print axioms sameLists
#print axioms endlessBorrower
#print axioms oneRoot
#print axioms finiteAudit
end SupplierAudit
```
