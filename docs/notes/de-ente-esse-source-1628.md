# De ente c.3: from received esse to one first being whose esse is its essence (#1628)

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
graph sourcehood) is dropped from `5c898d24`; it is also the only record that
defines `Trap` itself, a P2 link gap. The two GOD_4 grades-at-being routes
(`fc46b7f9`, `3367bf93`) lose their bookkeeping bridges citing `5c898d24`;
93 allowlist entries that no longer fail are removed (32 of them were already
removable on main; the allowlist only
shrank; `sense_index.py ratchet` passes).

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
#1633 supplies efficiency; add a definition record for `Trap` (#216); finish
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
correct. Not changed: `Trap` still lacks a definition record (P2, #216).
