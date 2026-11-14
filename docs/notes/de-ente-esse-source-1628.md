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

**Open interfaces.**

1. *Root uniqueness.* `atMostOneActualRootFromDeEnte` gives the uniqueness
   half of `7ab0ddcb` without the genus principle and grades. Composing it
   with root existence (`WholeRosterFoundation.actualRootExists`) into
   `7ab0ddcb` type-checks, but the new argument fails `truth check`: both
   `5c898d24` and `7ab0ddcb` carry the two senses
   `INTRINSIC_PRODUCTIVE_CONTRIBUTION_VERSUS_SOURCE_BACKED_1/_2`, and only
   legacy arguments are allowlisted (#1233 sense-index debt). Next step: fix
   the sense links of those two statements, then register the composition.
2. *First source to actual root.* `CommonEsseIsEssenceSource` lives in the
   causes-of-being order of the q.3 a.4 profile; the root interface
   (`ActualRoot m w`) is in the grounding order. To make n an actual root one
   needs (i) that n is concrete and exists at w (from `InAct n esse`; the
   converse of `0436de86`) and (ii) that nothing actual-concretely grounds n,
   e.g. "every actual concrete ground of an actual concretum causes its esse"
   (converse of `cb1cdea9`) together with "a being whose esse is its essence
   has no other cause of its esse". Neither is registered; (ii) is the q.3 a.4
   converse that Aquinas holds of ipsum esse subsistens.
3. *Necessary concrete being.* Given (2), `EveryContingentGroundedAt`
   (`c71c068c`) would make n necessary at accessible worlds (an actual root
   that were contingent would be grounded). The profile itself has no modal
   field; n's identity of esse and essence says nothing modal.
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
| Accidentally ordered infinite series | the scope of `fd12ad3d` | `fd12ad3d` covers every cause of being. Aquinas himself allows an infinite series of causes ordered per accidens (ST I q.46 a.2 ad 7, not re-read for this note), so the unrestricted premise is stronger than what his own regress arguments need. Relevance: if causes of being include accidentally ordered ones, an infinite chain of them is not excluded by Aquinas's own lights. | Not a rival account but a scope objection; the repair is a version of the premise restricted to essentially ordered (simultaneous) causes of being, which would need a matching restriction of the #1629 step. Recorded as the next test. |
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
