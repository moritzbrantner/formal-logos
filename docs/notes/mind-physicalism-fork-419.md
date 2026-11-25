# Mind and physicalism: a certified fork and an incompatible core (#419)

The arena is one frame (`TruthCore/Alternatives/MindPhysicalism.lean`): occurrences
that instantiate kinds, a target mental kind, physical kinds, and primitive `Causes`
and `RealizedBy`. Lean checks consequence only. All premises stay open, and every
model below is a finite formal interpretation, not a rival theory or a possibility claim. [Research record](../../corpus/attempts/mind-physicalism-fork.json)

## Source reading

Read from `PAPINEAU-RISE-PHYSICALISM-3-12`, pp.8-12, and notes 5-6 in
`PAPINEAU-RISE-PHYSICALISM-13-33`. The causal argument is at p.9. Its three exits are
at pp.10-11 and a generous reading of causation gives realization (p.11).

Premise 3, "The physical effects of mental causes are not all overdetermined", has
two readings, each with its own claim. Per cause, it yields a universal
conclusion in identity-or-realization form. Taken collectively it does not (`collectiveHybrid`). That is a result
about the reading: Papineau says the argument "seems pretty clearly valid" (p.10), and note 6 only discusses
Sturgeon's separate equivocation charge, which is not formalized here.

For the original #419 reading, not consulted and therefore not attributed: any eliminativist or nonreductivist author.
Those labels are the Lean definitions below. Papineau does not address q.75.

## Results

| Theorem | Exact content |
| --- | --- |
| `physicalistFork` | Excluded middle, completeness, influence, distributive premise 3 ⊢ `Eliminative ∨ Reductive ∨ Nonreductive` |
| `fourWayCoverage` | Excluded middle ⊢ `PhysicalistFork ∨ SomeUnbased`; no causal content |
| `positionsExclusive` | The six pairs among the four positions are incompatible, in every frame |
| `noPerSeOperation` | Those four premises, tokening and basis/sharing ⊢ no per-se operation |
| `q75BundleIncompatible` | Five q.75 premises with those six ⊢ `False` |
| `someBased` | Excluded middle, completeness, collective premise 3 ⊢ some target occurrence is based |

Witnesses, each with the causal premises: `eliminativeWitness`, `reductiveWitness`,
`realizationWitness` (a mental occurrence with no physical kind),
`occurrenceIdentityWitness` (all mental occurrences physical, the kind not).

Deletion models, each keeping a per-se operation and the other premises:
`completenessExit`, `influenceExit`, `overdeterminationExit` (each also with an
unbased occurrence and the fork false), `tokeningExit` and `bridgeExit` (each with
the reductive condition). So the core is inclusion-minimal for its five non-logical
premises. No model omits excluded middle. `bundleWitness` shows the premises jointly
satisfiable, so `noPerSeOperation` is not vacuous.

## What this does and does not show

Physicalism is not refuted and is not established. `physicalistFork` says what
follows given the premises; the exits say what an account with an unbased occurrence
must deny in that model. The core forces rejecting some member and selects none.

The decisive open bridge is `STMT-PHYSICAL-BASIS-IS-BODY-SHARING`. Q.75 a.2 speaks of
the body sharing in an exercise. Papineau speaks of identity or realization. Under
`bridgeExit` a reductive frame and a per-se operation coexist, so q.75's conclusion
and the causal argument touch only through that bridge. Whoever asserts it owes a
reading of `BodyShares` on which a realized exercise is shared with the body, and
that reading must then be checked against the q.75 interference premises. Whoever
denies it owes an account of what `PerSeIntellectualOperation` then excludes.

## Semantic grounding

`Causes` follows ordinary usage (a decision causing an arm movement, not a mere
correlate) and is not given transitivity, asymmetry or well-foundedness, since no
theorem needs them. `RealizedBy` relates a role state to its filler (a program step
and a circuit event, not that event's later effect); it differs from causation by
holding between an occurrence and what fills its role, and is given no structural
law. Generalizing either from ordinary cases to intellectual exercise is exactly what
the open premises assert. Rival accounts (Davidson's particulars, subset or
mechanistic realization) are not adjudicated, and a particulars reading needs another
frame. Overdetermination here means a distinct cause in Papineau's p.10 sense; a
noncompeting cause that is neither among nor realized by the physical determiners
counts as overdetermining, so a reply from noncompetition rejects premise 3 here.

## Remaining gaps

- Every premise, including tokening, the bridge and Papineau's completeness.
- A pinned eliminativist or nonreductivist witness, and hylomorphist, dualist,
  idealist and neutral-monist replies; no branch is identified with these.
- The q.75 interference premises (`docs/human-intellect-rival-assessment.md`).
- Consciousness, intentionality and rational agency, which stay separate.
- No inference toward theism or Catholicism is made, and no root premise changes.

## Thinking-source warrant (2026-11-19)

Question: does the existence of an actual thinker warrant a thinking ultimate
source? This is the interpretation/warrant slice of
[#1792](https://github.com/moritzbrantner/formal-logos/issues/1792), feeding the
proposed thinker-root route in #1791 and the same-source continuation in
#1787/#1731. Baseline: `5cbba270d1d99e3e852cff632cf42725cb90cb04`.
The source readings below are inspected research evidence, not newly registered
corpus claims or verified consequences. The original #419 proof and assessment
above are unchanged.

### Positive argument: the origin of cognitive power

[Locke, *Essay* IV.x.2–6, 8–13](https://englishphilosophy.org/locke/ehu/4/10)
offers a direct argument from the knowing self to an eternal cogitative source.
His exclusion of a wholly incogitative origin has a specified rationale:
division, arrangement and motion of matter supply only further mechanical
relations. Section 9 separates cogitative/incogitative from material/immaterial;
section 13 provisionally allows a material thinking first source before the
later argument against it. The first intellectual-source step therefore need
not first establish an immaterial human soul.

The useful analyst reconstruction asks what makes an explanation of cognition
complete. Actual understanding supplies the explanandum; an account confined to
describing movements still owes an account of why those movements constitute or
produce understanding. This gives a reason to investigate the intrinsic powers
of the proposed ground. It does not establish that those powers must themselves
be intellectual: that further claim is precisely what the comparison must test.
Neither failure to describe cognition in mechanical vocabulary nor lack of a
currently available reduction proves that a physical identity is impossible.

[Locke II.i.9–10](https://englishphilosophy.org/locke/ehu/2/1) distinguishes a
finite subject's power to think from its continuous exercise. The candidate
capacity-origin route is therefore different from #1791's episode-bearing
ancestry. This is an analyst-proposed support option, not a correction licensed
by Locke: #1791 requires an occurring episode, not continuous exercise, and
II.i.10 allows the infinite author to think continuously.
[IV.iii.6](https://englishphilosophy.org/locke/ehu/4/3) allows matter
endowed with cognitive powers by a source, while admitting obscurity about the
production of sensations. These passages support keeping materiality, capacity,
exercise and derivation separate; they do not prove that a nonmental productive
power is insufficient.

### A direct challenge to the mechanical exclusion

[Hume, *Treatise* 1.4.5.29–33](https://davidhume.org/texts/t/1/4/5), restates the
mechanical argument and disputes the inference from a description's lack of
apparent connection with thought to causal impossibility. His lever comparison
and appeal to bodily alterations of thought supply a concrete parity challenge.
He expressly separates causing a thought from identifying its subject's
substance. Accepting that objection does not require accepting his entire theory
of substance or causation, and his account supplies no complete explanation of
a subject's existential grounding.

The resulting live test is exact: is the proposed physical account an identity
or constitution claim, or a claim that a distinct mental effect is produced?
The first is not refuted because its individual constituents do not understand.
The second needs an account of the connection. The inspected source argument
does not establish an exhaustive characterization of the base's intrinsic
properties and powers, so it cannot exclude all such accounts merely by
describing the base mechanically.

### Physical realization and intrinsic mentality

[Strawson, “Realistic Monism” (2006), §§3–5, pp.13–26](https://web.ics.purdue.edu/~drkelly/StrawsonRealisticPhysicalism2006.pdf)
argues that genuine constitutive emergence must depend on the base's nature;
his liquidity comparison distinguishes explained structural emergence from
purported emergence of experience from wholly nonexperiential reality. At p.21
he acknowledges that the further exclusion of every nonexperiential intrinsic
constitution relies on an “unargued intuition.” This is a substantive prima facie
commitment, not no warrant, but the general dependence principle does not settle
it. His initial result is micropsychism, with combination still problematic.

[Chalmers, “Panpsychism and Panprotopsychism” (2013), §4, pp.15–18](https://www.amherstlecture.org/chalmers2013/chalmers2013_ALP.pdf)
targets that exact step. His alternative posits nonphenomenal, nonstructural
intrinsic properties with an a priori constitutive connection to experience.
He acknowledges that their nature remains schematic. This is a motivated
alternative to the asserted exclusion, not a delivered mechanism producing
consciousness. A structural/phenomenal gap does not automatically establish
an all-nonphenomenal/phenomenal gap.

[Broad, *The Mind and Its Place in Nature*, ch.II, pp.77–79](https://ditext.com/broad/mpn2.html)
provides a different alternative: irreducible trans-ordinal laws connecting
specified configurations with higher-level properties. They are stable laws,
not arbitrary emergence. The stopping point is an additional primitive
connection; the passage provides no empirically established consciousness law.
It contests requiring lower-level natures alone to supply the explanation.

These accounts must be compared separately. The earlier Papineau causal fork
supports identity/realization conditionally; its causal premises do not establish
that the physical realizer's intrinsic nature is wholly nonexperiential. Thus
causal evidence for embodied cognition need not be discarded to investigate
a mind-involving foundation. Conversely, materiality alone is not evidence for
an intellectual foundation.

### Completed comparison: one subject, two contents

Fix the explanatory target: a subject S jointly experiences a red patch R and
a tone T. The datum is conjoint awareness for S, not just two independently
realized contents. This is a selected philosophical case, not a reported
experiment. Its description includes no prior or numerically distinct source
subject.

[Goff, “Cosmopsychism, Micropsychism and the Grounding Relation,” manuscript
pp.7–9, 12–14](https://assets.zyrosite.com/Aq2ZN1NGQMILGL8l/cosmopsychism_and_micropsychism-YNqX3kzb2Eulj9gD.pdf)
offers a positive whole-to-aspect model: a total experience can be prior to its
visual and auditory aspects. Extending subsumption to subjects requires
subjects-as-aspects. He acknowledges the difficulty and proposes consciousness+,
including unknown nonphenomenal aspects. The experienced-aspect to experiencing-
subject transition therefore remains substantive; his tentative grounding
theory is an input to the proposed advantage.

[Chalmers, “The Combination Problem for Panpsychism,” manuscript pp.8–9,
23–25](https://consc.net/papers/combination.pdf)
offers phenomenal bonding, including co-consciousness, as a positive micro-side
proposal. Its boundary problem is discriminating: a sufficiently permissive
transitive bond threatens universal consciousness, whereas an insufficient bond
fails to unify the selected contents. This challenges mere aggregation without
refuting every relational constitution account.

[Miller, “Can Subjects Be Proper Parts of Subjects? The De-Combination Problem,”
§4, pp.147–150](https://onlinelibrary.wiley.com/doi/10.1111/rati.12166)
indexes unity and boundedness to the subject. A cosmic subject U can jointly
experience more contents than a finite subject S without those extra contents
being experienced by S. This answers a particular inconsistency charge against
subject parthood; it already admits S and does not explain S's existence or
select which aspects constitute subjects.

[Chalmers, “Idealism and the Mind-Body Problem,” manuscript pp.22–25](https://consc.net/papers/idealism.pdf)
distinguishes a single subject under fragmented cognitive modes from distinct
subjects constituted by a cosmic subject. The former avoids producing another
owner by revising personal distinctness; the latter retains a subject-constitution
obligation. Nonidentity cosmopsychism explicitly proposes grounding subjects'
existence, making it a direct candidate for existential grounding rather than
only episode realization. Its subject-constitution warrant and translation to
the selected concrete G relation still need defense. The two readings must not
share an unqualified ancestry verdict.

| Selected account | Positive proposal for the same R/T case | Remaining ownership question |
| --- | --- | --- |
| Micropsychism with bonding | A relation unifies micro-experiences into S's conjoint experience. | Why does that relation constitute S, and why does an additional content X fall outside S? |
| Nonidentity cosmopsychism | S and its experience are dependent aspects of an already unified U. | Why is an aspect a distinct experiencing subject, with its own bounded awareness? |
| Identity cosmopsychism | S is U under a restricted cognitive mode. | What warrants the mode/access account and revision of interpersonal distinctness? This supplies no distinct source subject. |

The absence of a distinct source does not refute #1791's proposed endpoint:
that endpoint permits the necessary thinking root n to be the starting thinker
b itself. A distinct predecessor is required only by its premise about a
grounded thinker. Identity cosmopsychism would still owe root status, necessity
and any further intellectual-cognition claim about that same subject.

Analyst judgment: whole-to-aspect explanation has a familiar phenomenal model
that bare addition does not. That is a limited positive reason to pursue
subsumption; it does not establish superiority over a developed bonding theory.
The visual aspect of a unified experience is not by itself evidence of a second
subject who owns it. Both distinct-subject proposals must explain ownership,
but this does not show that their difficulties are equal.

For distinct-subject accounts, the useful adequacy requirement is now sharper:
account for S's conjoint R/T awareness, why X is outside it, and S's existence.
Identity cosmopsychism instead must explain why R/T are jointly accessible and
X inaccessible in the selected cognitive mode, even if its single subject
experiences X elsewhere. A relation or restricted mode defined only by the
desired result names the missing explanation. Subject-indexed consistency is
not that explanation. No constitutive relation examined here has been shown to
be the bearer-existence G relation in #1791.

### What the proposed route would actually need

The following are distinct explanatory obligations, not newly asserted axioms:

| Proposed contribution | Exact remaining connection |
| --- | --- |
| A source adequate to produce cognitive powers | Why adequacy includes the source's own cognitive capacity, rather than a noncognitive productive power. |
| An intrinsic experiential basis | Why it includes a subject with intellectual cognition, not only qualitative experience or a proto-experiential nature. |
| A thinker or capacity in the explanatory ancestry | Why the dependence is the same finite `ActualConcreteGround` ancestry used in #1791. |
| An eternal cogitative source in Locke's argument | Why that same individual is necessary across the selected metaphysical alternatives; eternity alone does not supply de re necessity. |
| A source possessing cognitive capacity | Why it bears an actual episode in #1791's selected sense, if that stronger endpoint is used. |

`T(x) := ∃ e, Occurs e ∧ Bears x e` in #1791 is occurrence-based;
`HasIntellect` in [the existing definition](../../corpus/definitions/intellect.json)
concerns intellectual cognition, distinguished from sense. Neither is definitionally
equal to a generic power to produce cognition. Keep the existing P/¬P fork fixed.
A capacity route would be a separate support option, not a silent change of T.

The [cogito necessary-ancestor vocabulary](../../TruthCore/Causality/CogitoNecessaryConcrete.lean)
uses an actual-concrete grounding relation at a selected world. Locke's historical
origin, Hume's episode causation and Chalmers's constitutive grounding have no
automatic translation into it. Necessity, root status and mentality must remain
properties of the same witness in any eventual join. The existing
[root intellect/will endpoint](../../corpus/statements/root-intellect-will.json)
is a downstream target; this reading does not discharge any of its premises.

### Provisional assessment and continuation

The positive warrant is strongest for requiring a complete explanation to address
actual understanding and phenomenal character, and for investigating an intrinsic
basis rather than treating unspecified complexity as its explanation. Locke
provides a direct cognitive-source argument; Strawson shows why such an argument
need not reject every form of physicalism. Their shared anti-emergence commitment
is visible and is not counted twice as evidence.

The examined evidence does not yet favor a **distinct actual thinking existential
ancestor** over every specified alternative. The obstacle is substantive:
identity/constitution can avoid a separate producing subject, nonstructural
intrinsic properties need not be assumed experiential, and a productive capacity
need not already be the source's own intellectual exercise. An explanatory
shortfall is not a demonstrated impossibility, and a surviving proposal is not
thereby equally well supported. The current comparison supplies no warranted
ranking of all these incomplete accounts.

The completed unity comparison adds a limited positive reason for investigating
whole-to-aspect dependence and identifies subjective ownership as the next
discriminator. It does not turn one current subject into evidence of a prior
subject. The stronger mental-ancestry assessment remains open; the inspected
nonidentity account supplies an explicit existence-grounding proposal, whose
qualified whole-to-aspect motivation does not settle the subject-constitution
problem or validate its translation into the selected G relation. The possible
self-root endpoint must be assessed separately from a distinct-source argument.

No new theorem, registered source claim, premise closure or God conclusion is
claimed. The next worthwhile contribution must characterize the proposed
bonding or subject-subsumption relation beyond naming its desired output, and
explain S's existence and bounded ownership in the same case; an identity
account instead owes its access restriction and personal-identity claim.
Reopen the stronger ancestry judgment when such a connection is defended, or a
concrete failure of the selected alternative is demonstrated there. Another
opaque no-emergence premise or another proof of the existing conditional would
not answer it.

## Further contribution to theism and Catholicism (2026-11-19)

The owner's continuation asks how philosophy of mind can positively advance
the God/Catholicism case. This follows the reviewed #1804 unity comparison,
with baseline `a317b00dd638feb7c4c477f2e565720aeacf9ae6`. The proposal below is
a comparative research judgment and two candidate connections, not a new
registered derivation. The earlier distinct-thinking-ancestor assessment is
unchanged. Source passages are inspected readings; no new canonical attribution
or verified root edge is claimed. [Assessment record](../../corpus/attempts/4eb61695-aaff-4417-8c2e-151cc00ea5fb.json)

### Use rational understanding as a positive starting point

The strongest immediate starting point is a person actually understanding and
using reasons. A short reflective inference has determinate contents, a
relation of support, and the person's actual uptake of that relation. These
are separable from a correct output or a subsequent story about how it arose.
The existing [rational-basing assessment](epistemic-underminer-boundaries.md#rational-basing-the-particular-transition-must-exercise-the-capacity)
already favors an actual content-sensitive exercise over bare reliability,
ancestry or retrospective endorsement. This can provide prima facie warrant
without first completing a metaphysics of mind.

[Boghossian, “What Is Inference?” (2014), pp.4–5, 15–18](https://paulboghossian.com/pb/files/WhatIsInference.pdf)
argues that personal reasoning operates through understood contents and allows
primitive rule-following to stop a regress of further inferences. This is a
positive account of an intellectual performance, not a proof that its bearer
cannot be physical. Nor need an abstract validity relation itself be an
efficient cause: the proposed activity is the person's reasoning with contents.

Reuse the [intentionality comparison](intentionality-943.md): its producer/consumer
account already distinguishes factual guidance from incidental benefit and
permits error. The [agency comparison](reason-response-history.md) already
separates responsiveness, uptake and ownership. Neither a physical vehicle nor
deterministic implementation by itself excludes the relevant personal activity.
The new contribution is their possible connection to an ultimate explanation,
not rediscovery of these distinctions.

The [reason/intentionality/mental-causation target](../../corpus/statements/cc100-116-reason-intentionality-mental-causation.json)
is therefore a useful starting node. Its separate
[only-personal-explanation premise](../../corpus/statements/cc100-116-personal-explanation-restriction.json)
is not established by showing that persons reason. Personal-level explanation
of an inference does not entail a further person who produces the thinker.
A regress of interpreted symbols is also not a regress of existing subjects.

### Route A: a purposive explanation of rational embodied agents

This analyst proposal can grant physical realization of human thought. It asks
why an order exists with understanding agents, reliable-enough access to an
intelligible environment, and powers to act in it. A successful account of neural
implementation or evolutionary development need not be a competing answer to
that ultimate question. Equally, its incompleteness would not establish theism.

The proposed positive explanation is that finite beings capable of knowing,
choosing and sharing goods are worth creating. A source that understands that
good and wills its realization has a reason to produce coordinated conditions
for cognition and effective agency. The claim that these capacities are good
has prima facie support in the contrast between understanding and error,
effective participation and helplessness; the stronger claim about the ultimate
source's nature and purposes still needs comparative warrant.

[Swinburne, “God as the Simplest Explanation of the Universe” (2011), manuscript
pp.9–10, 18–20](https://users.ox.ac.uk/~orie0087/pdf_files/Papers%20from%20Philosophical%20Journals/Swinburne_2011-explanation.pdf)
provides the relevant local argument: valuable embodied agents need an orderly
environment for efficacious choice. He compares personal explanation with a
good-producing impersonal disposition. His motive and simplicity arguments are
substantive proposals, not an uncontested ranking. The paper's restrictions on
foreknowledge and rejection of classical timelessness are not imported here,
nor is its probabilistic machinery. The present route is an analyst qualitative
comparison, not a claim to have established his whole hypothesis.

This connects intellect with will: understanding a good supplies an intentional
content; aiming to realize it supplies a further explanatory commitment.
[Aquinas, ST I q.14 a.8 co.](https://www.newadvent.org/summa/1014.htm#article8)
likewise distinguishes an intelligible form merely being known from its
inclination toward a determinate effect through will. That passage supplies a
model of intellectual causation, not a proof that an unspecified first cause
has those powers. Source-level recognition and adoption of ends remain the
connection identified in the [moral-governance note](moral-governance-intellect-will.md).

| Compared account | Positive explanation | What would discriminate it here |
| --- | --- | --- |
| Purposive source | Understanding the good of finite agents motivates coordinated conditions for their knowing and action. | Does the same defended purpose explain the package, including its limitations, without separate adjustments for each datum? |
| Impersonal mind-inclusive order | Intrinsic powers, stable laws, learning and selection produce and sustain cognitive agents. | How much of the package follows from the specified powers and processes, and what remains an additional primitive? |
| Impersonal teleology | A tendency toward cognition or value organizes the order. | Is the tendency specified beyond its desired outcome, and does personal evaluative understanding add explanatory value? |

Assess the same package on each side: actual understanding and error,
correctable and entrenched mistakes, effective and impaired agency, embodied
dependence, and the relation between intellectual achievement and flourishing.
Selection and learning can explain useful truth-tracking; mere adaptive utility
does not settle every question about abstract understanding. Neither fact alone
selects a metaphysics. No new clinical or evolutionary study is reported here.

The proposed advantage is unification by an intelligible purpose. It is not a
count of unexplained labels, a numerical likelihood or an elimination of all
impersonal accounts. The same cognitive/world-order facts must not be counted
again as independent evidence simply because they also enter the moral or
intelligibility routes. This supplies a concrete research program for the
[theistic-best-explanation bridge](../../corpus/statements/cc100-116-theistic-best-explanation-bridge.json),
not an acceptance of its only-personal antecedent or a verified new consequence.

### Route B: the origination of an intellective principle

The other lead is a direct production argument. It must first say which being
understands. [ST I q.76 a.1 co.](https://www.newadvent.org/summa/1076.htm)
argues that the same embodied individual senses and understands. Merely having
Socrates's images represented in another intellect would make them understood;
it would not make Socrates the understander. Aquinas proposes the intellectual
principle as the substantial form of this human being. This is a positive
ownership candidate, already present in the q.75/q.76 reception work, now applied
to the source question. It does not automatically defeat physical constitution
or every account of subjects as aspects.

The candidate connection has four different commitments:

1. Some actual intellectual operation warrants an incorporeal, subsistent
   intellectual principle of this individual.
2. That principle has a cause of its existence and cannot be produced through
   transformation of a pre-existing substrate.
3. Its production is therefore creation in the sense of giving existence
   without transforming a presupposed subject.
4. Such production belongs to the first universal cause of being, rather than
   a secondary agent exercising an acquired or restricted power.

[ST I q.90 aa.2–3](https://www.newadvent.org/summa/1090.htm)
argues from mode of existence to mode of production: subsistent forms themselves
have being, unlike forms that arise only with their composites. It excludes
production of the rational soul from prior corporeal or spiritual matter and
assigns its creation immediately to God.
[Q.118 a.2](https://www.newadvent.org/summa/1118.htm)
repeats the operation–subsistence–creation connection. This use does not adopt
the article's embryology.

[Q.45 a.5 co./ad 1–3](https://www.newadvent.org/summa/1045.htm)
provides a further argument for the creator restriction: being absolutely is
the effect of the universal first cause, whereas instrumental production works
by disposing something already existing. Its own objections ask why an
immaterial secondary being could not produce its likeness, or why a finite
effect needs more than finite power. The article relies on earlier causal
metaphysics and divine-attribute arguments. A standalone reconstruction must
expose those dependencies rather than assume God in the creator premise and
then claim to infer God's existence.

The actual main vulnerability is already recorded in the
[human-intellect rival assessment](../human-intellect-rival-assessment.md):
a mechanism's own determinate constitution does not by itself limit its
representational range. An abstract object of thought is not automatically
evidence of a nonphysical vehicle. The [weak-subsistence result](../../corpus/statements/q75-intellect-weak-subsistence.json)
only excludes specified kinds of inherence. It does not already supply the
full incorporeality, causal origination, substrate exclusion or creator
restriction required above. These are interpretation/warrant obligations, not
new opaque premises asserted to settle them.

This is worth pursuing because it concerns a subject's intellectual principle
and its existence directly. It does not require a global premise that every
thinking effect has a prior episode-bearing thinker. Creation here does not
imply that the universe has a first temporal instant. No identity with the
selected `ActualConcreteGround` relation is inferred merely from the word
"cause". Any creator/root/intellect connection must retain the same witness.

### Catholic contribution and overall judgment

[CCC 362–368](https://www.vatican.va/content/catechism/en/part_one/section_two/chapter_one/article_1/paragraph_6_man.html)
affirms one human nature in the unity of body and spiritual soul, and separately
teaches immediate creation and immortality. This makes the ownership and
origination questions directly relevant to Catholic anthropology. The doctrinal
text identifies the proposed worldview's commitments; it is not philosophical
proof of them. Weak subsistence, natural incorruptibility, personal survival and
bodily resurrection remain different conclusions. Q.75 a.6 adds an
incorruptibility argument; it does not make the soul independent of its creator.

An intentional foundation and rational receivers would also make purposive
revelation an intelligible kind of interaction. Actual revelation, a particular
resurrection and Church identity still require the distinct evidence in the
[Catholic-case stages](../catholic-case.md#root-and-structure). This work selects
neither the Trinity nor Catholicism over other theisms, and does not recast
human subjects as parts of God.

My provisional research priority is Route A: the coordinated reality of
understanding, intelligibility and agency is a more informative target for
intellect-and-will identification than phenomenal occurrence alone. This is a
judgment about expected explanatory value, not a demonstrated ranking of the
complete metaphysical systems. Route B is a specific complementary connection
to investigate where the stronger intellectual-subsistence premises can be
defended. Their conjunction is not required to explore either route.

The [same-root intellect/will target](../../corpus/statements/root-intellect-will.json)
remains the graph destination. If other work warrants a necessary root, Route A
can ask whether that same root is purposive; it must not silently replace it
with a different mental source. Route B can ask whether an intellective
principle's production requires that first source. Neither investigation has
yet changed the root conclusion's establishment or supplied a new formal edge.

The next bounded tests are (A) whether one independently articulated good of
finite rational agency explains the compared cognitive/world-order package
better than the specified impersonal accounts, and (B) whether the defended
q.75 principle has exactly the mode of existence needed by q.90, followed by
the separate q.45 restriction on secondary creators. Reuse the existing
content/basing and bodily-interference comparisons; do not substitute another
conditional proof for those substantive tests.

## Rational participation: completed purpose comparison (2026-11-19)

The owner selected Route A. This continuation starts from
`ef99cc09989997f8ed2e985b059723792018ac19` and completes its bounded comparison:
does one fixed good of finite rational agency distinguish a purposive source
from developed impersonal accounts? The result is positive explanatory
unification with a limited comparative consideration, not an overall victory
for a personal source. The earlier Route B and thinking-ancestor assessments
are unchanged. This is a qualitative warrant assessment, with no new formal
result or change to the registered propositions. [Assessment record](../../corpus/attempts/9ee981ac-d0bf-4006-bfab-2ef8a5ff8dd7.json)

### Fix the purpose before accommodating the outcome

**P:** distinct finite subjects participate in goods through their own
understanding, response to reasons, effective action and relationships.

P values understanding itself, rather than only the useful conduct it can
produce. Its prima facie rationale is available in ordinary comparisons:
learning why an answer follows is an achievement beyond receiving it, and
informed participation adds something to being efficiently managed. This is
not a condition of human worth or a claim that people with greater cognitive
abilities matter more. Accepting that good requires neither a prior proof of
theism nor the conclusion that every possible instance must be created.

P gives a source that understands and adopts it related reasons for accessible
evidence, sufficiently stable action–outcome relations, effective powers and
other participants. These are coordinated means to one end, not separate
preferences invented for each observation. Necessity as an enabling condition
is conditional: sufficiently reliable order is needed *if* this kind of
embodied agency is to be sustained. It neither produces agents by itself nor
establishes that a source would create them.

[Aquinas, ST I q.19 aa.2–3](https://www.newadvent.org/summa/1019.htm)
offers communication of goodness as a rationale while denying that divine
goodness necessitates creation. Those passages presuppose divine intellect and
will; here they articulate P, not prove its attribution to the root.
[Swinburne 2011, manuscript pp.9–10](https://users.ox.ac.uk/~orie0087/pdf_files/Papers%20from%20Philosophical%20Journals/Swinburne_2011-explanation.pdf)
connects efficacious finite choice with an orderly environment. Reuse only that
means–end argument, with the earlier restrictions on his wider theology.

### What the purpose actually discriminates

Consider two analyst descriptions with the same immediately useful outcomes:
subjects reach them through understood reasons, or reach them through cueing
that bypasses their apparent reasoning. P provides a reason to prefer the
first, other relevant goods and costs equal. Likewise, P favors accessible
correction over an otherwise comparable arrangement that systematically blocks
subjects from identifying their errors. These are limited comparisons, not
certified possible worlds holding every physical condition fixed, and not
proofs of a unique best creation.

The comparisons give P content: merely installing correct behavior does not
fulfil the stated purpose. They discriminate against a criterion restricted
to the fixed useful outputs. They do **not** yet discriminate against a
naturalistic account of actual understanding. The existing
[basing analysis](epistemic-underminer-boundaries.md#rational-basing-the-particular-transition-must-exercise-the-capacity)
already separates an exercised content-sensitive capacity from a bypass; its
physical realization remains available. We reuse that result rather than
counting the contrast as a new anti-physicalist argument.

P also imposes constraints on explanations of failure. Finitude entails
limited knowledge, not false belief: one could know fewer truths without
believing falsehoods. Learning need not consist in correcting error. Effective
agency gives a reason for consequential action, not an automatic reason for
extreme suffering, entrenched deception or the destruction of agency. Such
conditions are adverse to this particular end, although an overall judgment
must consider other goods, feasibility and costs. Invoking those considerations
without showing their connection supplies permission at most, not an
explanation of the actual distribution.

[Q.47 aa.1–2](https://www.newadvent.org/summa/1047.htm)
motivates diversity among creatures; it does not directly justify arbitrary
inequalities in human opportunities. The
[optimal-creation comparison](optimal-creation-choice.md#verified-source-readings),
using q.25 a.6, already blocks the assumption that perfect making requires a
globally maximal product. That qualification does not erase P's local
preference for understanding and corrigibility.

### The developmental comparator explains a specific mixed profile

Use the positive producer/consumer account in
[the intentionality note](intentionality-943.md#multiple-functions-and-stable-factual-guidance-2026-11-14):
tracking a fact can guide opposed goals, so selection for successful action
need not select only comforting or immediately rewarded belief. Add constrained
reuse and cultural correction rather than an unexplained unlimited learner.

[Dehaene and Cohen (2007), pp.384–385](https://www.unicog.org/publications/DehaeneCohen_CulturalRecyclingCorticalMaps_Neuron2007.pdf)
propose that cultural abilities recruit older cortical resources and inherit
their constraints. This supplies a developmental proposal for abilities beyond
their precursors' original uses, not a proof that neural activity exhausts
understanding. [Trouche, Sander and Mercier (2014), Experiments 1–4](https://moodle2.units.it/pluginfile.php/745149/mod_resource/content/0/Trouche%2C%20Sanders%20%20Mercier%202014.pdf)
found that argument quality could support correction without confidence cues,
and that many participants transferred understanding after group discussion.
Experiment 3 included a modified transfer problem whose correct answer
differed from the original. That makes mere repetition an inadequate account
of successful transfer in those tasks. It does not establish universal rational
reliability, a complete evolutionary history, or the metaphysics of reasoning.

This comparator positively connects reusable factual guidance, learning,
dependence on presentation and training, individual error, and correction
through others. At that explanatory level it is more informative than the bare
statement that rational agency is good. A purposive source can use precisely
those processes; it then shares their explanatory success rather than gaining
another independent confirmation from it.

Three proposed discriminators consequently fail to identify the ultimate
source here: transfer beyond the initial task, changed answers when the
relevant reasons change, and correction through criticism. All can express the
flexible cognition the developmental account proposes. Nor does mathematical
thought's distance from immediate survival alone discriminate: reuse and
cumulative learning offer an actual alternative to direct selection for each
later accomplishment. This does not show that all theoretical understanding
has been explained. It shows why the inspected successes cannot simply be
assigned to one ultimate-source hypothesis.

Some stability and cognitive success are also prerequisites for observers like
us. Observer selection does not produce a universe or explain its laws, but
the comparison must condition observations appropriately. Do not count the
mutually dependent prerequisites of inquiry as three independent surprises.

### Compare explanations of the order at the same scope

The developmental proposal can be combined with different ultimate accounts.
The relevant comparison holds those local mechanisms fixed and asks what,
if anything, explains the order that supports them.

| Account of the order | Positive explanation | Distinctive application burden |
| --- | --- | --- |
| Source understands and adopts P | One valuable end makes the coordinated conditions intelligible as means. | Why attribute productive understanding and actual adoption to this source, given both successes and frustrated agency? |
| Impersonal intrinsic powers and laws | The order's determinate powers support development without an additional source-level intention. | Whether those powers adequately explain the order as a whole, or remain a defensible primitive; local developmental evidence alone does not decide. |
| Impersonal value-directed teleology | One valuable outcome restricts which developmental histories are favored. | Whether the proposed directed law is sufficiently determinate and warranted beyond fitting its intended result. |
| Direct creative value | The worth of an order explains its realization without a prior subject adopting it. | Why evaluative requiredness has productive efficacy, beyond its normative significance. |

[Nagel, *Mind and Cosmos*, ch.4, pp.91–93](https://studylib.net/doc/18288842/mind-and-cosmos---ch.-4)
provides the third account's actual structure: teleological principles favor
physically admissible paths toward valuable higher organization, consciousness
and reason. It is an additional directed law, not arbitrary nonintentional
bias. The proposal has an explanatory form but no calibrated law in this
passage. Applying it to P's exact package, or to our same necessary root, is
our reconstruction rather than a claim that Nagel established either.

[Leslie's own interview answers](https://closertotruth.com/news/an-interview-with-john-leslie/),
under the axiarchism question, supply the fourth account: ethical requiredness
itself produces existence unless overridden by a stronger requirement. His
ultimate explanation is impersonal even though his proposed reality contains
infinite minds. This is a substantive alternative, not a wholly mindless
cosmology. Its productive-value principle is an additional commitment; moral
realism alone does not entail it.

[Swinburne 2011, manuscript pp.18–19](https://users.ox.ac.uk/~orie0087/pdf_files/Papers%20from%20Philosophical%20Journals/Swinburne_2011-explanation.pdf)
does consider an impersonal source disposed to produce good. His simplicity
comparison construes it as a physical substance with location and specified
powers. That reasoning does not automatically dispose of nonphysical
impersonal grounds or Leslie's nonobjectual Good. The reusable positive point
is that understood reasons can motivate production.

### Test whether value-sensitive production requires representation

Distinguish an accidentally valuable output, a disposition directed toward
value, and an agent acting because it understands a good. The first does not
explain value-directed variation. The latter two offer different explanations
of such variation.

Try varying the reason-relevant circumstances or feasible alternatives while
holding evaluative standards fixed. Appropriate changes in what is produced
would challenge a fixed-output explanation. They would not by themselves
identify an understanding producer: Nagel's proposed end-directed law and
Leslie's stronger-requirement condition both allow responsiveness to changed
value-relevant circumstances without a representing source. Neither source
supplies a completed model of every such variation, but neither is the
fixed-output foil. Requiring that the change occur *because the producer
apprehends the reason* would import the personal explanation into the test.

The completed test therefore rejects this shortcut: normative reasons are not
automatically efficient causes, **therefore** only a mind can connect them to
production. The premise correctly separates normative support from productive
efficacy; the exclusive conclusion does not follow. Impersonal teleology
attributes directed powers to the order, not necessarily efficient pushing by
an abstract proposition. This is an assessment of that inference, not a
certified countermodel or a demonstration that the rival is true.

There is a further limit on a familiar diagnostic. With human agents, mistaken
belief can redirect conduct while the actual reasons remain unchanged; that
helps distinguish represented value from actual value. If the candidate
source is essentially omniscient, those variables cannot be separated through
an ordinary possible error by that source. A hypothetical divine mistake
would then be a counterpossible, not new evidence of representation. This
conditional point neither assumes omniscience for every purposive source nor
establishes it for the root.

Personal explanation nevertheless has a positive comparative consideration:
understanding and acting for goods already make some human production
intelligible. Direct creative value adds a productive relation not supplied
by the fact that something is worth realizing. I give the former a limited
prima facie advantage on this explanatory consideration. It is qualified by
the fact that our familiar agents are embodied and dependent, whereas an
ultimate source need not be. Extending practical explanation to that source
is substantive, not a free extrapolation. Intrinsic powers also have familiar
applications; Nagel adds their direction toward value. Familiarity alone
does not settle which extension is better overall.

### Overall judgment and consequence for the case

The fixed purpose passes the positive-unification test and excludes
unrestricted accommodation: understanding and access to correction are goods
within it, and their frustration counts against fulfilment of that end. It
provides an intelligible motive for a personal source and the limited
comparative consideration just stated. **This comparison does not establish
that the coordinated cognitive order favors a personal source overall over
the strongest impersonal completions.** That is a scoped judgment, not a
declaration that the rivals have equal plausibility or that primitive
commitments have no warrant.

The completed tests tell us where explanatory credit belongs. Actual basing
supports personal reasoning; transfer and criticism support flexible cognitive
development; P supplies a source-level rationale; a successful comparison of
ultimate accounts would be needed to attribute that purpose to the root.
These are different contributions of the same evidence, not independent
votes for God. The observed cognitive corrections do not establish that last
attribution, and adding a generic counterfactual-sensitivity condition does
not repair it.

This bears on the existing
[theistic-explanation bridge](../../corpus/statements/cc100-116-theistic-best-explanation-bridge.json),
but does not accept its
[only-personal antecedent](../../corpus/statements/cc100-116-personal-explanation-restriction.json).
The candidate abductive route can instead compare purposes without first
excluding every impersonal account; no replacement formal edge is registered
by this note. For the
[same-root target](../../corpus/statements/root-intellect-will.json),
necessity must come from the same independently warranted root. This comparison
does not derive necessity from intelligence, or choose a new mental source
and silently identify it with the existing root. Recognition, practical
adoption and production retain the distinct applications in the
[divine-love note](divine-love-goodness-bridge.md#practical-adoption-at-fixed-production-proposed-continuation)
and [moral-governance note](moral-governance-intellect-will.md).

The bounded question now has an answer; repeating broad comparisons of order,
truth and usefulness will not improve it. A stronger ranking would require a
source-specific consequence that survives the shared developmental explanation,
or additional warrant about the same root's productive nature from the existing
attribute work. The inspected empirical sources supply no such discriminating
ultimate-source consequence, and the present P does not determine the full
distribution of successful and frustrated agency. These are the concrete
limits of this test, not demands for a further proof of every premise.

Reopen this assessment if a defended source account constrains that distribution
more successfully, if an independently motivated teleological law explains it,
or if same-root recognition/adoption receives substantive support. Preserve P's
content when testing adverse cases; do not add disconnected purposes after each
failure. This completion contributes a motivated, constrained theistic support
option and rejects two tempting shortcuts. It supplies no new necessary-intellect
conclusion and no specifically Catholic identification; the historical-stage
boundaries stated above remain unchanged.

## Does divided access identify the source of the experiencer? (2026-11-25)

DDC's reports after callosal disconnection give a reason to take continuity of
his experienced agency seriously. His performance also shows that access to an
item depends on what he is asked to do with it. This tests the earlier R/T/X
comparison against one human case. The question for #1792 is whether the best
account of these two findings identifies a distinct thinker on which this
very experiencer depends for existence. [Assessment record](../../corpus/attempts/2f24e4c3-e987-4e4d-8752-1ae3522b2c3d.json)

### What changed with the task

Pinto and colleagues studied two people with complete callosal section. DDC,
whose anterior commissure was also largely sectioned, took part in the detailed
comparisons. With central fixation monitored during brief stimulus presentation
and an examiner unable to see the test stimuli, he could detect and locate a
single target in either visual half-field by voice or with either hand. Catch
trials contained no target. Yet when asked to compare two stimuli, his mean
accuracy was 90.4% within one field and 55.4% across fields, the latter
statistically indistinguishable from chance. DDC and DDV both described seeing
the whole field, feeling in control of their bodies and experiencing continuity
of conscious unity. That testimony is evidence about how agency felt to each
speaker. A speaker's access to a second perspective, if there were one, is
precisely what is in dispute. [Pinto et al. (2017), Methods, experiments 1–2,
figures 2–3, and phenomenal reports on p.1235](https://pure.uva.nl/ws/files/21255810/Split_brain.pdf)

A later test in **DDC himself** changed the information required for a correct
answer. He often expressed high confidence in an unsuccessful simultaneous
cross-field comparison. In a sequential task he saw a square or circle, then
an X or a question mark. X called for reporting X. A question mark required
reporting the *earlier shape*. Accuracy was 68.7% on those question-mark trials
with the cue across fixation, significantly above the authors' chance baseline.
Thus success on the full task cannot all be credited to trials permitting the
first shape to be ignored. Eye position was checked at each presentation.
In a simultaneous control with the same stimuli at the same positions as in
the sequential task, DDC's cross-field same/different judgments stayed at
chance. Stimulus identity and position therefore do not explain the difference
by themselves. Timing and the response rule still changed together. The authors propose a slower
route carrying more abstract information alongside impaired rapid visual
integration. Their study does not identify that route's anatomy. A correct
delayed answer requires less than simultaneous awareness of two detailed images.
[Pinto et al. (2023), methods and results of experiments 1–2, figures 2–5 and
general discussion](https://doi.org/10.3389/fnhum.2023.1278025)

There is genuine contrary testimony. In Sperry's earlier series, a participant
disclaimed authorship on seeing her own left-hand response. With different
figures flashed in opposite fields, a hidden left hand could draw one while
speech identified the other as the figure just drawn. Sperry favored two
conscious streams and explicitly recorded individual exceptions. These reports
have evidential weight against treating ordinary verbal self-description as an
inventory of every perceptual discrimination or action. They came from other
participants. [Sperry (1968), pp.725–726, 732–733](https://people.uncw.edu/puente/sperry/sperrypapers/60s/135-1968.pdf)

The objections to a unified agent also have testable content. A gaze or body
cue can make limited information available after a flash, and ipsilateral motor
control could let a single hemisphere direct a simple pointing response.
Pinto's team prevented hand-to-hand and cross-body contact, obtained fairly
precise locations, and found no significant crossed-hand timing penalty in a
speeded colour task. Those findings put pressure on a slow serial cue for every
answer. Motor control alone leaves verbal answers unexplained. Conversely,
fixation control during exposure does not exclude every cue during response,
and a location signal can help pointing without carrying shape identity. The
published disagreement concerns the route and amount of information available
for particular tasks. Either route can operate within an account accepting
real experiences. [Pinto et al. (2017), Discussion, pp.1235–1236](https://pure.uva.nl/ws/files/21255810/Split_brain.pdf)
and [Volz et al. (2018), pp.1–3](https://doi.org/10.1093/brain/awx359)

### What could individuate the owner?

Grant the personal-constitution proponent the strongest starting point here:
DDC experiences the successive demands as addressed to him, and can sometimes
use an earlier item to answer a later question. That makes it reasonable to
credit an actual point of view. An already experiencing whole offers a positive
model for why an aspect can have subjective character at all. The
nonidentity proposal extends that explanation to a *distinct subject's
existence*. To test the extension, hold the larger subject U fixed and specify
what singles out this finite perspective. Try a rule by which contents belong
to the same local owner just when they can guide a common judgment. This is an
analyst's test of a possible individuation rule. [Chalmers, *Idealism and the
Mind-Body Problem*, pp.23–24, on the identity and nonidentity proposals](https://consc.net/papers/idealism.pdf)

* **Immediate comparison** makes the boundary track stimulus placement and
  report format. Taken as the criterion for a persisting subject, it would let
  a failed comparison count against common ownership even within the life that
  DDC experiences as continuous. What succeeded was a delayed verbal report
  of the earlier shape after a cue in the opposite field. The request could
  reach the side retaining the shape and prompt an answer there. The task
  leaves open whether the shape information crossed and who owned the memory.
  Neither result locates an occasion on which an experiencer came into being.
* **Availability across time or by any route** explains how local channels
  can serve one agent. But information also crosses between people by cues
  while each retains a point of view. A rule using only successful transfer
  therefore needs a principled boundary between communication and constitution.
  Restricting the rule to the continuing organism gives an independent way to
  track DDC across the tasks. An account on which DDC is that organized living
  individual can use exactly the same boundary.
* **Numerical identity with U** allows a single subject to have experiences
  under modes with different access. It must explain which access restrictions
  persist when the task changes. Even a successful explanation on that reading
  gives U = x, whereas the distinct-ancestor premise requires a witness c ≠ x.

Both accounts can identify DDC, the continuing embodied individual, as the
bearer. Both can explain task performance through the same distinction between
rapid visual comparison and the use of retained information for a later report.
The organizational sufficiency thesis says the individual's organization and
powers suffice for this subject to exist without a distinct thinking ground.
On the personal constitution proposal, this same individual's existence as an
experiencer depends on a distinct experiencing whole U. The latter proposal draws
support for the familiar dependence of experiential
aspects on a subject and for explicitly addressing the bearer. Its extra
explanatory burden is why a restriction of U constitutes someone else who
experiences at all. [Earlier whole-to-aspect and bonding comparison](#completed-comparison-one-subject-two-contents)

A personal source would gain comparative warrant over a nonthinking one if
its independently motivated way of individuating subjects explained both why
this owner exists and which changes preserve it, where the organizational
account gives a wrong identity verdict on independent grounds. One concrete
test is to distinguish **continuing ownership of a remembered item** from
**receiving enough information from its original owner to answer correctly**.
The sequential task is a useful control against interpreting every correct
answer as simultaneous comparison. It scores the answer in both ownership
scenarios alike. Even first-person recognition of the item as previously seen
would bear on experienced continuity. Moving from that recognition to a
distinct constitutor would still require a reason why the bearer's existence
depends on U. Partial constitution of something capable of a conscious quality
likewise leaves open whether its *bearer* depends for being on a distinct
episode-bearing subject. [Existing best-constitution statement](../../corpus/statements/cc100-123-god-mind-best-constitution.json)

### Where the root inference would use the result

In the selected profile and world let x bear an occurring thought. A capacity
for cognition, a visual quality and a report occasion are each different from
the actual being bearing the episode. For #1791, **P_med(x)** needs a distinct
c bearing an occurring thought and a nonempty finite path from c to x whose
steps are `ActualConcreteGround m w`. Each step requires an existing concrete
source and `m.grounds w` relating it to the next being. Interpreting occurrence
at w is part of the application, since `Occurs` itself has no world index.
The constitutor's own occurrence, its distinctness, and dependence of x for
*existence* along this very path would together supply the local instance.
An organizational contributor to reports, a temporally earlier perceiver, or
a fact partly constituted by U supplies no such path by itself. **P_dir(x)**
requires direct existential support from a distinct thinker. A mediate path
can end with a nonthinking intermediary. [Fixed dependence senses](../../corpus/disambiguations/1272a7e5-e3e1-4c91-a1d3-343018262841.json)
and [formal predicates](../../TruthCore/Causality/ThinkingRootFork.lean)

Even a successful local instance would leave the quantifier in
`ThinkingBearerConeNoFresh`: for each eligible starting bearer and episode,
*every* thinking member of its cone with an incoming G edge must have such a
predecessor. With the cogito, bearer actuality and concreteness, accessibility
of distinct thinking predecessors, contingent-thinker grounding and excluded
middle, `necessaryThinkingRootOfThought` obtains one n that thinks, is a
reflexive-or-transitive ancestor of the starting bearer b, is an actual G-root,
and exists at every accessible world. The endpoint allows n = b. #1787's
supplied-root continuation would have to retain that same n through the
fixed-esse common-root argument. The existing `godOfRoot` helper also requires
first-being priority, its causal and perfection premises and the naming premise
at n. An occurrence in n does not settle its intellectual cognition or will.
[No-fresh premise](../../corpus/statements/dc7e315d-a364-48f2-9e61-d2aaec966e80.json),
[registered #1791 argument](../../corpus/arguments/a66aacdc-fe5b-4fc2-a6d3-00c639cbb6f4.json),
[conditional result](../../corpus/results/60df7e87-ea14-4212-9749-4d4e0dd8576d.json)
and [supplied-root naming helper](../../TruthCore/Results/Causality/DirectEsseRootGodExistence/Solution.lean)

**Provisional judgment.** DDC provides positive evidence for experienced
continuity with task-dependent access. Both metaphysical accounts share the
explanatory credit for the task-specific access mechanism. The results leave
open whether organization suffices for this embodied subject's existence
without a distinct thinking ground.
The access test thus reaches a definite limit. Reopen the ancestry question
for an independently warranted criterion of subject constitution that makes
the remembered-item distinction and explains why the same bearer's existence
has the required ground. Further accuracy or confidence measurements alone
would refine the account of access. This is a nonformal warrant assessment.
