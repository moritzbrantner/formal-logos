# Divine justice: wisdom-governed conformity to due order (#1457)

Complete proposed outcome, 2026-11-17. Baseline `91bcc8db`; the delivered
revision is the PR head. Analyst reconstructions with attribution deferred
(owner direction 2026-11-05); no claim, passage or source record is created.

## Question and destination

Does an account of divine justice give the existing open veracity premise
`Veracity GodAssertionsPermitted` (9286d83c, reaches the root, previously with
no concluding argument) a non-question-begging support option? The issue asks
for a justice route that is not a lexical switch from ontological goodness
(`GOD_4` is supremely good) to moral goodness.

Source orientation (read in full, ST I q.21 aa.1–4, English Dominican
translation, New Advent): a.1 co. distinguishes commutative from distributive
justice and denies the former of God; a.1 ad 2 says God cannot will anything
but what His wisdom approves, which is "as it were" His law of justice; a.1
ad 3 derives what is due to creatures from their ordering under divine wisdom
and denies that God is a debtor; a.2 calls God's justice truth because it
establishes things in the order conformable to wisdom's rule, and places
justice as law in the intellect and as command in the will; a.4 co. says
whatever God does in creatures is done according to proper order and
proportion; a.4 ad 3 answers the afflicted-just objection by the purifying
and elevating function of affliction. These are navigation, not attributed
claims.

## Formal outcome

Vocabulary `TruthCore.Causality.DivineJustice1457` (DEF a047c2db): `Order`
with `Wills`, `Approves`, `Fitting`, `DueTo`, `assertion`; no field laws.
Two senses of divine justice (DISAMB 530c775b): JUSTICE_1 `GodActsJustly`
(every willed act is fitting) and JUSTICE_2 `GodRendersAllDue` (every due act
is willed).

| Result | Premises | Conclusion |
|---|---|---|
| `justiceFromWisdom` | will only what wisdom approves; approval tracks due order | JUSTICE_1 |
| `permittedFromJustice` | JUSTICE_1; assertion is willed; fitting assertion is permitted | existing `GodAssertionsPermitted` |
| `voluntaristTrivializes` | Fitting ≡ willed by some GOD_4 | JUSTICE_1 |
| `controls` | none | structural certificate below |

All proofs are zero-axiom. The certificate gives a joint Boolean sample (a
classified bearer actually asserts `True` and wills the fitting act, every
route premise holds); four omission samples (each drops one premise of an
argument, keeps the others, and loses the conclusion); a sample where both
premises of JUSTICE_1 hold, an act is due and not willed, so JUSTICE_2 fails;
and one will profile (the bearer wills every act) that satisfies JUSTICE_1
under the voluntarist reading and fails it when `Fitting` is the independent
standard `· = true`. These are skeleton interpretations, not witnesses of
classical theism or of any moral theory.

## Findings

1. **New conditional support option.** `GodAssertionsPermitted` now has a
   verified route: JUSTICE_1, `GodAssertionIsWilled`, and
   `FittingAssertionPermitted`. JUSTICE_1 itself has a route from
   `GodWillsOnlyApproved` and `GodApprovalTracksOrder`. The direct-assumption
   option for `GodAssertionsPermitted` remains; nothing is discharged.
2. **The non-voluntarist content sits in one premise.**
   `GodApprovalTracksOrder` is where the Euthyphro question lives. If `Fitting`
   is read voluntaristically, JUSTICE_1 follows from that reading alone for
   *every* will profile (`voluntaristTrivializes`), so it adds no constraint,
   and the permission route reduces to "whatever a GOD_4 wills to assert is
   permitted", a divine-command account of permission. That is a coherent
   rival account; it is not refuted here. What the result shows is that it
   cannot be used as *independent* support for the veracity norm: the
   veracity route then needs the separate act-object norm
   `ContraryAssertionImpermissible` to do all the work. The control
   `VoluntaristDivergence` exhibits the two readings disagreeing on one
   profile, so the distinction is not merely verbal.
3. **JUSTICE_1 does not give JUSTICE_2.** Conformity of every willed act to due
   order, even with both its premises, leaves room for dues that are not
   rendered. The objection from the afflicted just (q.21 a.4 obj. 3) targets
   JUSTICE_2 directly. It reaches JUSTICE_1 only with a further premise that
   withholding a due is itself an unfitting willed act; that premise is not
   encoded, and Aquinas's a.1 ad 3 (creaturely debt derived from wisdom's
   order) and a.4 ad 3 suggest he would deny the unrestricted form. The route
   to `GodAssertionsPermitted` uses JUSTICE_1 only and so does not inherit the
   evidential burden of JUSTICE_2.
4. **Ontological goodness is not used.** No premise mentions
   `GodIsSupremelyGood`; the route does not pass from GOOD_4 to moral goodness.
   This answers acceptance item 4 of the issue by construction, not by an
   omission model across vocabularies (which would be trivial).

## Strongest standing rivals and their price

- **Voluntarism / divine-command permission.** Target:
  `GodApprovalTracksOrder` read as non-voluntarist. Mechanism: if due order is
  constituted by divine willing, the premise is trivially true and carries no
  independent constraint. Price, derived above: the justice route then gives
  no support to divine veracity beyond a command account of permission. No
  conflict with an accepted floor item has been shown, so the rival stands.
- **Natural-law realism without a divine legislator.** Target: none of the
  route premises; it accepts an independent `Fitting`. It contests a different
  question (whether due order needs a divine ground), which this batch does
  not address.
- **Consequentialist permission of beneficial deception.** Target:
  `FittingAssertionPermitted` only if fittingness is read as welfare-maximising;
  this is the same live rival recorded in `divine-veracity-1410.md` and is
  not re-argued here.

No substantive objection was identified to the inference steps themselves.

## Open premises introduced

`GodWillsOnlyApproved`, `GodApprovalTracksOrder`, `GodAssertionIsWilled`,
`FittingAssertionPermitted` (all OPEN, analyst formulations). The voluntarist
reading is a rival assumption, not a route premise.

## Provisional judgment (2026-11-17)

`GodAssertionIsWilled` is provisionally well supported on ordinary action
theory (genuine assertion is a voluntary act); no substantive objection is on
record. `GodWillsOnlyApproved` is the Thomist reading of q.21 a.1 ad 2 and is
plausible given a will whose object is the understood good, but the
inference from "will's object is the good as understood" to "wills only what
wisdom approves" needs actual perfect wisdom, not merely intellect.
`GodApprovalTracksOrder` and `FittingAssertionPermitted` carry the
substantive normative weight and remain underdetermined by present evidence.
Overall: the route clarifies *where* the moral warrant for divine veracity
must come from (independent due order plus its right-making force), without
raising the support of the conclusion above that of those two premises.

## Next tests

1. Identify `Fitting` on creatures with `DEF-FORM-END-DUE-PERFECTION`
   (`GoodnessFormEnd.Frame.Due`) through an explicit bridge, and test whether
   JUSTICE_2 restricted to *natural* dues of the form survives the
   afflicted-just objection under q.21 a.4 ad 3.
2. Mercy (q.21 a.3) as defect-removal beyond due: show it is compatible with
   JUSTICE_1 (giving more than due is not unfitting) and record the premise
   that blocks the "mercy relaxes justice" objection (a.3 obj. 2).
3. Connect `GodWillsOnlyApproved` to the q.19 will vocabulary and the
   intentional-willing question of #1459.
