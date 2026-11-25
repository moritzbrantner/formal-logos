"""Local, finite research controls. No metaphysical or Lean certification.

Test a candidate *constitutive* perfective order. Positive content and actual
intrinsic restrictions are independent finite assignments; restriction markers
are not derived from a comparison or an edge. All bearers in this audit are
actual. No represented causal/receipt adapter or grade calibration is asserted.
"""
from itertools import product


def subsets(xs):
    xs = tuple(xs)
    return [frozenset(x for i, x in enumerate(xs) if m & (1 << i))
            for m in range(1 << len(xs))]


def profile(has, pure, restricts):
    assert restricts <= has - pure
    return (has & pure, restricts)


def at_least(a, b):
    # a no poorer in actual positive content, no additional intrinsic limiter.
    return b[0] <= a[0] and a[1] <= b[1]


def more(a, b):
    return at_least(a, b) and not at_least(b, a)


def exhaustive():
    D = frozenset(range(3))
    S = subsets(D)
    assignments = qualifying = pure_ties = distinct_equivalent = 0
    for pure in S:
        rows = [(h, k) for h in S for k in subsets(h - pure)]
        for rs in product(rows, repeat=3):
            assignments += 1
            ps = [profile(h, pure, k) for h, k in rs]
            for i in range(3):
                assert at_least(ps[i], ps[i]) and not more(ps[i], ps[i])
                for j in range(3):
                    a, b = ps[i], ps[j]
                    assert not (more(a, b) and more(b, a))
                    assert (at_least(a, b) and at_least(b, a)) == (a == b)
                    if i != j and a == b:
                        distinct_equivalent += 1
                    if i != j and a[0] == pure and not a[1] and b[1]:
                        qualifying += 1
                        assert more(a, b)
                        if a[0] == b[0]:
                            pure_ties += 1
                    # Complete purity is sufficient but not necessary for zero restriction.
                    if rs[i][0] == pure:
                        assert not a[1]
                    for k in range(3):
                        c = ps[k]
                        if at_least(a, b) and at_least(b, c):
                            assert at_least(a, c)
                        if more(a, b) and more(b, c):
                            assert more(a, c)
    print(f'{assignments:,} three-bearer profiles; {qualifying:,} full-content/restriction-free source–restricted-recipient instances, including {pure_ties:,} pure-content ties: all strict in the candidate order.')
    print(f'{distinct_equivalent:,} ordered distinct-bearer equal-profile pairs: no identity inferred.')
    assert pure_ties and distinct_equivalent


def omissions_and_scope():
    p, q, r, s = range(4)
    # Actualized receiving potency may remain while ordinary unactualized potency
    # is empty. Both have every stipulated positive content. Only x bears the
    # independently assigned real esse restriction r.
    pure = frozenset({p, q})
    n = profile(frozenset({p, q}), pure, frozenset())
    x = profile(frozenset({p, q, r}), pure, frozenset({r}))
    assert n[0] == x[0] and more(n, x)
    # A mere non-pure individuating determination, not stipulated restrictive,
    # does NOT break the tie. Nor does any number of neutral determinations.
    neutral = profile(frozenset({p, q, s}), pure, frozenset())
    assert n == neutral and not more(n, neutral)
    # Loss of source completeness makes a genuine tradeoff possible.
    less_content = profile(frozenset({p}), pure, frozenset())
    assert not at_least(less_content, x) and not at_least(x, less_content)
    # Loss of source freedom from restrictions allows equal content AND same
    # actual restrictions. A causal difference does not change this order.
    assert not more(x, x)
    # Received intermediates with distinct restrictions, even equally complete,
    # need not be ordered. No cffad050 or d5a94eb1 is inferred.
    y = profile(frozenset({p, q, s}), pure, frozenset({s}))
    assert not at_least(x, y) and not at_least(y, x)
    # Calibration is not just 8176a284 repeated: with a real causal edge n->x
    # and an independently restricted non-effect y, scoped ascent can hold
    # while calibration fails at the noncausal pair n,y. Conversely, if identity
    # is supplied but the positive-completeness input fails, calibration can
    # hold while scoped ascent fails at the causal pair.
    profiles = [n, x, y]
    causes = {(0, 1)}
    identity = {0}
    cmp = {(0, 1)}
    ascent = lambda C, I, M: all(a not in I or (a, b) in M for a, b in C if a != b)
    calibrated = lambda ps, M: all(not more(a, b) or (i, j) in M
                                   for i, a in enumerate(ps) for j, b in enumerate(ps))
    assert ascent(causes, identity, cmp) and not calibrated(profiles, cmp)
    profiles = [less_content, x]
    cmp = {(i,j) for i,a in enumerate(profiles) for j,b in enumerate(profiles) if more(a,b)}
    assert calibrated(profiles, cmp) and not ascent(causes, identity, cmp)
    print('Controls passed: positive-content tie, neutral determination, tradeoff, shared restriction, incomparable intermediates, and two calibration/ascent non-entailments without the mediating hypotheses.')


if __name__ == '__main__':
    exhaustive()
    omissions_and_scope()
