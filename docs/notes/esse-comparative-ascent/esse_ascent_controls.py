"""Standalone finite checks of the proposed logical substitutions.
Not repository tests, Lean certification, or metaphysical models.
"""
from itertools import product

B = range(3)
pairs = [(c, x) for c in B for x in B if c != x]
all_pairs = list(product(B, repeat=2))

def subsets(items):
    for mask in range(1 << len(items)):
        yield frozenset(x for i, x in enumerate(items) if mask >> i & 1)

def maxima(A, M):
    return {m for m in A if not any((y, m) in M for y in B)}

def genus(A, C, maxima_):
    return all((m, x) in C for m in maxima_ for x in A if x != m)

def causal_actuality(A, C):
    return all(x not in A or c in A for c, x in C)

def maximal_target_asym(A, C, maxima_):
    return all((m, c) not in C for c, m in C if c in A and m in maxima_)

def no_incoming(C, maxima_):
    return not any(x in maxima_ for c, x in C)

def universal(A, C, n):
    return n in A and all((n, x) in C for x in A if x != n)

def run():
    cases = 0
    antecedents = 0
    nonvacuous = 0
    for A in subsets(list(B)):
        for M in subsets(all_pairs):
            maxs = maxima(A, M)
            for C in subsets(pairs):
                cases += 1
                if genus(A, C, maxs) and causal_actuality(A, C) and maximal_target_asym(A, C, maxs):
                    antecedents += 1
                    nonvacuous += bool(maxs)
                    assert no_incoming(C, maxs)
                    assert len(maxs) <= 1
    print(f"Maximal-target asymmetry + fixed-esse genus + cause actuality: {cases:,} assignments, {antecedents:,} antecedent-satisfying, {nonvacuous:,} with a maximum; no violations.")

    # The maximum definition ranges over every candidate, not just actual bearers.
    # Without cause actuality an inactive c can cause the actual maximum,
    # and the actual-pair asymmetry hypothesis says nothing about that edge.
    A, M, C = {0, 1}, {(0, 1)}, {(0, 1), (2, 0)}
    maxs = maxima(A, M)
    assert maxs == {0} and genus(A, C, maxs) and maximal_target_asym(A, C, maxs)
    assert not causal_actuality(A, C) and not no_incoming(C, maxs)
    print("Omission: inactive cause of a maximum survives without cause actuality.")

    # Actual root is a universal source and an assumed maximum, yet ties another.
    # This is an equal-grade preorder with a genuinely empty strict part.
    A, M, C = {0, 1}, set(), {(0, 1)}
    maxs = maxima(A, M)
    assert universal(A, C, 0) and 0 in maxs and len(maxs) == 2
    assert causal_actuality(A, C) and maximal_target_asym(A, C, maxs)
    assert not genus(A, C, maxs)
    print("Omission: a single universal maximal witness + causal asymmetry does not exclude a tied second maximum.")

    # Causal direction, actual source and actual receiver, represented identity,
    # received iff limited, and a genuine degree-induced strict comparison.
    # The receiving principle is distinct from the received act (no self potency).
    A, C, identity, received, limited = {0, 1}, {(0, 1)}, {0}, {1}, {1}
    essence = {0: 'a', 1: 'b'}
    esse = {0: 'a', 1: 'c'}
    receiver = {1: 'b'}
    potency = {('b','c')}
    assert identity == {x for x in A if essence[x] == esse[x]}
    assert universal(A,C,0) and not any(x == 0 for c,x in C)
    assert all(x in received for c,x in C) and received == limited
    assert all(receiver[x] == essence[x] and (receiver[x],esse[x]) in potency for x in received)
    assert all(p != q for p,q in potency)
    for name, degree in [('equal', {0:1,1:1}), ('inverted', {0:1,1:2}), ('ordered', {0:2,1:1})]:
        M = {(c,x) for c,x in product(A,repeat=2) if degree[c] > degree[x]}
        less = all(degree[x] < degree[c] for x in limited for c in A-limited)
        ascent = all((c,x) in M for c,x in C if c in identity)
        assert less == ascent == (name == 'ordered')
        print(f"Degree calibration ({name}): receipt/identity retained, comparative bridge={less}, identity ascent={ascent}.")

    # Actual identity ascent only covers actual targets. A phantom superior
    # defeats IsMaximumIn unless the MoreIn -> InAct bridge is used.
    A, C, M = {0,1}, {(0,1)}, {(0,1),(2,0)}
    assert universal(A,C,0) and (0,1) in M
    assert all((x,c) not in M for c,x in M)  # asymmetric MoreIn
    assert 0 not in maxima(A,M)
    assert not all(c in A for c,x in M)
    print("Scope control: actual-target ascent + order asymmetry does not ensure maximality against inactive candidates.")

if __name__ == '__main__':
    run()
