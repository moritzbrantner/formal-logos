"""Local research controls, not a Lean certificate or metaphysical model.
Run: python3 esse_ascent_prd_controls.py
Three carriers, finite powersets; all checks deterministic, no dependencies.
"""
from itertools import product


def subsets(items):
    items = tuple(items)
    return [frozenset(item for i, item in enumerate(items) if mask & (1 << i))
            for mask in range(1 << len(items))]


def anchor_audit():
    # Exact abstract shape of fixed-esse genus and ActualEsseCause, with
    # distinct causal edges. MoreIn includes inactive candidates and diagonals.
    B = range(3)
    As, Ms, Cs = subsets(B), subsets(product(B, B)), subsets((a,b) for a,b in product(B,B) if a!=b)
    checked = g_models = witnessed = reciprocal = 0
    for A, M, C in product(As, Ms, Cs):
        checked += 1
        maxima = {m for m in A if not any((y,m) in M for y in B)}
        G = all((m,x) in C for m in maxima for x in A if x != m)
        if not G:
            continue
        for n in A:
            if any((c,n) in C for c in A if c != n):
                continue
            g_models += 1
            assert maxima <= {n}
            if maxima:
                witnessed += 1
                assert maxima == {n}
                assert all((n,x) in C for x in A if x != n)
                if any((b,a) in C for a,b in C):
                    reciprocal += 1
                H = all(x not in A or c in A for c,x in C)
                if H:
                    assert not any(x in maxima for c,x in C)
    print(f'Anchor + G: {checked:,} assignments; {g_models:,} (assignment,anchor) instances; {witnessed:,} with a maximum, including {reciprocal:,} with reciprocal edges; all pass.')
    # Anchor may not be maximum in the absence of any maximum: even a finite
    # strict/asymmetric relation can have a cycle on 3 nodes.
    A = {0,1,2}; C = {(0,1),(0,2)}; M = {(0,1),(1,2),(2,0)}
    assert all((c,0) not in C for c in A) and not any(all((y,m) not in M for y in A) for m in A)
    # A single universal source with tied actual effect is not G.
    A={0,1}; C={(0,1)}; M=set()
    assert (0,1) in C and (1,0) not in C and all((y,m) not in M for y in A for m in A)
    assert not all((m,x) in C for m in A for x in A if x!=m)
    # Actual no-incoming doesn't exclude a nonactual cause without H.
    A={0,1}; C={(0,1),(2,0)}; M={(0,1)}
    assert all((c,0) not in C for c in A) and (2,0) in C
    print('Anchor omissions: maximum existence, all-maxima reach, and actuality of incoming causes remain separate.')


def content_audit():
    # Has is a relation, Pure a fixed classification per profile. No numerical
    # degrees, source naming, or intrinsic/eminent adapter inferred.
    B=range(3); D=range(3); sets=subsets(D)
    profiles=full_pure=real_thisness=pure_indisc=0
    ties_impure=0
    for H0,H1,H2,P in product(sets, repeat=4):
        profiles += 1; H=(H0,H1,H2)
        PI = all(a==b or H[a]!=H[b] or not H[a] <= P for a,b in product(B,B))
        for n in B:
            if H[n]!=P:  # completeness + purity at n
                continue
            full_pure += 1
            unique = {d for d in H[n] if all(d not in H[x] for x in B if x!=n)}
            if unique:
                real_thisness += 1
                assert all((H[x]&P) < P for x in B if x!=n)
            if PI:
                pure_indisc += 1
                for x in B:
                    if x == n: continue
                    missing=P-H[x]; nonpure=H[x]-P
                    assert missing or nonpure
                    if not missing:
                        ties_impure += 1
                        assert nonpure
    print(f'Pure content: {profiles:,} profiles; {full_pure:,} full-and-pure root choices; {real_thisness:,} with real-thisness, {pure_indisc:,} satisfying pure indiscernibility. All pass; {ties_impure:,} tied recipient comparisons with nonpure content under indiscernibility.')
    # Different recipients can miss different pure determinations: no shared
    # missing witness is necessary for strict pairwise containment.
    P={0,1}; H=({0,1},{0},{1})
    assert all(H[x] < P for x in [1,2])
    assert not any(all(d not in H[x] for x in [1,2]) for d in P)
    # Indiscernibility doesn't prohibit pure-content ties with impure recipients.
    P={0}; H=({0},{0,1},{0,2})
    assert all(a==b or H[a]!=H[b] or not H[a]<=P for a,b in product(B,B))
    assert all(H[x]&P==P and H[x]-P for x in [1,2])
    print('Controls: pairwise missing witnesses need not form a common thisness; pure-content ties survive with distinct nonpure content.')


def saturation_audit():
    # Independently described finite positive actual contents and admissible
    # capacities; this is a structural surrogate, not a theory of esse.
    D=range(3); S=subsets(D); checked=contraction=tied=saturated=0
    for cap_s, cap_x, act_s, act_x in product(S, repeat=4):
        checked+=1
        if not (cap_x < cap_s and act_s <= cap_s and act_x <= cap_x): continue
        contraction+=1
        if act_s==act_x: tied+=1
        if act_s==cap_s:
            saturated+=1
            assert act_x < act_s
    assert tied and saturated
    print(f'Capacity/actuality: {checked:,} profiles; {contraction:,} contracted-capacity profiles, {tied:,} tied actual contents, {saturated:,} saturated sources all strictly contain the recipient.')
    # Nonempty tie: different constitutive restrictions, identical actual content.
    cap_s={0,1}; cap_x={0}; act_s=act_x={0}
    assert cap_x<cap_s and act_s==act_x
    # Source saturation, genuine contraction -> actual missing witness.
    act_s=cap_s
    assert act_x<act_s

if __name__ == '__main__':
    anchor_audit(); content_audit(); saturation_audit()
