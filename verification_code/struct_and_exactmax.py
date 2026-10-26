"""
struct_and_exactmax.py
 (1) Step (i) of the proof of Theorem 7.8: for (q, o0) = (2,3), (2,6), (3,2), (3,4) we have N** = 42, 378, 16, 320,
     and for every n0 dividing N** every component without a codimension-1 condition has weight at most
     W(q) (3/4 for q = 2, 4/9 for q = 3).  Proposition 7.7 then bounds all components with these minimal
     codimensions, for all n.
     For comparison (not needed for the proof) also the exact maximal weights for q=2 (o0=2..8) and
     q=3 (o0=2..6): max over all divisors n0 of N**(q,o0) of the weights of components with minimal codim o0.
 (2) Brute-force test of Theorem 7.2 on many n: (a) and (b) with K from the closure (B), D_C | D_inf,
     all codimensions divide O_inf, and (c) with D = D_C.
"""
import random, time
from math import gcd, lcm
from fractions import Fraction
from components import enumerate_components
from closure import closure, pfree
from mmlib import divisors, split_p


def exact_max(q, o0):
    Nss = closure(q, o0)['Nss']
    best, arg = Fraction(0), None
    for n0 in divisors(Nss):
        comps, *_ = enumerate_components(q, n0)
        for C in comps:
            if C['o0'] == o0 and C['weight'] > best:
                best, arg = C['weight'], n0
    return best, arg, Nss


def Ncount_bound(q, o, D, p):
    s = 0
    for d in divisors(o):
        dp = pfree(d, p)
        if D % dp == 0:
            s += d * gcd(q ** o - 1, D // dp)
    return s


def check_struct(q, n):
    """returns number of non-singleton-type components checked; raises on violation"""
    comps, conds, n1, p, a = enumerate_components(q, n)
    cnt = 0
    for C in comps:
        if C['o0'] == 1:
            assert len(C['conds']) == 1, "codim-1 condition not a singleton"
            continue
        cnt += 1
        o0 = C['o0']
        cl = closure(q, o0)
        K, Oinf, Dinf = cl['K'], cl['Oinf'], cl['Dinf']
        # (a): all eta in V have order dividing K
        for i in C['V']:
            assert K % (n1 // gcd(n1, i)) == 0, ("Thm 7.2 (a)", q, n)
        DC = 1
        byo = {}
        for (d, k, e, o, fib) in C['conds']:
            c, d1 = split_p(d, p)
            # (b): ord xi | K, d | ord_K(q) (tested as d | O_inf, which equals ord_K(q) for this K), d' e | K
            assert K % e == 0 and Oinf % d == 0 and K % (d1 * e) == 0, ("Thm 7.2 (b)", q, n)
            assert Oinf % o == 0, ("codim divides O_inf", q, n)
            DC = lcm(DC, d1)
            byo[o] = byo.get(o, 0) + 1
        assert Dinf % DC == 0, ("D_C | D_inf", q, n)
        # (c) with D = D_C
        for o, N in byo.items():
            assert N <= Ncount_bound(q, o, DC, p), ("Thm 7.2 (c)", q, n, o)
    return cnt


if __name__ == '__main__':
    t0 = time.time()
    print("(1) step (i) of Thm 7.8: all components for all n0 | N**, (q, o0) = (2,3), (2,6), (3,2), (3,4)")
    for q, o0, Nss_claim in ((2, 3, 42), (2, 6, 378), (3, 2, 16), (3, 4, 320)):
        Nss = closure(q, o0)['Nss']
        assert Nss == Nss_claim
        Wq = Fraction(3, 4) if q == 2 else Fraction(4, 9)
        mx = Fraction(0)
        for n0 in divisors(Nss):
            comps, *_ = enumerate_components(q, n0)
            for C in comps:
                if C['o0'] >= 2:
                    mx = max(mx, C['weight'])
        assert mx <= Wq
        print(f"  q={q} o0={o0}: N**={Nss}; largest weight of a component without codimension-1 conditions, over "
              f"all n0 | N**: {mx} <= W({q}) = {Wq}", flush=True)
    print("    exact maximal weights for comparison (not needed for the proof)")
    PAPER = {(2, 2): Fraction(3, 4), (2, 3): Fraction(35, 64), (2, 4): Fraction(7, 16), (2, 6): Fraction(9, 32),
             (2, 8): Fraction(15, 256), (3, 2): Fraction(4, 9), (3, 3): Fraction(4, 27), (3, 4): Fraction(4, 27),
             (3, 6): Fraction(16, 729)}
    for q, rng in [(2, range(2, 9)), (3, range(2, 7))]:
        for o0 in rng:
            w, arg, Nss = exact_max(q, o0)
            print(f"  q={q} o0={o0}: N**={Nss}, max weight {w} = {float(w):.5f} (attained at n0={arg})", flush=True)
            if (q, o0) in PAPER:
                assert w == PAPER[(q, o0)]
            assert w <= (Fraction(3, 4) if q == 2 else Fraction(4, 9))
    print(f"  [{time.time()-t0:.0f}s]")
    print("(2) Theorem 7.2 (a),(b),(c) by brute force")
    random.seed(1)
    plan = {2: 3000, 3: 1500, 4: 1200, 5: 1000, 7: 800, 8: 600, 9: 600, 11: 400, 13: 400, 16: 300, 25: 300, 27: 300}
    for q, N in plan.items():
        ns = list(range(2, N + 1)) + [random.randint(N, 20 * N) for _ in range(40)]
        tot = sum(check_struct(q, n) for n in ns)
        print(f"  q={q}: n in [2,{N}] + 40 random n <= {20*N}: {tot} components checked, no violation "
              f"[{time.time()-t0:.0f}s]", flush=True)
    print("PASSED: step (i) of Thm 7.8 and the comparison values; Thm 7.2 (a),(b),(c) hold on all tested components")
