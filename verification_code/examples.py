"""
examples.py -- reproduces the numbers of the worked examples, which illustrate the method but are not part of
the proof (and are not formalised in Lean):
  * Section 10, (q, n) = (2, 4599): orders, essential types, M, the 63 components (table), the hand-checked
    weight 6663/2^18, the lower bound for delta from Theorem 3.2, L, the bounds of Lemma 5.1 for omega(2^4599 - 1),
    the margin of Theorem 4.2(b), S and the margin of criterion (*) with W(2) = 3/4, and the resulting bounds for the
    relative error in Corollary 8.9(a);
  * Section 12, (q, n) = (2, 21): the four components, their dimensions, weights and numbers of passing vectors,
    and CN_2(21) = 1 * 3 * 294^2 = 259308 by Theorem 3.2 (cf. Hachenberger's book, Example 14.6);
  * Section 12, (q, n) = (3, 10): the essential conditions at level 2 whose target has order 5, with the orders of
    their fibre elements.
Run: python3 examples.py  (about 5 seconds; uses galois for the (2,21) passing counts)
"""
import time
from collections import Counter
from fractions import Fraction
from math import log2, gcd
from mmlib import divisors, ordmod, essential_types, M_S_g, omega_bound, cW
from components import enumerate_components


def example_2_4599():
    q, n = 2, 4599
    print(f"=== Section 10: (q,n) = ({q},{n}) = 3^2*7*73")
    print("  e and ord_e(2):", [(e, ordmod(2, e)) for e in divisors(n)])
    types = essential_types(q, n)                        # (d, e, nu, o)
    print("  essential types (d,e)^nu:", ", ".join(f"({d},{e})^{nu}" for (d, e, nu, o) in sorted(types, key=lambda t: (t[1], t[0]))))
    M, S, g = M_S_g(q, n)
    comps, conds, n1, p, a = enumerate_components(q, n)
    norb = len({min((i * pow(q, j, n1)) % n1 for j in range(ordmod(q, n1 // gcd(n1, i)) if i else 1)) for i in range(n1)})
    assert M == len(conds) == 1145 and norb == 293
    print(f"  M = {M} essential conditions on {norb} Frobenius orbits; {len(comps)} components")
    rows = Counter()
    for C in comps:
        tc = Counter((d, e) for (d, k, e, o, fib) in C['conds'])
        key = (len(C['conds']), C['dim'], C['weight'], tuple(sorted(tc.items(), key=lambda t: (t[0][1], t[0][0]))))
        rows[key] += 1
    print("  number | conditions | dim | weight | types in one component")
    for (nc, dim, w, tc), cnt in sorted(rows.items(), key=lambda t: (t[0][1], t[0][0])):
        ts = ", ".join(f"({d},{e})" + (f"^{m}" if m > 1 else "") for (d, e), m in tc)
        print(f"  {cnt:6d} | {nc:10d} | {dim:3d} | {str(w):12s} = {float(w):.4f} | {ts}")
    assert len(comps) == 63 and Fraction(6663, 2 ** 18) in {w for (nc, dim, w, tc) in rows}
    assert Fraction(1 + 3 + 9, 2 ** 9) + Fraction(1 + 3 + 3, 2 ** 18) == Fraction(6663, 2 ** 18)
    logdelta = sum(log2(1 - float(C['weight'])) for C in comps)
    logL = sum(log2(2 * (1 - 2.0 ** (-o))) for (d, k, e, o, fib) in conds)
    om_exact, om_crude = omega_bound(q, n, True), omega_bound(q, n, False)
    margin13 = n + log2(1 - 2.0 ** (-n)) + logdelta - om_exact - n / 2 - logL
    print(f"  Theorem 3.2: log2 delta >= {logdelta:.3f};  log2 L = {logL:.2f}")
    print(f"  Lemma 5.1: omega(2^4599 - 1) <= {om_exact} (exact t_k), <= {om_crude} (second bound)")
    print(f"  Theorem 4.2(b) inequality: margin {margin13:.1f} bits (with omega <= {om_exact})")
    star = n / 2 + log2(1 - 2.0 ** (-n)) - (om_exact + M + cW(0.75) * float(S))
    print(f"  criterion (*): M = {M}, S = {float(S):.4f} (M_1 = {g}; total weight S + M_1/2 = {float(S) + g / 2:.3f}),"
          f" W(2) = 3/4: margin {star:.1f} bits with omega <= {om_exact}, "
          f"{star + om_exact - om_crude:.1f} bits with omega <= {om_crude}")
    assert om_exact == 253 and M == 1145 and abs(float(S) - 2.908) < 0.001
    # Corollary 8.9(a): relative error |PCN/(theta CN) - 1| <= 2^omega L / (q^(n/2) delta) (first inequality, with
    # the bounds for delta, L and omega above) and <= 2^(omega + M + c(W) S) / q^(n/2) (second inequality)
    rel1 = om_exact + logL - n / 2 - logdelta
    rel2 = om_exact + M + cW(0.75) * float(S) - n / 2
    print(f"  Corollary 8.9(a): relative error |PCN/(theta CN) - 1| <= 2^{rel1:.2f} (first inequality), "
          f"<= 2^{rel2:.2f} (second inequality)")
    assert rel1 < -900 and rel2 < -893


def example_2_21():
    import itertools
    import numpy as np
    import galois
    q, n = 2, 21
    print("=== Section 12: (q,n) = (2,21)")
    comps, conds, n1, p, a = enumerate_components(q, n)
    GF = galois.GF(2 ** 42)
    g = GF.primitive_element
    z = g ** ((2 ** 42 - 1) // 21)                       # primitive 21st root of unity
    gE = g ** ((2 ** 42 - 1) // (2 ** 21 - 1))           # generator of E^x, E = F_{2^21}
    basis = [gE ** i for i in range(21)]                 # an F_2-basis of E (gE has degree 21)

    def F(w, j):                                         # resolvent F_eta(w), eta = z^j
        s, x, eta_inv = GF(0), w, z ** (-j)
        for t in range(21):
            s += eta_inv ** t * x
            x = x ** 2
        return s
    Fb = [[F(b, j) for j in range(21)] for b in basis]   # F is F_2-linear in w

    def bits(x):
        v = int(x)
        return [(v >> i) & 1 for i in range(42)]
    total = 1
    for C in sorted(comps, key=lambda C: C['dim']):
        keep = set(C['V'])
        rows = []
        for j in range(21):
            if j not in keep:                            # coordinates outside the component vanish
                cols = [bits(Fb[i][j]) for i in range(21)]
                rows += [[cols[i][r] for i in range(21)] for r in range(42)]
        Nsp = galois.GF(2)(np.array(rows, dtype=int)).null_space()
        assert Nsp.shape[0] == C['dim']
        passing = 0
        for coeffs in itertools.product([0, 1], repeat=C['dim']):
            c = galois.GF(2)(np.array(coeffs, dtype=int)) @ Nsp
            Fw = {j: sum((Fb[i][j] for i in range(21) if int(c[i])), GF(0)) for j in keep}
            passing += all(sum((Fw[i] for i in fib), GF(0)) != 0 for (d, k, e, o, fib) in C['conds'])
        total *= passing
        tc = Counter((d, e) for (d, k, e, o, fib) in C['conds'])
        print(f"  component: dim {C['dim']}, conditions {dict(tc)}, weight {C['weight']} = {float(C['weight']):.4f},"
              f" passed by {passing} of {2 ** C['dim']} vectors")
    print(f"  CN_2(21) = product of the passing counts = {total}")
    assert total == 259308 == 1 * 3 * 294 ** 2


def example_3_10():
    q, n = 3, 10
    print("=== Section 12: (q,n) = (3,10)")
    comps, conds, n1, p, a = enumerate_components(q, n)
    for (d, k, e, o, fib) in conds:
        if d == 2 and e == 5:
            ords = sorted(n1 // gcd(n1, i) for i in fib)
            print(f"  level 2, target of order {e} (k = {k}), codimension {o}: fibre element orders {ords}")


if __name__ == '__main__':
    t0 = time.time()
    example_2_4599()
    example_3_10()
    example_2_21()
    print(f"examples reproduced [{time.time() - t0:.0f}s]")
