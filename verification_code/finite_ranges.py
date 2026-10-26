"""
finite_ranges.py -- the finite ranges of the Main Theorem (Prop 8.4).

For every prime power q < 32 and every n with q < n < N(q) (N(q) = threshold of Prop 8.3, with the
q-specific ranges below), evaluate criterion (*) of Theorem 8.1(b),
      log2(q^n - 1) - (n/2) log2 q  >=  omega + M + c(W) S,      c(W) = log2(1/(1-W))/W,
with the exact values M = sum nu(d,e), S = sum_{ord_e(q) >= 2} nu(d,e) q^-ord_e(q) over the essential types (d,e)
(nu(d,e) = d phi(e)/ord_e(q), Lemma 5.2), omega(q^n - 1) replaced by the bound of Lemma 5.1 (crude t_k first,
exact t_k if needed), and W = W(q) of Theorem 7.8 (rounded up).  Pairs with n <= q are covered by
the theorem of Garefalakis and Kapetanakis; q >= 32 needs nothing here (all n > q >= 32 exceed the threshold 14).
A pair is accepted only if (*) holds with at least 1 bit to spare (a factor 2).  The script checks that
the pairs that are not accepted are exactly the 70 pairs certified in pcn_certificates.txt (the 50 failures
and 20 tight pairs).
The margins are computed in double precision; a margin within 1e-6 of 0 would be recomputed with mpmath
(60 digits).  Every accepted pair has a margin of at least 1.03 bits, far above the rounding error.
For q = 4 the analytic range of Prop 8.3 covers every n >= 1010 (Prop 6.5(a): M <= 3n/4 for all n >= 12),
so the finite range is 4 < n < 1010.
Run time: about a minute.
"""
import time
from math import log2
import mpmath as mp
from mmlib import M_S_g, omega_bound

W = {2: 0.75, 3: 4 / 9, 4: 0.2946, 5: 0.3392, 7: 0.1683, 8: 0.0469, 9: 0.1006, 11: 0.0670, 13: 0.0478,
     16: 0.0118, 17: 0.0279, 19: 0.0223, 23: 0.0152, 25: 0.0129, 27: 0.0110, 29: 0.0096, 31: 0.0084}
# ranges q < n < N(q) not covered by Prop 8.3 (thresholds from Prop 8.3)
RANGES = {2: range(3, 16674), 3: range(4, 131200), 4: range(5, 1010), 5: range(6, 43618),
          7: range(8, 336), 8: range(9, 171), 9: range(10, 111), 11: range(12, 65), 13: range(14, 45),
          16: range(17, 32), 17: range(18, 29), 19: range(20, 25), 23: range(24, 19), 25: range(26, 18),
          27: range(28, 16), 29: range(30, 15), 31: range(32, 14)}


def margin(q, n, exact_omega=False):
    M, S, g = M_S_g(q, n)
    om = omega_bound(q, n, exact_omega)
    Wq = W[q]
    lhs = n * log2(q) / 2 + log2(1.0 - float(q) ** (-n))
    rhs = om + M + log2(1.0 / (1.0 - Wq)) / Wq * float(S)
    m = lhs - rhs
    if abs(m) < 1e-6:                       # high-precision re-evaluation (triggered at the certified pair
                                            # (2,24) with the exact omega: margin log2(1 - 2^-24) = -8.6e-8)
        mp.mp.dps = 60
        lhs = mp.log(mp.mpf(q) ** n - 1, 2) - mp.mpf(n) / 2 * mp.log(q, 2)
        Wm = mp.mpf(Wq)
        rhs = om + M + mp.log(1 / (1 - Wm), 2) / Wm * mp.mpf(S.numerator) / S.denominator
        m = float(lhs - rhs)
    return m


def main():
    t0 = time.time()
    certified = set()
    for line in open('pcn_certificates.txt'):
        if not line.startswith('#') and line.strip():
            q, n = map(int, line.split('|')[0].split())
            certified.add((q, n))
    fails = set()
    for q, rng in RANGES.items():
        ns = list(rng)
        worst, worst203 = None, None
        for n in ns:
            m = margin(q, n)
            if m <= 0:
                m = margin(q, n, exact_omega=True)
            if m < 1:
                fails.add((q, n))                # failure or tight: needs a certificate
                continue
            if worst is None or m < worst[1]:
                worst = (n, round(m, 2))
            if n >= 203 and (worst203 is None or m < worst203[1]):
                worst203 = (n, round(m, 2))
        nf = sorted(n for (qq, n) in fails if qq == q)
        print(f"q={q:2d}: {len(ns):6d} values of n checked; not accepted (margin < 1 bit): n = {nf}; "
              f"smallest margin {worst} (for n >= 203: {worst203})  [{time.time()-t0:.0f}s]", flush=True)
    assert fails == certified, (sorted(fails ^ certified))
    print(f"OK: the pairs with margin < 1 bit are exactly the {len(certified)} certified pairs.")


if __name__ == '__main__':
    main()
