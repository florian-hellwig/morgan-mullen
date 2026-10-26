"""
thresholds.py -- check of Prop 8.3: for each row, with the listed k,
   F_k(N) = N[(1/2 - 1/k) log2 q - lambda] - log2 C_k - c(W) g_q(log_q N) - 1 >= 0
and a_k - c(W)(pi^2/6 + q/(q-1))/(N ln q) > 0, where a_k = (1/2 - 1/k) log2 q - lambda.
As in the paper (from ln(x/N) <= x/N - 1): F_k(x) >= F_k(N) + (x - N)[a_k - c(W)(pi^2/6 + q/(q-1))/(N ln q)],
so F_k(n) >= 0 for all n >= N.  For q >= 32 the values at q = 32 are used (log2 q >= 5, q/(q-1) <= 32/31, ...).
Computed with mpmath at 50 digits; W, lambda rounded up, c(W) is increasing in W.
Also finds the least N (for the same k) at which both hold.
"""
from functools import lru_cache
import mpmath as mp
import sympy

mp.mp.dps = 50


@lru_cache(maxsize=None)
def C(k):
    v = mp.mpf(1)
    for l in sympy.primerange(2, 2 ** k):
        v *= 2 * mp.power(l, mp.mpf(-1) / k)
    return v


def cW(W):
    W = mp.mpf(W)
    return mp.log(1 / (1 - W), 2) / W


def g(q, x):
    q = mp.mpf(q)
    return mp.pi ** 2 / 6 * x - 1 + (1 + mp.log(x + 1)) * q / (q - 1) + q / (q - 1) ** 2


def F(q, n, k, lam, W):
    ak = (mp.mpf(1) / 2 - mp.mpf(1) / k) * mp.log(q, 2) - mp.mpf(lam)
    return n * ak - mp.log(C(k), 2) - cW(W) * g(q, mp.log(n) / mp.log(q)) - 1, ak


def ok(q, n, k, lam, W):
    val, ak = F(q, n, k, lam, W)
    der = ak - cW(W) * (mp.pi ** 2 / 6 + mp.mpf(q) / (q - 1)) / (n * mp.log(q))
    return val >= 0 and der > 0 and ak > 0


ROWS = [  # q, range of n, W, k, lambda, threshold N of Prop 8.3
    (2, "all n (n>=3780)", "0.75", 13, "0.41", 16674),
    (3, "3|n", "0.444444444444444444445", 11, "0.5983", 1575),
    (3, "3!|n, n>=131200", "0.444444444444444444445", 12, "0.62", 2769),
    (4, "all n (n>=12)", "0.2946", 10, "0.75", 1010),
    (5, "all n", "0.3392", 16, "1", 43618),
    (7, "all n", "0.1683", 9, "1", 336),
]
# W(q) rounded up as printed in Theorem 7.8 (weights.py prints the unrounded values)
WQ = {8: "0.0469", 9: "0.1006", 11: "0.0670", 13: "0.0478", 16: "0.0118", 17: "0.0279", 19: "0.0223",
      23: "0.0152", 25: "0.0129", 27: "0.0110", 29: "0.0096", 31: "0.0084", 32: "0.0118"}

# thresholds N(q) of Prop 8.3 for q >= 8 (lambda = 1)
THRESHOLD = {8: 171, 9: 111, 11: 65, 13: 45, 16: 32, 17: 29, 19: 25, 23: 19, 25: 18, 27: 16, 29: 15, 31: 14, 32: 14}

if __name__ == '__main__':
    for q, lab, W, k, lam, N in ROWS:
        good = ok(q, N, k, lam, W)
        # least N with the same k
        lo, hi = 2, N            # bisection for the least n with ok (ok is monotone once a_k > 0)
        assert ok(q, hi, k, lam, W)
        while lo < hi:
            mid = (lo + hi) // 2
            if ok(q, mid, k, lam, W):
                hi = mid
            else:
                lo = mid + 1
        n0 = lo
        print(f"q={q:2d} {lab:22s} k={k:2d} lambda={lam:7s} W={float(W):.5f}: N={N:6d} valid: {good};"
              f" least N for this k: {n0}")
        assert good and n0 == N
    for q, W in WQ.items():
        best = None
        for k in range(4, 12):
            n = 2
            while n < 400 and not ok(q, n, k, "1", W):
                n += 1
            if n < 400 and (best is None or n < best[0]):
                best = (n, k)
        print(f"q={q:2d}{' (and all q>=32)' if q == 32 else '':15s} W={float(W):.5f} lambda=1: threshold N={best[0]} (k={best[1]})")
        assert best[0] == THRESHOLD[q]
    print("PASSED: all thresholds of Prop 8.3 confirmed")
