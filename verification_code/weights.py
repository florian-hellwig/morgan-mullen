"""
weights.py -- Theorem 7.8 (weights): an upper bound W(q) for the weight of every component that contains
no codimension-1 condition, following the proof of Theorem 7.8 step by step.
All arithmetic is exact (Fractions and integers); the only floating-point steps are the check e^1.03883 < 2.83
and the signs of two derivatives in lemma27_q2 (Lemma 7.5; the name keeps an earlier number),
all with wide margins.

Evaluation of W_cl and W_cr (first paragraph of the proof):
    Sigma(O, D) = sum_{o | O, o >= o0} q^-o I_D(o),   I_D(o) = sum_{d | o, d' | D} d gcd(q^o - 1, D/d'),
    Sigma(O, D) <= sum_{o | O, o0 <= o <= o0 + 40} q^-o I_D(o) + 3 m^2 D q^-m,   m = o0 + 41
(I_D(o) <= sigma_1(o) D <= o^2 D and sum_{o >= m} o^2 q^-o <= 3 m^2 q^-m for m >= 7; the tail term is
dropped if O < m).  W_cl uses (O, D) = (O_inf, D_inf) of the closure (B), W_cr uses (Lambda, Lambda_p').

  (i)   (q, o0) in {(2,3), (2,6), (3,2), (3,4)}: W_cl > W(q); exact computation (struct_and_exactmax.py);
        here only N** = 42, 378, 16, 320 and W_cl > W(q) are checked.
  (ii)  q = 2:  W_cl(2, o0) <= 3/4 for 2 <= o0 <= 4095, o0 != 3, 6, and <= 0.032 for o0 >= 9;
        o0 >= 4096: Lemma 7.5 gives W_cl(2, o0) <= 3 o0^2 D_inf 2^-o0 <= 3/128.
  (iii) q = 3:  W_cl(3, o0) <= 4/9 for 3 <= o0 <= 374, o0 != 4, and <= 0.051 for o0 >= 7; o0 >= 375: (v).
  (iv)  4 <= q <= 31: W_cr(q, o0) <= W(q) for 2 <= o0 < o1(q); o0 >= o1(q): (v).
  (v)   W_cr(q, o0) <= T_q(o0) = 3 o0^3 (2.83/q)^o0 (Rosser-Schoenfeld); T_q(o1) <= W and
        (1 + 1/o1)^3 2.83 <= q, for (q, o1(q), W(q)), (3, 375, 0.051) and (32, 7, 0.0118).
  (vi)  q >= 32, 2 <= o0 <= 6: sum_{o | Lambda+, o >= o0} sigma_1(o) Lambda+ 32^-o <= 0.0118,
        Lambda+ = o0 lcm(1..o0).
"""
import math
from math import gcd, lcm
from fractions import Fraction
from mmlib import divisors, char_of
from closure import closure, pfree

W = {2: Fraction(3, 4), 3: Fraction(4, 9), 4: Fraction('0.2946'), 5: Fraction('0.3392'), 7: Fraction('0.1683'),
     8: Fraction('0.0469'), 9: Fraction('0.1006'), 11: Fraction('0.0670'), 13: Fraction('0.0478'),
     16: Fraction('0.0118'), 17: Fraction('0.0279'), 19: Fraction('0.0223'), 23: Fraction('0.0152'),
     25: Fraction('0.0129'), 27: Fraction('0.0110'), 29: Fraction('0.0096'), 31: Fraction('0.0084')}
O1 = {4: 39, 5: 20, 7: 12, 8: 11, 9: 9, 11: 8}          # o1(q); o1(q) = 7 for q >= 13
W_BIG = Fraction('0.0118')                               # W(q) for q >= 32
T2, T3 = Fraction(32, 1000), Fraction(51, 1000)          # targets for q = 2, o0 >= 9 and q = 3, o0 >= 7


def sigma1(o):
    return sum(divisors(o))


def I_D(q, p, o, D):
    """I_D(o) = sum_{d | o, d' | D} d gcd(q^o - 1, D/d')"""
    s = 0
    for d in divisors(o):
        dp = pfree(d, p)
        if D % dp == 0:
            m = D // dp
            s += d * (gcd(pow(q, o, m) - 1, m) if m > 1 else 1)
    return s


def Sigma_bound(q, o0, O, D, m):
    """sum_{o | O, o0 <= o < m} q^-o I_D(o) + (0 if O < m else 3 m^2 D q^-m), exact"""
    assert m >= 7 and o0 <= m
    p, _ = char_of(q)
    tot = Fraction(0)
    for o in range(o0, m):
        if O % o == 0:
            tot += Fraction(I_D(q, p, o, D), q ** o)
    if O >= m:
        tot += Fraction(3 * m * m * D, q ** m)
    return tot


def W_cl_bound(q, o0):
    c = closure(q, o0)
    return Sigma_bound(q, o0, c['Oinf'], c['Dinf'], o0 + 41)


def W_cl_exact(q, o0):
    """W_cl(q, o0) as an exact finite sum over the divisors o >= o0 of O_inf (for small o0)."""
    p, _ = char_of(q)
    c = closure(q, o0)
    return sum((Fraction(I_D(q, p, o, c['Dinf']), q ** o) for o in divisors(c['Oinf']) if o >= o0), Fraction(0))


def W_cr_bound(q, o0):
    p, _ = char_of(q)
    Lam = pfree(o0, p) * lcm(*range(1, o0 + 1))
    return Sigma_bound(q, o0, Lam, pfree(Lam, p), o0 + 41)


def rs_ok(q, o1, Wt):
    """(v): T_q(o1) = 3 o1^3 (2.83/q)^o1 <= W and (1 + 1/o1)^3 2.83 <= q, in exact arithmetic"""
    return (o1 >= 7 and 3 * o1 ** 3 * 283 ** o1 <= Wt * (100 * q) ** o1
            and (o1 + 1) ** 3 * 283 <= o1 ** 3 * 100 * q)


def uniform_bound(o0, m):
    """(vi): sum_{o | L+, o0 <= o < m} sigma_1(o) L+ 32^-o + tail, L+ = o0 lcm(1..o0)"""
    Lp = o0 * lcm(*range(1, o0 + 1))
    tot = sum((Fraction(sigma1(o) * Lp, 32 ** o) for o in range(o0, m) if Lp % o == 0), Fraction(0))
    if Lp >= m:
        tot += Fraction(3 * m * m * Lp, 32 ** m)
    return tot


def lemma27_q2(x0=12):
    """(ii), o0 >= 4096: with L = log2 o0 >= 12, log2(128 o0^2 D_inf) <= 7 + 2L + 3L(1 + 6L) <= 2^L = o0.
    The difference 2^L - 18L^2 - 5L - 7 is positive at L = 12 and increasing for L >= 12."""
    f = lambda L: 2 ** L - 18 * L * L - 5 * L - 7
    df_pos = 2 ** x0 * math.log(2) - 36 * x0 - 5 > 0 and math.log(2) ** 2 * 2 ** x0 > 36   # f' > 0 and f'' > 0
    return f(x0) > 0 and df_pos


if __name__ == '__main__':
    assert math.exp(1.03883) < 2.8260 < 2.83
    worst = {}

    # (i) the four exceptional pairs
    need = {}
    for q, o0, Nss in ((2, 3, 42), (2, 6, 378), (3, 2, 16), (3, 4, 320)):
        c = closure(q, o0)
        assert c['Nss'] == Nss, (q, o0, c['Nss'])
        wcl = W_cl_exact(q, o0)
        assert wcl > W[q]
        need[(q, o0)] = wcl
    print("(i)   W_cl > W(q) exactly for", {k: f"{v} = {float(v):.4f}" for k, v in need.items()},
          "; N** = 42, 378, 16, 320")
    others = [(q, o0) for q, rng in ((2, range(2, 9)), (3, range(2, 7))) for o0 in rng
              if (q, o0) not in need and W_cl_exact(q, o0) > W[q]]
    assert others == []
    print("      for all other q = 2, o0 <= 8 and q = 3, o0 <= 6: W_cl(q, o0) <= W(q);",
          "W_cl(2,2) =", W_cl_exact(2, 2), " W_cl(2,4) =", W_cl_exact(2, 4), " W_cl(3,3) =", W_cl_exact(3, 3))

    # (ii) q = 2
    big, best9 = Fraction(0), (Fraction(0), None)
    for o0 in range(2, 4096):
        if o0 in (3, 6):
            continue
        b = W_cl_bound(2, o0)
        assert b <= (W[2] if o0 <= 8 else T2), (o0, float(b))
        big = max(big, b)
        if o0 >= 9 and b > best9[0]:
            best9 = (b, o0)
    assert lemma27_q2()
    print(f"(ii)  q=2: W_cl(2,o0) <= 3/4 for 2 <= o0 <= 4095 (o0 != 3, 6), largest bound {float(big):.5f}; "
          f"for o0 >= 9 at most {float(best9[0]):.5f} (o0 = {best9[1]}) <= 0.032; o0 >= 4096: <= 3/128 by Lemma 7.5")
    worst[2] = max(big, Fraction(3, 128))

    # (iii) q = 3
    big, best7 = Fraction(0), (Fraction(0), None)
    for o0 in range(3, 375):
        if o0 == 4:
            continue
        b = W_cl_bound(3, o0)
        assert b <= (W[3] if o0 <= 6 else T3), (o0, float(b))
        big = max(big, b)
        if o0 >= 7 and b > best7[0]:
            best7 = (b, o0)
    assert rs_ok(3, 375, T3)
    print(f"(iii) q=3: W_cl(3,o0) <= 4/9 for 3 <= o0 <= 374 (o0 != 4), largest bound {float(big):.5f}; "
          f"for o0 >= 7 at most {float(best7[0]):.5f} (o0 = {best7[1]}) <= 0.051; o0 >= 375: (v) with W = 0.051")
    worst[3] = max(big, T3)

    # (iv) 4 <= q <= 31 and (v)
    for q in [4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31]:
        o1 = O1.get(q, 7)
        bs = [(W_cr_bound(q, o0), o0) for o0 in range(2, o1)]
        b, arg = max(bs)
        assert b <= W[q], (q, float(b))
        assert rs_ok(q, o1, W[q]), q
        assert o1 == 7 or not rs_ok(q, o1 - 1, W[q])          # o1(q) is the least start >= 7
        print(f"(iv)  q={q}: W_cr(q,o0) <= {float(b):.5f} for 2 <= o0 < {o1} (largest at o0 = {arg}); "
              f"(v) from o1 = {o1}; W(q) = {float(W[q])}")
        assert arg <= 3
        worst[q] = b

    # (vi) q >= 32 and (v) at q = 32
    bs = [(uniform_bound(o0, o0 + 41), o0) for o0 in range(2, 7)]
    b, arg = max(bs)
    assert b <= W_BIG and rs_ok(32, 7, W_BIG)
    print(f"(vi)  q>=32: uniform bound <= {float(b):.6f} for 2 <= o0 <= 6 (largest at o0 = {arg}); (v) at q = 32 from 7")

    print("largest bounds:", {q: round(float(w), 5) for q, w in worst.items()})
    print("PASSED: every component without codimension-1 conditions has weight at most W(q) as stated in Thm 7.8 "
          "(given the exact computation (i) in struct_and_exactmax.py)")
