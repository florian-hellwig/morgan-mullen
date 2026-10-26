"""
bounds_for_M.py -- the computer-assisted constants of Prop 6.5 (bounds for M/n, q <= 4):
  f_a(o)  = sum_{d | o, v_p(d) <= a} p^(v_p(d)-a) min(1/d, d/o)
  R_a(k)  = sum_{d | o, v_p(d) <= a, d | ord_{k/gcd(k,d')}(q)} p^(v_p(d)-a) / ord_{k/gcd(k,d')}(q)   (o = ord_k(q))
  R*_a(o) = max{R_a(k) : k | q^o - 1, ord_k(q) = o}
The local maxima R*_a(o) are computed with fractions.  The tables of f_a(o) are computed in integers, as
S_a(o) = o p^a f_a(o) = sum_{d | o, v_p(d) <= a} p^(v_p(d)) min(d, o/d), and every bound f_a(o) <= u/w of
Prop 6.5 is checked exactly as w S_a(o) <= u o p^a.  Floating point is used only for the printed values and
for float duplicates of the kappa checks, which are also done exactly.
"""
import time
from fractions import Fraction
from math import gcd
import numpy as np
import sympy
from mmlib import divisors, ordmod, split_p


def f_a(o, a, p):
    s = Fraction(0)
    for d in divisors(o):
        c, _ = split_p(d, p)
        if c <= a:
            s += Fraction(p ** c, p ** a) * min(Fraction(1, d), Fraction(d, o))
    return s


def Rstar(q, o, a):
    p = sympy.factorint(q)
    p = list(p)[0]
    best = Fraction(0)
    for k in divisors(q ** o - 1):
        if ordmod(q, k) != o:
            continue
        s = Fraction(0)
        for d in divisors(o):
            c, d1 = split_p(d, p)
            if c > a:
                continue
            oe = ordmod(q, k // gcd(k, d1))
            if oe % d == 0:
                s += Fraction(p ** c, p ** a * oe)
        best = max(best, s)
    return best


def S_table(p, omax, amax):
    """integer table S[a][o] = o p^a f_a(o) = sum_{d | o, v_p(d) <= a} p^(v_p(d)) min(d, o/d)
    for 1 <= o <= omax, 0 <= a <= amax (numpy sieve over divisors)"""
    assert p ** amax * omax < 2 ** 52          # S[a][o] <= p^a o (Lemma 6.2): no overflow, exact as float
    S = np.zeros((amax + 1, omax + 1), dtype=np.int64)
    for d in range(1, omax + 1):
        c = 0
        x = d
        while x % p == 0:
            x //= p
            c += 1
        if c > amax:
            continue
        os_ = np.arange(d, omax + 1, d, dtype=np.int64)
        v = np.minimum(d, os_ // d) * p ** c
        for a in range(c, amax + 1):
            S[a, d::d] += v
    return S


def bounded(S, p, a, lo, hi, bound, excl=()):
    """exact check of f_a(o) <= bound for all lo <= o <= hi, o not in excl: bound.den S_a(o) <= bound.num o p^a"""
    u, w = bound.numerator, bound.denominator
    assert int(S[a].max()) * w < 2 ** 63 and u * hi * p ** a < 2 ** 63      # no int64 overflow
    o = np.arange(lo, hi + 1, dtype=np.int64)
    ok = S[a, lo:hi + 1] * w <= u * o * p ** a
    for x in excl:
        ok[x - lo] = True
    return bool(ok.all())


def sup(S, p, a, lo, hi, excl=()):
    """(largest f_a(o) for lo <= o <= hi, o not in excl, rounded to 6 digits; the smallest o attaining it)"""
    v, minus_o = max((S[a][o] / (o * p ** a), -o) for o in range(lo, hi + 1) if o not in excl)
    return round(float(v), 6), -minus_o


def tau_const_pow(s):
    """kappa_s^s exactly: prod over primes l < 2^s of max_alpha (alpha+1)^s / l^alpha"""
    v = Fraction(1)
    for l in sympy.primerange(2, 2 ** s):
        v *= max(Fraction((al + 1) ** s, l ** al) for al in range(0, 60))
    return v


def tau_const(s):
    """kappa_s = max_m tau(m) m^(-1/s) = prod over primes l < 2^s of max_alpha (alpha+1) l^(-alpha/s)"""
    v = 1.0
    for l in sympy.primerange(2, 2 ** s):
        v *= max((al + 1) * l ** (-al / s) for al in range(0, 60))
    return v


if __name__ == '__main__':
    t0 = time.time()
    k3, k4 = tau_const(3), tau_const(4)
    assert tau_const_pow(3) == Fraction(1536, 35) and tau_const_pow(4) == Fraction(127401984, 25025)
    assert Fraction(1536, 35) <= Fraction(35273, 10000) ** 3 and Fraction(127401984, 25025) <= Fraction(84470, 10000) ** 4
    print("kappa_3^3 = 1536/35, kappa_4^4 = 127401984/25025 (exact)")
    print(f"kappa_3 = {k3:.6f}, kappa_4 = {k4:.6f};  kappa_3*10822^(-1/6) = {k3*10822**(-1/6):.6f}; "
          f"kappa_3*42000^(-1/6) = {k3*42000**(-1/6):.6f}; kappa_4*340000^(-1/4) = {k4*340000**(-1/4):.6f}")
    assert k3 < 3.5273 and k4 < 8.4470
    # exact versions of the three threshold checks (kappa_3^6 <= theta^6 N, kappa_4^4 <= theta^4 N)
    assert (Fraction(1536, 35) ** 2 <= Fraction(3, 4) ** 6 * 10822 and Fraction(1536, 35) ** 2 < Fraction(5983, 10000) ** 6 * 42000
            and Fraction(127401984, 25025) < Fraction(35, 100) ** 4 * 340000)
    assert k3 * 10822 ** (-1 / 6) <= 0.75 and k3 * 42000 ** (-1 / 6) < 0.5983 and k4 * 340000 ** (-1 / 4) < 0.35

    # ---------------- q = 2
    print("q=2: exact local maxima R*_a(o), o <= 60 (five largest per a, as (o, value)):")
    R2 = {}
    for a in range(0, 7):
        R2[a] = {o: Rstar(2, o, a) for o in range(1, 61)}
        top = sorted(R2[a].items(), key=lambda t: -t[1])[:5]
        print(f"   a={a}: {[(o, str(v)) for o, v in top]}")
    assert max(v for o, v in R2[0].items() if o not in (1, 2, 3, 6)) <= Fraction(2, 5)
    assert max(v for o, v in R2[1].items() if o not in (1, 2, 6)) <= Fraction(3, 8) and max(R2[1].values()) == Fraction(3, 4)
    assert R2[2][4] == Fraction(7, 16) and max(v for o, v in R2[2].items() if o != 4) <= Fraction(3, 8)
    assert all(max(R2[a].values()) <= Fraction(15, 64) for a in range(3, 7))
    r90 = {a: Rstar(2, 90, a) for a in range(0, 4)}
    print("   R*_a(90):", {a: str(v) for a, v in r90.items()})
    assert r90[1] == Fraction(2, 15)
    S2 = S_table(2, 340000, 19)            # 2^19 > 340000, so a <= 19 covers every a (f_a decreases for a >= v_2(o))
    s0 = sup(S2, 2, 0, 61, 340000)
    s1 = max(sup(S2, 2, a, 61, 340000, (90,) if a == 1 else ()) for a in range(1, 20))
    s2 = max(sup(S2, 2, a, 61, 340000) for a in range(2, 20))
    s3 = max(sup(S2, 2, a, 61, 340000) for a in range(3, 20))
    print(f"   61 <= o <= 340000: sup f_0 = {s0}; sup_(a>=1) f_a without (o,a) = (90,1): {s1}; "
          f"f_1(90) = {f_a(90, 1, 2)}; sup_(a>=2) f_a = {s2}; sup_(a>=3) f_a = {s3}   [{time.time()-t0:.0f}s]")
    assert bounded(S2, 2, 0, 61, 340000, Fraction(22, 63))
    assert all(bounded(S2, 2, a, 61, 340000, Fraction(12, 35), (90,) if a == 1 else ()) for a in range(1, 20))
    assert all(bounded(S2, 2, a, 61, 340000, Fraction(121, 360)) for a in range(2, 20))
    assert all(bounded(S2, 2, a, 61, 340000, Fraction(5, 16)) for a in range(3, 20))
    # ---------------- q = 3
    print("q=3: exact local maxima R*_a(o), o <= 36 (six largest per a):")
    R3 = {}
    for a in range(0, 5):
        R3[a] = {o: Rstar(3, o, a) for o in range(1, 37)}
        top = sorted(R3[a].items(), key=lambda t: -t[1])[:6]
        print(f"   a={a}: {[(o, str(v)) for o, v in top]}")
    assert max(v for o, v in R3[0].items() if o not in (1, 2, 4, 8)) <= Fraction(7, 16)
    assert all(max(R3[a].values()) <= Fraction(4, 9) for a in range(1, 5))
    S3 = S_table(3, 42000, 10)             # 3^10 > 42000
    t0_ = sup(S3, 3, 0, 37, 42000)
    t1_ = max(sup(S3, 3, a, 37, 42000) for a in range(1, 11))
    print(f"   37 <= o <= 42000: sup f_0 = {t0_}; sup_(a>=1) f_a = {t1_}")
    assert bounded(S3, 3, 0, 37, 42000, Fraction(3, 5))
    assert all(bounded(S3, 3, a, 37, 42000, Fraction(4667, 10000)) for a in range(1, 11))
    # ---------------- q = 4
    # n even (a >= 1): sup_(a>=1) f_a(o) <= 3/4 for o <= 12000 (beyond: kappa_3 o^(-1/6) <= 3/4, checked above).
    # n odd (a = 0): f_0(o) <= 2/3 for o >= 2 is proved by hand in Prop 6.5(a); here it is also checked for o <= 12000.
    S4 = S_table(2, 12000, 14)             # 2^14 > 12000
    ua = max(sup(S4, 2, a, 1, 12000) for a in range(1, 15))
    u0 = sup(S4, 2, 0, 2, 12000)
    print(f"q=4: sup_(a>=1) f_a(o), o <= 12000: {ua};  sup f_0(o), 2 <= o <= 12000: {u0} "
          f"(exact f_0(3) = {f_a(3, 0, 2)})   [{time.time()-t0:.0f}s]")
    assert all(bounded(S4, 2, a, 1, 12000, Fraction(3, 4)) for a in range(1, 15))
    assert bounded(S4, 2, 0, 2, 12000, Fraction(2, 3)) and f_a(3, 0, 2) == Fraction(2, 3)
    print("PASSED: all constants of Prop 6.5 confirmed")
