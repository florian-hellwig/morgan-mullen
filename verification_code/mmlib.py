"""
mmlib.py -- helper library for the verification scripts: multiplicative orders, the essential types,
the exact values of M and S (Lemma 5.2), and the bound of Lemma 5.1 for omega(q^n - 1).

Notation: q = p^r, n = p^a * n1 with p not dividing n1 (n1 is the paper's n').
An essential type is a pair (d, e) with d | n, d = p^c d1, e | n1/d1 and d | ord_e(q).  There are
nu(d,e) = d*phi(e)/ord_e(q) essential conditions of that type, each of codimension ord_e(q) (Lemma 5.2).
"""
from math import gcd, log2, floor
from functools import lru_cache
from fractions import Fraction
import sympy


@lru_cache(maxsize=None)
def factor(n):
    return tuple(sorted(sympy.factorint(n).items()))


def divisors(n):
    ds = [1]
    for pr, ex in factor(n):
        ds = [d * pr ** i for d in ds for i in range(ex + 1)]
    return sorted(ds)


@lru_cache(maxsize=None)
def phi(n):
    r = n
    for pr, _ in factor(n):
        r = r // pr * (pr - 1)
    return r


@lru_cache(maxsize=None)
def ordmod(q, e):
    """multiplicative order of q modulo e (e >= 1, gcd(q,e) = 1); ord mod 1 is 1"""
    if e == 1:
        return 1
    assert gcd(q, e) == 1
    # order divides lambda(e); compute via phi(e) and strip primes
    o = phi(e)
    for pr, _ in factor(o):
        while o % pr == 0 and pow(q, o // pr, e) == 1:
            o //= pr
    return o


def char_of(q):
    f = factor(q)
    assert len(f) == 1, "q must be a prime power"
    return f[0]          # (p, r)


def split_p(n, p):
    a = 0
    while n % p == 0:
        n //= p
        a += 1
    return a, n          # n = p^a * n1


def essential_types(q, n):
    """list of (d, e, nu, o) over all essential types for (q, n)"""
    p, _ = char_of(q)
    a, n1 = split_p(n, p)
    out = []
    for d in divisors(n):
        c, d1 = split_p(d, p)
        N = n1 // d1
        for e in divisors(N):
            o = ordmod(q, e)
            if o % d == 0:
                nu = d * phi(e)
                assert nu % o == 0
                out.append((d, e, nu // o, o))
    return out


def M_S_g(q, n):
    """M = number of essential conditions, S = total weight of those with codim >= 2 (exact
    Fraction), g = M_1 = number of codimension-1 conditions"""
    M, S, g = 0, Fraction(0), 0
    for d, e, nu, o in essential_types(q, n):
        M += nu
        if o >= 2:
            S += Fraction(nu, q ** o)
        else:
            g += nu
    return M, S, g


# ---------------------------------------------------------------- omega(q^n - 1)
@lru_cache(maxsize=None)
def logprod_const(q):
    """c_q = -sum_{j>=1} log2(1 - q^-j), rounded up"""
    s = 0.0
    for j in range(1, 400):
        s -= log2(1.0 - q ** (-j))
    return s + 1e-9


@lru_cache(maxsize=None)
def t_crude(q, k):
    """second bound of Lemma 5.1 for the number of primes l with ord_l(q) = k (k >= 2):
    they are all = 1 mod m, m = lcm(2,k), so >= m+1, and their product divides Phi_k(q)
    <= 2^(phi(k) log2 q + c_q)."""
    m = k if k % 2 == 0 else 2 * k
    x = (phi(k) * log2(q) + logprod_const(q)) / log2(m + 1)
    return floor(x + 1e-9)


@lru_cache(maxsize=None)
def cyclo_value(k, q):
    num, den = 1, 1
    for d in divisors(k):
        mu = sympy.mobius(k // d)
        if mu == 1:
            num *= q ** d - 1
        elif mu == -1:
            den *= q ** d - 1
    assert num % den == 0
    return num // den


@lru_cache(maxsize=None)
def t_exact(q, k):
    """largest t such that the product of the t smallest primes = 1 mod lcm(2,k) is <= Phi_k(q)"""
    m = k if k % 2 == 0 else 2 * k
    V = cyclo_value(k, q)
    t, prod, cand = 0, 1, m + 1
    while True:
        while not sympy.isprime(cand):
            cand += m
        if prod * cand > V:
            return t
        prod *= cand
        t += 1
        cand += m


def omega_bound(q, n, exact=False):
    om = len(factor(q - 1)) if q > 2 else 0
    for k in divisors(n):
        if k > 1:
            om += t_exact(q, k) if exact else t_crude(q, k)
    return om


def cW(W):
    """c(W) = log2(1/(1-W))/W"""
    return log2(1.0 / (1.0 - W)) / W


def star_margin(q, n, W, exact_omega=False):
    """margin (in bits) of criterion (*) of Theorem 8.1(b) with exact M, S:
       log2(q^n - 1) - (n/2) log2 q - [omega + M + c(W) S]"""
    M, S, g = M_S_g(q, n)
    om = omega_bound(q, n, exact_omega)
    lhs = n * log2(q) / 2 + log2(1.0 - float(q) ** (-n))
    return lhs - (om + M + cW(W) * float(S)), M, S, om
