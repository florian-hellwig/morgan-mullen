"""
pcn_certificates.py -- explicit primitive completely normal (PCN) elements (Prop 8.5) for the 70 pairs (q, n)
with q < n for which criterion (*) of Theorem 8.1(b), evaluated as in finite_ranges.py (exact M and S, and the
bound of Lemma 5.1 for omega(q^n-1)), fails or holds with less than 1 bit to spare: the 50 failures, all with
n <= 160, and 20 tight pairs, all with n <= 104 except (2,378).  (With the exact omega(q^n-1), (*) fails at 41
of the 70 pairs.)  All other pairs with
q < n below the thresholds of Prop 8.3 satisfy (*) with at least 1 bit to spare (finite_ranges.py), and the
pairs with n <= q are covered by Garefalakis-Kapetanakis (JPAA 2019, Theorem 1.3).

Certificate for (q, n), q = p^r, m = r n:  a monic f in F_p[x] of degree m and w in R = F_p[x]/(f) with
 (P) w^N = 1 and w^(N/l) != 1 for every prime l | N, where N = p^m - 1 = q^n - 1.
     Then w has order N = |R| - 1, so every non-zero element of R is a power of w, R is a field
     (hence f is irreducible) and w is primitive.  No separate irreducibility test is needed.
     --verify also checks that f is monic of degree m (so that |R| = p^m) and that the prime factors l of N
     are prime (sympy.isprime, deterministic below 2^64; Lucas' test above, see proven_prime).
 (CN) for every d | n: the m elements gamma_d^j * sigma^(d t)(w)  (0 <= j < r d, 0 <= t < n/d) have
     F_p-rank m, where sigma(y) = y^q and gamma_d = w^(N/(q^d - 1)).  gamma_d has order q^d - 1, so it
     generates F_{q^d} and {gamma_d^j : j < r d} is an F_p-basis of F_{q^d}; full rank therefore means
     that sigma^(d t)(w), t < n/d, is an F_{q^d}-basis of E, i.e. w is normal over F_{q^d} (definition).
Output: pcn_certificates.txt (f and w as coefficient lists, lowest degree first; primes of N).
Run: python3 pcn_certificates.py --verify       re-checks the 70 certificates in pcn_certificates.txt
     python3 pcn_certificates.py --selftest     applies the checks to every element of three small fields
     python3 pcn_certificates.py                searches the certificates again and rewrites the file
                                                (about 3 minutes)
"""
import sys, time, random, ast
import numpy as np
import sympy
from gfp import Ring, rank_mod_p
from mmlib import divisors, char_of

# (a) the 50 pairs with q < n where criterion (*), evaluated as in finite_ranges.py, fails (all with n <= 160), and
# (b) the 20 pairs with q < n where (*) holds but with less than 1 bit to spare (certified for robustness);
# finite_ranges.py checks that this is exactly the set of pairs with margin < 1 bit.
PAIRS = {2: [3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 21, 24, 27, 30, 36, 40, 42, 54, 60, 63, 126, 378],
         3: [4, 5, 6, 7, 8, 10, 12, 13, 16, 20, 24, 26, 32, 39, 40, 80, 160],
         4: [5, 6, 7, 9, 10, 15, 21, 30],
         5: [6, 8, 12, 16, 18, 24, 32, 48, 104],
         7: [8, 12, 16, 18, 24, 48],
         9: [10, 20],
         11: [12],
         13: [20],
         19: [24]}
NPAIRS = sum(len(v) for v in PAIRS.values())


def proven_prime(l):
    """primality with a proof: sympy.isprime is deterministic below 2^64; a larger l is proved prime by
    Lucas' test (a^(l-1) = 1 and a^((l-1)/r) != 1 mod l for every prime r | l - 1, with the prime factors
    r of l - 1 proved prime in the same way).  Only one factor in the certificates exceeds 2^64 (88 bits,
    of 2^378 - 1)."""
    if l < 2 ** 64:
        return sympy.isprime(l)
    fac = sympy.factorint(l - 1)
    prod = 1
    for r, e in fac.items():
        prod *= r ** e
    if prod != l - 1 or not all(proven_prime(int(r)) for r in fac):
        return False
    for a in range(2, 1000):
        if pow(a, l - 1, l) != 1:
            return False
        if all(pow(a, (l - 1) // r, l) != 1 for r in fac):
            return True
    raise RuntimeError("no Lucas witness found below 1000")


def primes_of(q, n):
    ps = set()
    for d in divisors(n):
        ps |= set(int(x) for x in sympy.factorint(int(sympy.cyclotomic_poly(d, q))).keys())
    N, M = q ** n - 1, q ** n - 1
    for l in ps:
        assert proven_prime(l) and N % l == 0
        while M % l == 0:
            M //= l
    assert M == 1, "factorisation incomplete"
    return sorted(ps)


def check_primitive(Rg, w, N, ls):
    one = Rg.one()
    if not np.array_equal(Rg.pow(w, N), one):
        return False
    return all(not np.array_equal(Rg.pow(w, N // l), one) for l in ls)


def check_cn(Rg, w, q, n, r, p, N, Fr):
    m = r * n
    sig = [w]
    for t in range(1, n):
        sig.append((Fr @ sig[-1]) % p)                 # sigma^t(w)
    for d in divisors(n):
        gamma = Rg.pow(w, N // (q ** d - 1))
        gj = [Rg.one()]
        for j in range(1, r * d):
            gj.append(Rg.mul(gj[-1], gamma))
        rows = [Rg.mul(gj[j], sig[d * t]) for t in range(n // d) for j in range(r * d)]
        if rank_mod_p(np.array(rows), p) != m:
            return False
    return True


def random_monic(p, m, rng):
    return [rng.randrange(p) for _ in range(m)] + [1]


def irreducible_candidate(p, m, rng):
    """a monic polynomial of degree m over F_p that is very likely irreducible: random, filtered by the
    necessary condition x^(p^m) = x in F_p[x]/(f).  (Irreducibility is not assumed anywhere: it is proved
    by the certificate itself, since w of order p^m - 1 forces F_p[x]/(f) to be a field.)"""
    while True:
        f = random_monic(p, m, rng)
        if f[0] == 0:
            continue
        Rg = Ring(p, f)
        x = Rg.elem([0, 1])
        if np.array_equal(Rg.pow(x, p ** m), x):
            return f, Rg


def certify(q, n, rng):
    p, r = char_of(q)
    m = r * n
    N = q ** n - 1
    ls = primes_of(q, n)
    while True:
        f, Rg = irreducible_candidate(p, m, rng)
        Fr = Rg.frobenius_matrix(q)
        for _ in range(200):
            w = Rg.elem([rng.randrange(p) for _ in range(m)])
            if not check_primitive(Rg, w, N, ls):
                continue
            if check_cn(Rg, w, q, n, r, p, N, Fr):
                return f, w, ls


def verify_file(path='pcn_certificates.txt'):
    k = 0
    for line in open(path):
        if line.startswith('#') or not line.strip():
            continue
        head, fs, ws, lss = [s.strip() for s in line.split('|')]
        q, n = map(int, head.split())
        f, w, ls = ast.literal_eval(fs), ast.literal_eval(ws), ast.literal_eval(lss)
        p, r = char_of(q)
        # f monic of degree m = r n over F_p, w of degree < m (so R = F_p[x]/(f) has p^m = q^n elements)
        assert len(f) - 1 == r * n and f[-1] % p == 1 and len(w) <= r * n, (q, n, "f not monic of degree r*n")
        assert ls == primes_of(q, n)
        Rg = Ring(p, f)
        wv = Rg.elem(w)
        assert check_primitive(Rg, wv, q ** n - 1, ls), (q, n, "not primitive")
        assert check_cn(Rg, wv, q, n, r, p, q ** n - 1, Rg.frobenius_matrix(q)), (q, n, "not CN")
        k += 1
        print(f"  ({q},{n}) verified", flush=True)
    print(f"{k} certificates verified")


def selftest():
    """apply the order test to every element of three small fields and the rank test to the elements that pass it,
    and print the numbers of primitive elements
    (next to phi(q^n - 1)) and of primitive CN elements found by them (for inspection; not compared with an
    independent count here)"""
    import itertools
    for q, n, f in [(2, 6, [1, 1, 0, 0, 0, 0, 1]), (3, 4, [2, 0, 0, 1, 1]), (2, 12, None)]:
        p, r = char_of(q)
        m = r * n
        rng = random.Random(7)
        if f is None:
            while True:
                f = random_monic(p, m, rng)
                Rg = Ring(p, f)
                if any(check_primitive(Rg, Rg.elem([rng.randrange(p) for _ in range(m)]), q ** n - 1,
                                       primes_of(q, n)) for _ in range(40)):
                    break
        Rg = Ring(p, f)
        Fr = Rg.frobenius_matrix(q)
        N = q ** n - 1
        ls = primes_of(q, n)
        prim = cnp = 0
        for coeffs in itertools.product(range(p), repeat=m):
            w = Rg.elem(list(coeffs))
            if check_primitive(Rg, w, N, ls):
                prim += 1
                cnp += check_cn(Rg, w, q, n, r, p, N, Fr)
        print(f"  selftest ({q},{n}): primitive = {prim} (expected phi(q^n-1) = {sympy.totient(N)}), "
              f"primitive CN = {cnp}")


if __name__ == '__main__':
    if '--verify' in sys.argv:
        verify_file()
        sys.exit()
    if '--selftest' in sys.argv:
        selftest()
        sys.exit()
    rng = random.Random(20260925)
    out = open('pcn_certificates.txt', 'w')
    out.write("# q n | f over F_p (coefficients, lowest degree first; monic, degree r*n) | w (coefficients) "
              "| primes of q^n - 1\n")
    t0 = time.time()
    k = 0
    for q, ns in PAIRS.items():
        for n in ns:
            f, w, ls = certify(q, n, rng)
            k += 1
            out.write(f"{q} {n} | {f} | {[int(c) for c in w]} | {ls}\n")
            out.flush()
            print(f"[{k:2d}/{NPAIRS}] (q,n)=({q},{n}) certified [{time.time()-t0:.0f}s]", flush=True)
    print(f"ALL {NPAIRS} PAIRS CERTIFIED")
