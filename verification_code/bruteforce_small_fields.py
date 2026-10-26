"""
bruteforce_small_fields.py -- checks Sections 2-3 of the paper against the definition of complete
normality, on small fields, by exhaustive enumeration of E = F_{q^n}.

For each pair (q, n) with ord_{n'}(q) | n (so that the n'-th roots of unity lie in E):
  (T1) w is CN (by definition: for every d | n the conjugates sigma^{dt}(w), t < n/d, are
       F_{q^d}-linearly independent, tested as an F_p-rank computation)
       <=>  C_{d,k}(w) != 0 for every essential condition (d,k)            [Thm 2.5 + Thm 2.6]
  (T2) the same with all conditions                                        [Thm 2.5]
  (T3) every kernel V_{d,k} has exactly q^(n - lcm(d, ord_e(q))) elements   [Thm 2.5, codimension]
  (T4) components (adjacency = sharing a pair orbit) give independent events:
       #CN * |E|^(r-1) == prod_K #G_K   (r = number of components)          [Thm 3.2]
  (T5) every component other than a codimension-1 singleton contains no codimension-1 condition
       and the codimension-1 conditions are singletons                      [Lemma 3.3(c)]
  (T6) #CN >= (q-1)^n' q^((p^a-1) n'), with equality iff n' | q-1         [Corollary 8.8]
  (T7) with PCN = #{primitive CN elements}, theta = phi(q^n-1)/(q^n-1), delta = CN/q^n,
       beta = 1 + (2^omega - 1) q^(n/2) and L = prod over essential C of 2(1 - q^-o(C)):
       |PCN - theta (q^n-1) delta| <= theta beta (L - delta)                [Thm 4.2(a)]
       |PCN - theta CN| <= theta 2^omega q^(n/2) L <= 2^(omega+M+c(W)S) q^(-n/2) theta CN,
       with W = W(q) of Theorem 7.8 (checked after dividing by theta CN > 0)  [Corollary 8.9(a)]
Usage: python3 bruteforce_small_fields.py            (runs the default list, about two minutes)
"""
import sys, time, itertools
from math import gcd, lcm
import numpy as np
import galois
from math import log2
from fractions import Fraction
from mmlib import divisors, ordmod, split_p, char_of, factor, phi
from weights import W as W_TABLE


def batched_rank(A, p):
    """ranks of a batch of matrices A[b] over F_p (A: int array (B, R, C))"""
    A = (A % p).astype(np.int64)
    B, R, C = A.shape
    inv = np.zeros(p, dtype=np.int64)
    for x in range(1, p):
        inv[x] = pow(x, p - 2, p)
    row = np.zeros(B, dtype=np.int64)
    ar = np.arange(R)
    for col in range(C):
        mask = (A[:, :, col] != 0) & (ar[None, :] >= row[:, None])
        has = mask.any(axis=1)
        idx = np.nonzero(has)[0]
        if len(idx) == 0:
            continue
        piv = np.argmax(mask[idx], axis=1)
        r0 = row[idx]
        tmp = A[idx, r0].copy()
        A[idx, r0] = A[idx, piv]
        A[idx, piv] = tmp
        pv = A[idx, r0, col]
        A[idx, r0] = (A[idx, r0] * inv[pv][:, None]) % p
        f = A[idx, :, col].copy()
        f[np.arange(len(idx)), r0] = 0
        A[idx] = (A[idx] - f[:, :, None] * A[idx, r0][:, None, :]) % p
        row[idx] += 1
    return row


def run(q, n, verbose=True):
    t0 = time.time()
    p, r = char_of(q)
    a, n1 = split_p(n, p)
    assert (q ** n - 1) % n1 == 0, "needs mu_{n'} inside E"
    m = r * n                                  # [E : F_p]
    E = galois.GF(p ** m)
    W = E.elements                              # all w in E
    alpha = E.primitive_element
    sig = [W ** (q ** t) for t in range(n)]     # sigma^t(W), t = 0..n-1

    # ---------- CN by definition (F_p-rank test for each d | n)
    cn_def = np.ones(len(W), dtype=bool)
    for d in divisors(n):
        M = n // d
        gamma = alpha ** ((q ** n - 1) // (q ** d - 1))      # generates F_{q^d}^*
        rows = []
        for t in range(M):
            for j in range(r * d):
                rows.append((gamma ** j) * sig[d * t])      # gamma^j sigma^{dt}(w)
        A = np.stack([np.asarray(x.vector()) for x in rows], axis=1)   # (|E|, m, m)
        cn_def &= batched_rank(np.asarray(A), p) == m

    # ---------- resolvent coordinates F_eta(u), eta = zeta^i
    zeta = alpha ** ((q ** n - 1) // n1)
    pa = p ** a
    F = {}
    for i in range(n1):
        for u in range(pa):
            acc = E.Zeros(len(W))
            for t in range(n):
                if t % pa == u:
                    acc = acc + (zeta ** (-(i * t) % n1)) * sig[t]
            F[(i, u)] = acc

    # pair orbits of (i, u) -> (q i mod n1, u + 1 mod p^a)
    orb = {}
    for i in range(n1):
        for u in range(pa):
            if (i, u) in orb:
                continue
            x = (i, u)
            oid = len(set(orb.values()))
            while x not in orb:
                orb[x] = oid
                x = ((x[0] * q) % n1, (x[1] + 1) % pa)

    # ---------- conditions
    conds = []      # (d, k, codim, essential, set of pair-orbit ids, zero-mask)
    for d in divisors(n):
        c, d1 = split_p(d, p)
        N = n1 // d1
        seen = set()
        for k in range(N):
            if k in seen:
                continue
            j = k
            while j not in seen:                 # identify (d,k) ~ (d, q^d k)
                seen.add(j)
                j = (j * pow(q, d, N)) % N if N > 1 else 0
            e = N // gcd(N, k) if N > 1 else 1
            o = ordmod(q, e)
            codim = lcm(d, o)
            ess = (o % d == 0)
            val = E.Zeros(len(W))
            supp = set()
            for t in range(d1):
                i = (k + t * N) % n1
                for u in range(0, pa, p ** c):
                    val = val + F[(i, u)]
                    supp.add(orb[(i, u)])
            zero = (val == 0)
            conds.append((d, k, codim, ess, supp, zero))
            # (T3) kernel size
            assert zero.sum() == q ** (n - codim), ("T3 fails", q, n, d, k)

    ess = [c for c in conds if c[3]]
    allnz_ess = np.ones(len(W), bool)
    for c in ess:
        allnz_ess &= ~c[5]
    allnz_all = np.ones(len(W), bool)
    for c in conds:
        allnz_all &= ~c[5]
    assert np.array_equal(cn_def, allnz_ess), ("T1 fails", q, n)
    assert np.array_equal(cn_def, allnz_all), ("T2 fails", q, n)

    # ---------- components (union-find on essential conditions sharing a pair orbit)
    parent = list(range(len(ess)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i1, i2 in itertools.combinations(range(len(ess)), 2):
        if ess[i1][4] & ess[i2][4]:
            parent[find(i1)] = find(i2)
    comps = {}
    for i in range(len(ess)):
        comps.setdefault(find(i), []).append(ess[i])
    counts = []
    for K in comps.values():
        G = np.ones(len(W), bool)
        for c in K:
            G &= ~c[5]
        counts.append(int(G.sum()))
        codims = [c[2] for c in K]
        if 1 in codims:                                            # (T5)
            assert len(K) == 1, ("T5 fails", q, n)
    lhs = int(cn_def.sum()) * len(W) ** (len(comps) - 1)
    rhs = 1
    for x in counts:
        rhs *= x
    assert lhs == rhs, ("T4 fails", q, n)
    bound = (q - 1) ** n1 * q ** ((p ** a - 1) * n1)              # (T6) Corollary 8.8 (Hachenberger's bound)
    assert int(cn_def.sum()) >= bound and ((int(cn_def.sum()) == bound) == ((q - 1) % n1 == 0)), ("T6 fails", q, n)
    # (T7) Theorem 4.2(a) and Corollary 8.9(a), with the exact PCN
    Nm = q ** n - 1
    nz = np.asarray(W) != 0
    prim = np.zeros(len(W), dtype=bool)
    logs = np.asarray(E(np.asarray(W)[nz]).log(), dtype=np.int64)
    prim[nz] = np.gcd(logs, Nm) == 1
    cnt, pcn = int(cn_def.sum()), int((cn_def & prim).sum())
    assert int(prim.sum()) == phi(Nm), ("primitive count", q, n)
    om = len(factor(Nm))
    theta = Fraction(phi(Nm), Nm)
    delta = Fraction(cnt, q ** n)
    codims = [c[2] for c in ess]
    L = Fraction(1)
    for o in codims:
        L *= 2 * (1 - Fraction(1, q ** o))
    Mq, M1 = len(codims), codims.count(1)
    S = sum((Fraction(1, q ** o) for o in codims if o >= 2), Fraction(0))
    beta = 1 + (2 ** om - 1) * q ** (n / 2)
    tol = 1e-12
    assert float(abs(pcn - theta * Nm * delta)) <= float(theta) * beta * float(L - delta) * (1 + tol), ("T7 Thm4.2a", q, n)
    assert L <= 2 ** Mq * (1 - Fraction(1, q)) ** M1, ("T7 L", q, n)
    rel = float(abs(Fraction(pcn) / (theta * cnt) - 1))
    b1 = 2 ** om * float(L) / (q ** (n / 2) * float(delta))
    Wq = float(W_TABLE[q])
    b2 = 2 ** (om + Mq + log2(1 / (1 - Wq)) / Wq * float(S)) / q ** (n / 2)
    assert rel <= b1 * (1 + tol) and b1 <= b2 * (1 + 1e-9), ("T7 Cor8.9a", q, n)
    if verbose:
        big = max(len(K) for K in comps.values())
        print(f"(q,n)=({q},{n}): |E|={len(W)}, CN={int(cn_def.sum())}, {len(conds)} conditions "
              f"({len(ess)} essential), {len(comps)} components (largest has {big} conditions): "
              f"PCN={pcn}: T1-T7 OK  [{time.time()-t0:.1f}s]", flush=True)
    return int(cn_def.sum())


DEFAULT = [(2, 2), (2, 4), (2, 6), (2, 8), (2, 12), (2, 16), (3, 2), (3, 3), (3, 4), (3, 6), (3, 8),
           (3, 9), (4, 2), (4, 3), (4, 4), (4, 6), (5, 2), (5, 4), (5, 5), (5, 6), (7, 3), (7, 4),
           (8, 2), (8, 4), (9, 2), (9, 3), (9, 4), (11, 4), (13, 3), (13, 4)]

if __name__ == '__main__':
    pairs = DEFAULT if len(sys.argv) == 1 else [tuple(map(int, s.split(','))) for s in sys.argv[1:]]
    for q, n in pairs:
        run(q, n)
    print("ALL CHECKS PASSED")
