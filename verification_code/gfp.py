"""
gfp.py -- minimal, dependency-light arithmetic in F_p[x]/(f) with numpy (elements = int vectors of
length m, lowest degree first).  Used for the PCN certificates; it handles fields with m up to a few hundred.
"""
import numpy as np


class Ring:
    def __init__(self, p, f):
        """f: list of ints, lowest degree first, monic, degree m"""
        self.p = p
        self.f = [c % p for c in f]
        assert self.f[-1] == 1
        self.m = m = len(f) - 1
        # R[k] = x^(m+k) mod f, for k = 0..m-2
        R = np.zeros((max(m - 1, 1), m), dtype=np.int64)
        cur = np.array([(-c) % p for c in self.f[:m]], dtype=np.int64)       # x^m mod f
        for k in range(m - 1):
            R[k] = cur
            # multiply cur by x
            top = cur[-1]
            cur = np.concatenate(([0], cur[:-1]))
            cur = (cur + top * np.array([(-c) % p for c in self.f[:m]], dtype=np.int64)) % p
        self.R = R

    def elem(self, coeffs):
        v = np.zeros(self.m, dtype=np.int64)
        v[:len(coeffs)] = coeffs
        return v % self.p

    def one(self):
        return self.elem([1])

    def mul(self, a, b):
        c = np.convolve(a, b) % self.p
        m = self.m
        low, high = c[:m].copy(), c[m:]
        if len(high):
            low = (low + high @ self.R[:len(high)]) % self.p
        return low

    def pow(self, a, e):
        res = self.one()
        base = a.copy()
        while e:
            if e & 1:
                res = self.mul(res, base)
            e >>= 1
            if e:
                base = self.mul(base, base)
        return res

    def frobenius_matrix(self, q):
        """matrix F (m x m, over F_p) with F @ v = v^q  (x -> x^q is F_p-linear)"""
        xq = self.pow(self.elem([0, 1]), q)
        cols = [self.one()]
        for i in range(1, self.m):
            cols.append(self.mul(cols[-1], xq))
        return np.stack(cols, axis=1) % self.p


def rank_mod_2(A):
    """rank over F_2 with rows packed into Python integers (fast for large m)"""
    rows = [int(''.join(str(int(x)) for x in r), 2) for r in (np.array(A, dtype=np.int64) % 2)]
    rank = 0
    pivots = {}                                  # leading bit -> row
    for r in rows:
        while r:
            lb = r.bit_length() - 1
            if lb in pivots:
                r ^= pivots[lb]
            else:
                pivots[lb] = r
                rank += 1
                break
    return rank


def rank_mod_p(A, p):
    if p == 2:
        return rank_mod_2(A)
    A = np.array(A, dtype=np.int64) % p
    R, C = A.shape
    r = 0
    for c in range(C):
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * pow(int(A[r, c]), p - 2, p)) % p
        col = A[:, c].copy()
        col[r] = 0
        A = (A - np.outer(col, A[r])) % p
        r += 1
        if r == R:
            break
    return r
