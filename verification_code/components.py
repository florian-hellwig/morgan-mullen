"""
components.py -- explicit enumeration of all essential conditions of (q, n) and of their components
(union-find on the q-orbits of mu_{n'}, which is what the component relation reduces to by Lemma 3.3(a)).
Used to check Theorem 7.2 and step (i) of the proof of Theorem 7.8 (via Prop 7.7).
"""
from math import gcd
from fractions import Fraction
from mmlib import divisors, ordmod, split_p, char_of


def enumerate_components(q, n):
    p, _ = char_of(q)
    a, n1 = split_p(n, p)
    # q-orbits of Z/n1 (eta = zeta^i)
    orb = [-1] * n1
    orbits = []
    for i in range(n1):
        if orb[i] < 0:
            j, O = i, []
            while orb[j] < 0:
                orb[j] = len(orbits)
                O.append(j)
                j = (j * q) % n1
            orbits.append(O)
    parent = list(range(len(orbits)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    conds = []                                   # (d, k, e, o, fibre)
    for d in divisors(n):
        c, d1 = split_p(d, p)
        N = n1 // d1
        Qd = pow(q, d, N) if N > 1 else 0
        seen = bytearray(N)
        for k in range(N):
            if seen[k]:
                continue
            j = k
            while not seen[j]:
                seen[j] = 1
                j = (j * Qd) % N if N > 1 else 0
            e = N // gcd(N, k) if N > 1 else 1
            o = ordmod(q, e)
            if o % d:
                continue                         # not essential
            fib = [(k + t * N) % n1 for t in range(d1)]
            conds.append((d, k, e, o, fib))
            r0 = find(orb[fib[0]])
            for i in fib[1:]:
                r = find(orb[i])
                if r != r0:
                    parent[r] = r0
    comps = {}
    for cnd in conds:
        comps.setdefault(find(orb[cnd[4][0]]), {'conds': [], 'orbits': set()})['conds'].append(cnd)
    for a_, O in enumerate(orbits):
        r = find(a_)
        comps.setdefault(r, {'conds': [], 'orbits': set()})['orbits'].add(a_)
    out = []
    for C in comps.values():
        V = [i for a_ in C['orbits'] for i in orbits[a_]]
        C['V'] = V
        C['dim'] = len(V) * p ** a
        C['weight'] = sum((Fraction(1, q ** cnd[3]) for cnd in C['conds']), Fraction(0))
        C['o0'] = min(cnd[3] for cnd in C['conds'])
        out.append(C)
    return out, conds, n1, p, a
