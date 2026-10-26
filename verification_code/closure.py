"""
closure.py -- the closure (B) of Section 7 of the paper:
  K0 = o0' (q^o0 - 1);  O0 = lcm(o0, ord_{l^v}(q) : l | o0'),  v = v_l(o0') + v_l(q^o0 - 1);
  D0 = (O0)_{p'};  D_{i+1} = lcm(D_i, (ord_{D_i}(q))_{p'}) until stable = D_inf;
  K = lcm(K0, D_inf);  O_inf = lcm(O0, ord_{D_inf}(q));  N** = lcm(K, O_inf).
Only v_l(q^o0 - 1) for small l and orders modulo the D_i are needed (no factoring of q^o0 - 1).
"""
from math import lcm
from mmlib import factor, ordmod, split_p, char_of


def pfree(m, p):
    return split_p(m, p)[1]


def v_l_qpow(q, o0, l):
    v, m = 0, l
    while pow(q, o0, m) == 1:
        v += 1
        m *= l
    return v


def closure(q, o0):
    p, _ = char_of(q)
    o0p = pfree(o0, p)
    O0 = o0
    for l, a in factor(o0p) if o0p > 1 else ():
        v = a + v_l_qpow(q, o0, l)
        O0 = lcm(O0, ordmod(q, l ** v))
    D = pfree(O0, p)
    D0 = D
    while True:
        Dn = lcm(D, pfree(ordmod(q, D), p))
        if Dn == D:
            break
        D = Dn
    Oinf = lcm(O0, ordmod(q, D))
    K0 = o0p * (q ** o0 - 1)
    K = lcm(K0, D)
    Nss = lcm(K, Oinf)
    return dict(K0=K0, O0=O0, D0=D0, Dinf=D, Oinf=Oinf, K=K, Nss=Nss)
