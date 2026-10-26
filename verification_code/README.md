# Python programs for the computer-assisted steps

These programs carry out every computer-assisted step of the paper *Resolvent Components of Completely Normal Elements
and the Morgan–Mullen Conjecture* (Section 9 of the paper lists them). They also test the theorems of Sections 2–3,
Theorem 4.2(a) and Corollaries 8.8 and 8.9(a) against the *definition* of complete normality on small fields. The
Lean 4 formalisation in the root of this repository carries out every computer-assisted step again as a verified computation (a Boolean checker with a kernel-checked
soundness proof, or a proof checked by the kernel directly; in a few places by a different route; see its README).

## Run

```bash
pip install sympy numpy mpmath galois
# exact versions of EXPECTED_OUTPUT.txt: pip install sympy==1.14.0 numpy==2.4.6 mpmath==1.3.0 galois==0.4.11
python run_all.py          # any system, including Windows (Anaconda Prompt); about 4 minutes on one core
bash run_all.sh            # the same with bash; PYTHON=python bash run_all.sh selects another interpreter
```

`EXPECTED_OUTPUT.txt` was produced on Windows, on one core of a laptop with an Intel Core Ultra 7 155H processor,
with Python 3.11.16 (Anaconda), sympy 1.14.0, numpy 2.4.6, mpmath 1.3.0 and galois 0.4.11; the same output (apart
from run times) was obtained on Linux with Python 3.13.16, sympy 1.14.0, numpy 2.5.3, mpmath 1.3.0 and galois 0.4.11.
The libraries are cited in the paper (SymPy: Meurer et al., PeerJ
Comput. Sci. 3 (2017) e103; NumPy: Harris et al., Nature 585 (2020) 357–362; mpmath: https://mpmath.org;
galois: M. Hostetter, https://github.com/mhostetter/galois).

Compare the output with `EXPECTED_OUTPUT.txt` (only the run times differ).

Every block ends with `PASSED`, `OK`, `verified` or (for the examples) `reproduced`. If an assertion fails, the script stops with a traceback.

## What each script checks

| script | statement | what it does | time |
|---|---|---|---|
| `bruteforce_small_fields.py` | Lemma 2.3, Thm 2.5, 2.6, 3.2, Lemma 3.3, Thm 4.2(a), Cor 8.8, Cor 8.9(a) | For 30 small pairs, every w: CN by definition ⇔ all essential fibre sums ≠ 0; kernel sizes; independence of components; CN_q(n) ≥ (q−1)^n′ q^((p^a−1)n′) with equality iff n′ ∣ q−1; with the exact number PCN_q(n) of primitive CN elements, the two-sided estimate of Thm 4.2(a) and both inequalities of Cor 8.9(a) (check (C1) of the paper) | 2 min |
| `struct_and_exactmax.py` | Thm 7.2, Prop 7.7, Thm 7.8 (i) | Step (i): N** = 42, 378, 16, 320 for (q,o0) = (2,3), (2,6), (3,2), (3,4), and for all n0 ∣ N** every component without codimension-1 conditions has weight ≤ W(q); for comparison the exact maximal weights (q=2: o0 ≤ 8, q=3: o0 ≤ 6); Thm 7.2 (a)–(c) on about 1.1·10⁵ components (check (C2) of the paper) | 30 s |
| `weights.py` | Thm 7.8 (ii)–(vi) | W_cl (q = 2: o0 ≤ 4095, q = 3: o0 ≤ 374) and W_cr (4 ≤ q ≤ 31, o0 < o1(q)) with cut-off o0 + 41 and tail 3m²Dq^(−m); Lemma 7.5 for q = 2, o0 ≥ 4096; the Rosser–Schoenfeld tail 3o0³(2.83/q)^o0; the uniform bound for q ≥ 32; in exact arithmetic except the floating-point checks listed below; checks that W_cl > W(q) exactly for (q,o0) = (2,3), (2,6), (3,2), (3,4) among q = 2, o0 ≤ 8 and q = 3, o0 ≤ 6 | 1 s |
| `bounds_for_M.py` | Prop 6.5 | Local maxima R*_a(o); the bounds for f_a(o) on the finite ranges, in exact integer arithmetic; κ₃³ = 1536/35, κ₄⁴ = 127401984/25025; for q = 4 also f_0(o) ≤ 2/3 for 2 ≤ o ≤ 12000 (proved by hand in Prop 6.5(a)) | 15 s |
| `thresholds.py` | Prop 8.3 | F_k(n_*) ≥ 0 and the condition on a_k n_* ln q, with 50 digits; each threshold n_* is the least possible for its k (check (C3) of the paper) | 2 s |
| `finite_ranges.py` | Prop 8.4 | Criterion (*) with exact M, S for every q < n below the thresholds (q = 4: 4 < n < 1010); the pairs with margin < 1 bit are exactly the 70 certified ones | 1 min |
| `pcn_certificates.py --verify` | Prop 8.5 | Re-checks the 70 primitive CN elements in `pcn_certificates.txt` | 6 s |
| `examples.py` | §10, §12 (not part of the proof) | The example (2,4599) of Section 10 (types, the 63 components, weights, S, M, the bounds for δ, L and ω, the margins and the resulting bounds of Cor 8.9(a)) and the examples (2,21) (components, passing counts, CN_2(21) = 259308) and (3,10) of Section 12 | 5 s |

(Approximate times on one core of the laptop above, rounded; they vary with the machine.)

Helper modules:

- `mmlib.py`: orders, essential types, exact M and S, the ω-bound. Proposition 8.4 rests on `essential_types`,
  `M_S_g` and `omega_bound` alone (about 60 lines), so this is the file to read first.
- `components.py`: explicit components by union–find on q-orbits.
- `closure.py`: the closure (B) of Section 7.
- `gfp.py`: arithmetic in F_p[x]/(f) for the certificates.

All computations of the proof use exact integer or rational arithmetic, except: the margins of criterion (*) in `finite_ranges.py`
(double precision; every accepted pair has at least one bit to spare); the analytic thresholds in `thresholds.py`
(`mpmath`, 50 digits); the second bound for t_k in Lemma 5.1 (`mmlib.py`, double precision with a safety margin of
10^-9, so that rounding can only increase it); and a few comparisons with wide margins in `weights.py`
(e^1.03883 < 2.83 and the signs of two derivatives). Section 12 of the paper ("What the proof uses") gives the same
list. (The comparisons with Theorem 4.2(a) and Corollary 8.9(a) in `bruteforce_small_fields.py` and some of the values
printed by `examples.py`, which are not part of the proof, also use floating point.)

## Certificates

Each line of `pcn_certificates.txt` reads `q n | f | w | primes of q^n−1`. The lists are coefficients, lowest
degree first. The check:

- f is monic of degree m = rn over F_p (so F_p[x]/(f) has q^n elements).
- w^(q^n−1) = 1 and w^((q^n−1)/ℓ) ≠ 1 for every listed prime ℓ. This makes F_p[x]/(f) a field and w
  primitive; the script also confirms that dividing q^n−1 by the listed primes as often as possible leaves 1, and
  proves that they are prime (`sympy.isprime`, deterministic below 2^64; Lucas' test, with the factorisation of
  ℓ−1, for the one larger prime, an 88-bit factor of 2^378−1).
- For every d ∣ n, the F_p-rank of {γ^j · w^(q^(dt))} is full, where γ = w^((q^n−1)/(q^d−1)). This is
  exactly "normal over F_{q^d}".

`python pcn_certificates.py --selftest` applies the order test to every element of F_{2^6}, F_{3^4} and F_{2^12}
and the rank test to the elements that pass it, and prints the number of primitive elements (next to φ(q^n−1)) and of primitive CN elements (6, 16 and 360;
check (C4) of the paper). The numbers are printed for inspection; they are not compared automatically with an
independent count. `python pcn_certificates.py` (without options) searches the certificates again
and rewrites the file; with its fixed random seed it reproduces the same file in about 3 minutes.

## What the code does *not* check

The hand proofs. The scripts test consequences (brute force on small fields, about 10⁵ components) and
compute the constants; they do not replace reading the proofs in the paper.
