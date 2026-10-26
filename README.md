# Resolvent Components of Completely Normal Elements and the Morgan–Mullen Conjecture: Lean 4 Formalisation and Python Programs

[![Lean CI](https://github.com/florian-hellwig/morgan-mullen/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/florian-hellwig/morgan-mullen/actions/workflows/lean_action_ci.yml)

This repository contains the Lean 4 formalisation (with Mathlib) and the Python programs accompanying the paper

> F. Hellwig, *Resolvent Components of Completely Normal Elements and the Morgan–Mullen Conjecture*, arXiv: *link to follow*.

The main formal statement is the conjecture of I. H. Morgan and G. L. Mullen (*Completely normal primitive basis
generators of finite fields*, Utilitas Math. 49 (1996), 21–43):

> For every prime power $q$ and every $n \ge 1$, the field $`\mathbb{F}_{q^n}`$ contains an element that is
> **primitive** (it generates the cyclic group $`\mathbb{F}_{q^n}^\times`$) and **completely normal** over
> $`\mathbb{F}_q`$ (it generates a normal basis of $`\mathbb{F}_{q^n}`$ over every intermediate field
> $`\mathbb{F}_{q^d}`$, $d \mid n$).

The case $n \le q$ is a theorem of T. Garefalakis and G. Kapetanakis and enters as an axiom; the case $n > q$ and
Corollaries 8.8 and 8.9 of the paper, including every computer-assisted step, are formalised. What has to be trusted is
listed [below](#what-is-trusted).

All statement numbers below ("Lemma 2.3", "Theorem 7.8", …) and the notation in the docstrings ($\mathcal E$,
$\mathcal C$, $w_{\mathcal C}$, $\sigma_1$, $\kappa_3$, $\vartheta$, …) refer to that paper. Some file, namespace, section and
command names keep the numbers of an earlier draft (`Sec2Lemma5.lean`, `Sec7W28*.lean` and the namespace `W28`,
`section Lemma12`, `section Prop26`, `#audit_deep_cor36`, `#audit_deep_cor37`, which refer to Lemma 2.3, Theorem 7.8,
Lemma 4.1, Proposition 7.7 and Corollaries 8.8 and 8.9). The formalisation
follows the paper's proofs, with the same constants, tables, ranges and thresholds, except where noted
[below](#where-the-formalisation-differs-from-the-paper) (and in Appendix A of the paper). The Python programs for the
computer-assisted steps, which the paper cites, are in the folder [`verification_code/`](verification_code/)
(see its README).

**Status:** there is no `sorry`, `lake build` finishes without errors or warnings, every
computer-assisted step of the paper is carried out again inside Lean as a verified computation, and the main theorem
depends only on the three axioms on which all of Mathlib rests, the two axioms behind the evaluation of the
verified checkers outside the kernel, and two results from the literature (see [What is trusted](#what-is-trusted)).

## The main theorem

`MorganMullen.morgan_mullen` in [`MorganMullen/Sec8Main.lean`](MorganMullen/Sec8Main.lean):

```lean
theorem morgan_mullen (F E : Type*) [Field F] [Field E] [Finite E] [Algebra F E] :
    HasMMProperty F E
```

That is: for every finite field extension $E/F$, the field $E$ contains a primitive element that is
completely normal over $F$.

## Corollary 8.8: Hachenberger's lower bound

Corollary 8.8 of the paper, in [`MorganMullen/Sec8Corollary.lean`](MorganMullen/Sec8Corollary.lean): for every
prime power $q$ and $n = p^a n'$ with $p \nmid n'$, the number $\mathrm{CN}_q(n)$ of completely normal elements
satisfies $\mathrm{CN}_q(n) \ge (q-1)^{n'} q^{(p^a-1)n'}$, with equality if and only if $n' \mid q - 1$.

```lean
theorem hachenberger_lower_bound :
    (q - 1) ^ Model.nfree q n * q ^ ((Model.pa q n - 1) * Model.nfree q n) ≤ cnCount F E
theorem hachenberger_eq_iff :
    cnCount F E = (q - 1) ^ Model.nfree q n * q ^ ((Model.pa q n - 1) * Model.nfree q n) ↔
      Model.nfree q n ∣ q - 1
```

for finite fields `F`, `E` with `[Algebra F E]`, `q = Fintype.card F` and `n = Module.finrank F E`. Here
`cnCount F E` is the number of `w : E` with `IsCompletelyNormal F E w` (`Sec3Product.lean`), `Model.nfree q n` is
the $p$-free part $n'$ of $n$ and `Model.pa q n` is $p^a$ (`Model.lean`). The proof follows the paper's proof of
Corollary 8.8, with the differences listed [below](#where-the-formalisation-differs-from-the-paper); it uses Theorem 7.8 (`weight_le_Wq`) and hence the Rosser–Schoenfeld axiom, but not
`garefalakis_kapetanakis`:

```
'MorganMullen.hachenberger_lower_bound' depends on axioms:
  [propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler, MorganMullen.rosser_schoenfeld_psi]
```

(the same for `hachenberger_eq_iff`). Its proofs evaluate 6 of the 25 checkers, those of Theorem 7.8; `AuditDeep.lean`
checks that they are among the checkers of the main theorem.

## Corollary 8.9: primitive completely normal elements

Corollary 8.9 of the paper, in [`MorganMullen/Sec8PCN.lean`](MorganMullen/Sec8PCN.lean). With
$\theta = \varphi(q^n - 1)/(q^n - 1)$, $\omega = \omega(q^n - 1)$, $L$ as in Theorem 4.2, $W = W(q)$ as in Theorem 7.8 and
$c(W)$ as in Theorem 8.1:

(a) for every pair $(q, n)$,
$`|\mathrm{PCN}_q(n) - \theta\,\mathrm{CN}_q(n)| \le \theta\, 2^\omega q^{n/2} L \le 2^{\omega + M + c(W) S} q^{-n/2}\, \theta\, \mathrm{CN}_q(n)`$;

(b) the ratio $`\mathrm{PCN}_q(n)/(\theta\,\mathrm{CN}_q(n))`$ tends to 1 as $q^n \to \infty$.

```lean
theorem pcn_sub_theta_cn_abs_le :
    |(pcnCount F E : ℝ) - thetaFrac (Fintype.card E - 1) * cnCount F E| ≤
      thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
        Real.sqrt (Fintype.card E) * lFactor F E
theorem pcn_error_le_star :
    thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
        Real.sqrt (Fintype.card E) * lFactor F E ≤
      (2 : ℝ) ^ (((Fintype.card E - 1).primeFactors.card : ℝ) + (Model.numM q n : ℝ) +
          cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) / Real.sqrt (Fintype.card E) *
        thetaFrac (Fintype.card E - 1) * cnCount F E
theorem pcn_ratio_tendsto_one :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ (F : Type u) (E : Type v) [Field F] [Fintype F] [Field E]
      [Fintype E] [Algebra F E], X ≤ Fintype.card E →
        |(pcnCount F E : ℝ) / (thetaFrac (Fintype.card E - 1) * cnCount F E) - 1| < ε
```

(`pcn_theta_cn` is (a) as one statement.) Here `pcnCount F E` is the number of primitive completely normal elements
(`Sec4Counting.lean`), `thetaFrac N` is $\varphi(N)/N$, `twoPowOmega N` is $2^{\omega(N)}$, `lFactor F E` is $L$,
`Wq q` is $W(q)$, `cW` is $c$, and `Model.numM`, `Model.sumS` are $M$ and $S$ (with `q = Fintype.card F`,
`n = Module.finrank F E`, $q^{n/2}$ = `Real.sqrt (Fintype.card E)`). The first inequality of (a) uses no computation and
depends only on the three axioms of Mathlib; the second inequality and (b) use Theorem 7.8 (and (b) also
Proposition 6.5), and hence the Rosser–Schoenfeld axiom, but not `garefalakis_kapetanakis`:

```
'MorganMullen.pcn_sub_theta_cn_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MorganMullen.pcn_ratio_tendsto_one' depends on axioms:
  [propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler, MorganMullen.rosser_schoenfeld_psi]
```

(`pcn_error_le_star` and `pcn_theta_cn` have the same list as (b).) The proof of the first inequality evaluates no checker,
that of the second inequality the 6 checkers of Theorem 7.8, and that of (b) 11 checkers (those of Theorem 7.8 and the 5
of Proposition 6.5); `AuditDeep.lean` lists them and checks that they are among the checkers of the main theorem.

## Statement numbers and Lean names

| paper | Lean | file |
|---|---|---|
| Theorem 2.6 (essential reduction) | `isCompletelyNormal_iff_essential` | `Sec2Coordinates` |
| Theorem 3.2 (product formula) | `delta_eq_prod`, `delta_ge_prod` | `Sec3Product` |
| Theorem 4.2, $L \le 2^M (1 - \frac1q)^{M_1}$ | `lFactor_le` | `Sec4Counting` |
| Theorem 4.2 (a) | `pcn_sub_main_abs_le` | `Sec4Counting` |
| Theorem 4.2 (b) | `pcn_ge`, `hasMM_of_counting` | `Sec4Counting` |
| Lemma 6.1 | `Model.numM_eq_sum_rho` ($M = \sum_\eta \rho(\eta)$), `Model.sumS_eq_sum_sEta` ($S = \sum_\eta s(\eta)$) | `Sec6NumberOfConditions` |
| Corollary 6.4 | `Model.numM_le_n` | `Sec6NumberOfConditions` |
| Theorem 7.8 | `weight_le_Wq` | `Sec7Weights` |
| Theorem 8.1 (a) | `delta_ge_deltaStar` | `Sec8Main` |
| Theorem 8.1 (b) | `hasMM_of_star` | `Sec8Main` |
| Lemma 8.2 (a), (b) | `two_pow_omega_le`, `sumS_le_gq` | `Sec8Main` |
| Theorem 8.6 (Main Theorem) | `morgan_mullen` | `Sec8Main` |
| Corollary 8.8 | `hachenberger_lower_bound`, `hachenberger_eq_iff` | `Sec8Corollary` |
| Corollary 8.9 (a) | `pcn_sub_theta_cn_abs_le`, `pcn_error_le_star` (together `pcn_theta_cn`) | `Sec8PCN` |
| Corollary 8.9 (b) | `pcn_ratio_tendsto_one` | `Sec8PCN` |

## What is trusted

```
#print axioms MorganMullen.morgan_mullen
'MorganMullen.morgan_mullen' depends on axioms:
  [propext, Classical.choice, Quot.sound,                          -- the axioms of Mathlib
   Lean.ofReduceBool, Lean.trustCompiler,                          -- evaluation of the 25 checkers
   MorganMullen.garefalakis_kapetanakis,                           -- cited result 1
   MorganMullen.rosser_schoenfeld_psi]                             -- cited result 2
```

The reference output is in [`AXIOMS_AUDIT.txt`](AXIOMS_AUDIT.txt); the CI workflow re-checks this list (and those of
Corollaries 8.8 and 8.9) on every push and fails if one of them changes.

**Cited results.** [`MorganMullen/Axioms.lean`](MorganMullen/Axioms.lean) states exactly the two external results
that the proof uses besides classical facts (paper, §12, *What the proof uses*):

| axiom | statement | source |
|---|---|---|
| `garefalakis_kapetanakis` | every extension $\mathbb{F}_{q^n}/\mathbb{F}_q$ with $n \le q$ has the Morgan–Mullen property | T. Garefalakis, G. Kapetanakis, *On the existence of primitive completely normal bases of finite fields*, J. Pure Appl. Algebra 223 (2019), 909–921, Theorem 1.3 (their Theorem 1.4 covers more generally $n' < q$, $n'$ the $p$-free part of $n$) |
| `rosser_schoenfeld_psi` | $`\psi(x) < 1.03883\,x`$ for all $x > 0$, where $\psi(x) = \log \mathrm{lcm}(1, \dots, \lfloor x \rfloor)$ is Chebyshev's function (Mathlib's `Chebyshev.psi`); the paper writes the bound as $`\log \mathrm{lcm}(1, \dots, \lfloor x \rfloor) < 1.03883\,x`$ | J. B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94, Theorem 12 |

The proof of Theorem 1.3 of Garefalakis–Kapetanakis uses a computer calculation; 24 of the 37 pairs left by it are
completely basic extensions, and the remaining 13 pairs are settled by the explicit examples of I. H. Morgan and G. L. Mullen
(Utilitas Math. 49 (1996), 21–43). All this enters only through this axiom (paper, §1.2 and Remark 8.7).

Everything else (normal basis theorem, Dedekind's lemma, Gauss sums, …) comes from Mathlib or is proved here.

**Verified computations.** Each large computer-assisted step is a computable Boolean checker together with a
Lean proof that `checker = true` implies the mathematical statement; smaller computations (for instance $\kappa_3$,
$\kappa_4$ and the rows of $(\ast\ast)$) are proved by the kernel directly. The 25 checkers are evaluated outside
the kernel through `Lean.ofReduceBool` (this is where `Lean.ofReduceBool` and `Lean.trustCompiler` come from): Lean's
compiler translates them and Lean's interpreter runs them, calling natively compiled library code (such as GMP
arithmetic) where it exists. So, as for every use of `native_decide`, one trusts Lean's compiler and interpreter and the
native implementations of the library functions used; the proofs that the checkers are sound are checked by the
kernel. `native_decide` itself is not used (in Lean v4.34.1 it would record each evaluation as an auxiliary axiom
`c = true`; the two constants above are marked as deprecated in favour of that mechanism, which relies on the same
compiler and interpreter; the toolchain is pinned). Data produced outside Lean
(factorisations, the certified multiples $\hat O$, $\hat D$, $\hat M$ of Theorem 7.8, Pratt certificates, …), and anything computed by an unverified Lean function
(such as the labelling of the components in Theorem 7.8), is only ever *checked*, never
trusted.

[`AuditDeep.lean`](AuditDeep.lean) makes this part of the trusted base explicit. It lists the 25 checkers that
the proof evaluates, collects the 7224 constants they depend on (228 of them from this project), and fails if any
project constant among them carries `@[implemented_by]` or `@[extern]` (none does), or if the project declares an
axiom other than the two above. The 104 constants with such attributes that do occur lie outside this project
(for instance GMP arithmetic on `Nat` and `Int`, arrays and well-founded recursion in Lean core); they are what
`Lean.trustCompiler` stands for, as for every proof that uses `native_decide`.

## Checking the definitions

Lean checks the proof, relative to the trusted base described above. What a human reader still has to
check is that the theorem says what the conjecture says, i.e. the four definitions in
[`MorganMullen/Basic.lean`](MorganMullen/Basic.lean) (plus the two axioms above):

```lean
/-- `w` is normal over `K`: its conjugates `σ w`, `σ ∈ Gal(E/K)`, form a `K`-basis of `E`. -/
def IsNormalElem (K E : Type*) [Field K] [Field E] [Algebra K E] (w : E) : Prop :=
  LinearIndependent K (fun σ : Gal(E/K) => σ w) ∧
    Submodule.span K (Set.range fun σ : Gal(E/K) => σ w) = ⊤

/-- `w` is completely normal over `F`: normal over every intermediate field `F ⊆ K ⊆ E`. -/
def IsCompletelyNormal (F E : Type*) [Field F] [Field E] [Algebra F E] (w : E) : Prop :=
  ∀ K : IntermediateField F E, IsNormalElem K E w

/-- `w` is primitive: non-zero, and every non-zero element of `E` is a power of `w`. -/
def IsPrimitiveElem {E : Type*} [Field E] (w : E) : Prop :=
  w ≠ 0 ∧ ∀ x : E, x ≠ 0 → ∃ k : ℕ, w ^ k = x

/-- The Morgan–Mullen property of `E/F`. -/
def HasMMProperty (F E : Type*) [Field F] [Field E] [Algebra F E] : Prop :=
  ∃ w : E, IsPrimitiveElem w ∧ IsCompletelyNormal F E w
```

(`Gal(E/K)` is Mathlib notation for `E ≃ₐ[K] E`. For a finite field the intermediate fields are exactly the
$\mathbb{F}_{q^d}$, $d \mid n$, including $F$ itself and $E$.)

The statements of Corollaries 8.8 and 8.9 use further definitions, which have to be checked as well: `cnCount`
(`Sec3Product.lean`), `pcnCount` and `lFactor` (`Sec4Counting.lean`), `thetaFrac` and `twoPowOmega`
(`Sec4Abstract.lean`), `Model.nfree`, `Model.pa`, `Model.numM` and `Model.sumS` (`Model.lean`), `Wq`
(`Sec7Weights.lean`) and `cW` (`Sec8Defs.lean`). Here `lFactor`, `Model.numM` and `Model.sumS` ($L$, $M$ and $S$) are
defined through a combinatorial model of the essential conditions in `Model.lean` (a condition is a level $d$ together
with an orbit of targets in $`\mathbb Z/n'`$).

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan) (the Lean version manager; it installs the
toolchain pinned in `lean-toolchain`, Lean `v4.34.1`) and git. Mathlib `v4.34.1` is pinned in
`lake-manifest.json`. Then:

```bash
git clone https://github.com/florian-hellwig/morgan-mullen.git
cd morgan-mullen
lake exe cache get            # download prebuilt Mathlib (recommended)
lake build                    # build the formalisation: about 10 minutes (Props. 6.5 and 8.4 take most of it)
lake env lean Audit.lean      # print the axioms of the main theorem and of Cor. 8.8, 8.9 (compare with AXIOMS_AUDIT.txt)
lake env lean AuditDeep.lean  # list the verified checkers and check that none relies on custom compiled code
```

`lake build` should finish with `Build completed successfully` and no warnings;
`grep -rn sorry MorganMullen/` finds nothing. If the Mathlib cache cannot be downloaded, `lake build` compiles
the required part of Mathlib from source (about 3600 files; several hours on a laptop with two cores).

The same steps run automatically on GitHub Actions
([`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)).

## Computer-assisted steps

| statement | what Lean checks | files | time |
|---|---|---|---|
| Prop. 6.5 (bounds for $M$, $q \le 4$) | the tables of the proof: $f_a$ for $61 \le o \le 340000$ ($q = 2$), $37 \le o \le 42000$ ($q = 3$), $o \le 12000$ ($q = 4$); the local maxima $`R^*_a(o)`$ for $o \le 60$, $a \le 6$, and $`R^*_1(90)`$ ($q = 2$) and $o \le 36$, $a \le 4$ ($q = 3$), via factorisations of $q^o - 1$ checked by trial division; the tail bounds with $\kappa_3$, $\kappa_4$ are proved | `Sec6FaBound`, `Sec6Comp`, `Sec6Runs` | ≈ 4 min |
| Thm. 7.8 (weights $W(q)$), steps (ii)–(vi) | $W_{cl}$ with certified multiples of $O_\infty$, $D_\infty$ for $q = 2$, $o_0 \le 4095$ and $q = 3$, $o_0 \le 374$; $W_{cr}$ for $4 \le q \le 31$, $o_0 < o_1(q)$; cut-off $o_0 + 41$; the Rosser–Schoenfeld tail; the uniform bound for $q \ge 32$ | `Sec7W28*` | ≈ 5 s |
| Thm. 7.8, step (i) | a labelling of the components (computed by an unverified function, then checked), for all $n_0 \mid 42, 378$ ($q = 2$) and $n_0 \mid 16, 320$ ($q = 3$) | `ExactComp`, `ExactSound`, `Sec7Exact` | < 5 s |
| Prop. 8.3 (analytic range) | upper bounds for $\log_2 C_k$ and the inequality $(\ast\ast)$ row by row, at the thresholds of the table | `Sec8Analytic` | ≈ 30 s |
| Prop. 8.4 (finite ranges) | criterion $(\ast)$ with one bit to spare, exact $M$, each term $q^{-o}$ of $S$ replaced by an upper bound that is a multiple of $2^{-64}$, for all $q < 32$, $q < n$ below the thresholds, except the 70 pairs of Prop. 8.5 | `Fin32*`, `Sec8Finite` | ≈ 2.5 min |
| Prop. 8.5 (70 certificates) | explicit primitive completely normal elements, with Pratt certificates | `Cert*`, `Sec8Certificates` | ≈ 80 s |

(Times: build of the file on one core.)

## Where the formalisation differs from the paper

The formalisation follows the proofs of the paper, with the same constants, tables, ranges and thresholds, except
where noted below (Appendix A of the paper summarises the differences). One argument takes a different route:

* **Lemma 4.1** (`primitive_charSum_le`): the paper uses Vinogradov's formula for the indicator of the primitive
  elements; here the explicit coefficients are not needed. After a discrete logarithm $E^\times \cong \mathbb Z/(q^n - 1)$
  the indicator of the primitive elements is $\prod_{\ell \mid q^n - 1} (1 - 1_{\ell \mathbb Z/(q^n-1)})$, and the
  $\ell^1$-argument of Theorem 4.2 is applied on $\mathbb Z/(q^n - 1)$: the coefficients have $\ell^1$-norm at most
  $2^\omega \theta$, the trivial character has coefficient $\theta$, and the others give Gauss sums of absolute value
  $q^{n/2}$ (Mathlib).

Some elementary steps are arranged differently: Lemma 2.3(a) is derived from its case $t = 0$; in Theorem 2.5 the identity
$`R_{\hat\xi} = \frac1{d'} C_{d,k}`$ is obtained directly from the definition of the coordinates by a geometric series over the
fibre; the independence of $`\{w : C_{d,k}(w) = 0\}`$ of the representative $k$ (the paragraph after Definition 2.4) is derived from this
identity and the Frobenius rule for $`R_{\hat\xi}`$; Theorem 3.2 uses Lemma 2.3(c) in a block form, for the coordinate tuples of
whole pair orbits (`coord_product`); Proposition 6.3 is formalised for rational $\vartheta$, $\Theta$, which suffices
for its applications; the proof of Corollary 8.8 uses only $`M_1 \le \#\{\eta \in \mu_{n'} : o(\eta) = 1\}`$
(`card_codim_one_le`), not the equality $M_1 = \gcd(n', q - 1)$, it proves $(\dagger)$ in the form
$(1 - W)^{s(\eta)/W} \ge 1 - \frac1q$, for $q \ge 3$ by Bernoulli's inequality $(9/5)^x \le 1 + \frac45 x$
($x = \frac94 s(\eta) \le \frac12$) instead of $c(\frac49) < 1.91$ and $3.82 q^{-2} < 1/(q \ln 2)$
(`lt_rpow_of_three_le`), and in the case of equality with $q = 2$, $o(\zeta) = 2$, $2 \mid n$ ($\zeta$ a generator of
$\mu_{n'}$) it obtains strictness from the strict union bound in the component of the level-one condition through
$\zeta$, which contains a second (level-two) condition (`prob_goodSet_gt`), without determining $n' = 3$ or the weight
$\frac34$; and in the large-$n$ step of Corollary 8.9 (b) the
exponent $\omega + M + c(W) S - \frac n2 \log_2 q$ of the bound of (a) is shown to be at most $-h(n) - 1$ directly
(`relErr_lt_large`), instead of through $\Delta$ and $\log_2(q^n - 1) \ge n \log_2 q - 1$, and $h(n) \to \infty$ is made
explicit through $g_2(y) \le \frac{14}3 y + 3$ and $\log_2 n \le 4\sqrt n$ (`exists_hPCN_ge`); that $c$ is
increasing, which the paper only states, is proved from the concavity lemma `rpow_div_le_one_sub` (`cW_le_cW`).

Where the Python programs and the formalisation carry out a computation differently, Appendix A of the paper
lists the differences:

* **Prop. 6.5**: the factorisations of $q^o - 1$ are given as data and checked (product and trial division); Python
  takes them from `sympy`.
* **Theorem 7.8, step (i)**: a labelling of $\mu_{n_0'}$ (computed by the unverified function `labArr`) is checked
  to be invariant under $\eta \mapsto \eta^q$ and constant on the fibres of the essential conditions (Python uses
  the components themselves), and the total weight of the conditions of codimension $\ge 2$ with each label is
  bounded (`ExactComp`, `ExactSound`); a certified multiple of $`N^{**}`$ is used.
* **Theorem 7.8, steps (ii) and (iii)**: $W_{cl}$ is evaluated with multiples of $O_\infty$ and $D_\infty$
  certified by congruences (the criterion in Appendix A of the paper; the triples $\hat O$, $\hat D$, $\hat M$ of
  `Sec7W28Data`); Python computes
  $O_\infty$ and $D_\infty$ themselves.
* **Prop. 8.3**: the inequalities $(\ast\ast)$ are proved with rational bounds (Python: 50 digits); for $q = 17$ the
  exponent $k = 7$ is used (Python: $k = 6$; same threshold $29$).
* **Prop. 8.4**: Lean checks exactly the pairs of the proposition (Python checks all $n < 131200$ for $q = 3$). Within
  Lemma 5.1, Lean uses a sieve value for $t_k$ (only "$\ge t_k$" is proved) when $\varphi(k)\lfloor\log_2 q\rfloor \le 3000$,
  and otherwise an integer upper bound for the second bound of Lemma 5.1 (Python uses the second bound first and the
  exact $t_k$ where needed). $(\ast)$ is verified with the bound of Lemma 5.1 plus $1$ in place of $\omega(q^n - 1)$, i.e.
  with one bit to spare, in exact rational arithmetic: each $q^{-o}$ in $S$ is replaced by an upper bound that is a
  multiple of $2^{-64}$, and $\log_2 q$, $c(W)$ by proved rational bounds; $`\log_2(q^n-1) \ge n\log_2 q - \frac{1}{1000}`$
  is used, which holds since $`q^n \ge 2048`$ for every accepted pair.
* **Prop. 8.5**: every prime factor of $q^n - 1$ is certified by a Pratt certificate (Python: `sympy.isprime`,
  deterministic below $2^{64}$, and Lucas' test for the one larger factor); the full $\mathbb F_p$-rank is certified by
  checking a computed inverse matrix; and $\gamma$ is computed as $\prod_{0 \le t < n/d} \sigma^{dt}(w)$
  ($= w^{(q^n-1)/(q^d-1)}$), with only a check that $\gamma^{q^d} = \gamma$, which suffices for the implication from full rank to
  normality.

One detail of form: **Theorem 7.2** (`structure_a`, `structure_b`) does not state that $K$ is $p$-free, because
hypothesis (ii) already forces it (`ordMod q K = 0` if $p \mid K$, so (ii) fails unless $K = 0$, a trivial case).

Statements given only for illustration or information are not formalised; the proof does not use them. These include
the exact values of $`N^{**}`$ and $W_{cl}$, the exact maxima and the
other values quoted for information in the proof of Theorem 7.8, the identification of the closure (B) with the least
admissible $K$ (§7), the margins quoted after Prop. 8.4, the note after the proof of Prop. 8.5 on the choice of the 70 pairs, the
remarks following the proof of Cor. 8.9, Remark 8.10, the paragraph *Sharpness* in §12 (attainment of $W(2)$,
$W(3)$ and of $M\le n$, and the lower bound for $\delta_n$), the comparisons with earlier work (after
the proof of Thm. 2.6, in §4, in Remark 8.7 and in §12), the example $(2,8)$ in §12, the worked
examples (§1.5, §2, §3, §5, §10 and §12), and the checks (C1)–(C4) of Section 11.

## Repository layout

```
.
├── MorganMullen.lean           root module, imports (directly or indirectly) every file of the proof
├── MorganMullen/               the formalisation (one file per part of the paper, see below)
├── Audit.lean                  prints the axioms of the main theorem and of Corollaries 8.8 and 8.9
├── AuditDeep.lean              lists the verified checkers and audits what they depend on
├── AXIOMS_AUDIT.txt            reference output of Audit.lean and AuditDeep.lean
├── verification_code/          Python programs and data for the computer-assisted steps (own README)
├── lakefile.toml               Lake project file (depends on Mathlib v4.34.1)
├── lake-manifest.json          exact pinned versions of Mathlib and its dependencies
├── lean-toolchain              Lean version (v4.34.1)
├── .github/workflows/          CI: build, no sorry, axiom check, deep audit
├── CITATION.cff                citation metadata
└── LICENSE                     Apache License 2.0
```

| file in `MorganMullen/` | content (paper numbering) |
|---|---|
| `NT.lean` | $p$-free part, $\mathrm{ord}_e(q)$ |
| `Basic.lean` | normal, completely normal, primitive, Morgan–Mullen property |
| `Axioms.lean` | the two cited results |
| `Model.lean`, `ModelBasic.lean` | combinatorial model: pairs, conditions, targets, codimensions, components |
| `Sec2Coordinates.lean` | Lemma 2.1, Def. 2.2, Def. 2.4, Thms. 2.5, 2.6 |
| `Sec2Lemma5.lean` | Lemma 2.3 (coordinates, Frobenius, product decomposition) |
| `Sec3Components.lean` | Lemma 3.3 |
| `Sec3Product.lean` | Thm. 3.2 (product formula) |
| `Sec4Abstract.lean` | Lemma 4.1 (Gauss sums; $\ell^1$-argument on $\mathbb Z/(q^n-1)$) and the counting criterion in abstract form |
| `Sec4Counting.lean` | Thm. 4.2 (with (a) and (b)) |
| `Sec5Omega.lean` | Lemma 5.1 |
| `Sec5Types.lean` | Lemma 5.2 (essential types, exact $M$, $S$) |
| `Sec6NumberOfConditions.lean` | Lemma 6.1 (both identities), Lemma 6.2, Prop. 6.3, Cor. 6.4, Prop. 6.5 |
| `Sec6FaBound.lean`, `Sec6Comp.lean`, `Sec6Runs.lean` | Prop. 6.5: tail bound for $f_a$, verified checkers, runs |
| `Sec7Pratt.lean` | Pratt closure (for Lemma 7.5) |
| `Sec7Structure.lean` | Lemma 7.1, Thm. 7.2, choices (A)/(B), Lemma 7.4, Cor. 7.6, Prop. 7.7, Lemma 7.5 |
| `ExactComp.lean`, `ExactSound.lean`, `Sec7Exact.lean` | Thm. 7.8, step (i): $(q, o_0) = (2,3), (2,6), (3,2), (3,4)$ |
| `Sec7W28Data.lean`, `Sec7W28Defs.lean`, `Sec7W28Sound.lean`, `Sec7W28Runs.lean` | Thm. 7.8, steps (ii)–(vi): certificates, checkers, soundness, runs |
| `Sec7Weights.lean` | Thm. 7.8 (`weight_le_Wq`) |
| `CertDefs.lean`, `CertData.lean`, `CertProofs.lean`, `Sec8Certificates.lean` | Prop. 8.5 (70 explicit certificates) |
| `Sec8Defs.lean` | $c(W)$, criterion $(\ast)$, ranges of Prop. 8.3 |
| `Fin32Comp.lean`, `Fin32Sound.lean`, `Fin32Runs.lean`, `Sec8Finite.lean` | Prop. 8.4 (finite ranges) |
| `Sec8Analytic.lean` | Prop. 8.3: the inequality $(\ast\ast)$ row by row |
| `Sec8Main.lean` | Thm. 8.1 (a), (b), Lemma 8.2, Prop. 8.3, Thm. 8.6 (main theorem) |
| `Sec8Corollary.lean` | Cor. 8.8 (Hachenberger's lower bound for $\mathrm{CN}_q(n)$, with the case of equality) |
| `Sec8PCN.lean` | Cor. 8.9 (primitive completely normal elements: the error bound (a) and $`\mathrm{PCN}_q(n)/(\theta\,\mathrm{CN}_q(n)) \to 1`$ (b)) |

## Statement on the use of AI tools

The research questions, the overall direction and all final decisions of this work are the author's; the arguments
were generated by AI language models (Claude Fable 5.1 and Claude Opus 5.5, Anthropic) under the author's direction.
In particular, the author posed the questions that led to extending the known cases of the conjecture to further pairs
$`(q,n)`$, and directed the work on the pair $`(2,4599)`$ (Section 10 of the paper), which the first approaches could
not settle, and on generalising the argument found for it. The text of the paper was drafted by the same AI models
under the author's direction and heavily revised by the author. The author has checked every step of the final proof
by hand and has verified the main citations against the original sources. The author takes full responsibility for
the correctness of the results.

The Python programs in `verification_code` were written by AI under the author's direction; the author has run them
and confirmed their output, but has not reviewed their code line by line. In addition, at the author's request, AI
models reviewed the mathematics and reproduced all computations with separately written code, in many separate
sessions. The Lean 4 formalisation was generated entirely
by AI. The author has built it on his own computer and run its audit files, confirming that it relies only on the
axioms and the trusted base set out in [What is trusted](#what-is-trusted) and in Appendix A of the paper. He has also
verified that the formal statements of the main theorem and of Corollaries 8.8 and 8.9, together with the definitions
they use, faithfully capture these results and that the two cited results used as axioms are stated correctly; he has
not reviewed the rest of the formalisation.

## Citation

If you use the formalisation or the Python programs, please cite the paper (arXiv link to follow) and this repository.
GitHub's "Cite this repository" button gives the citation of the paper; the metadata of the repository itself are in
[`CITATION.cff`](CITATION.cff).

## Licence

Apache License 2.0, the same licence as Lean and Mathlib. See [`LICENSE`](LICENSE).
