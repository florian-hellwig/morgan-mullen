import MorganMullen.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# External results used as axioms

Only the two results that the paper cites from the literature and does not prove are axioms.
Everything classical that Mathlib provides (normal basis theorem, Dedekind's lemma,
`G(χ,ψ) G(χ⁻¹,ψ⁻¹) = q` for Gauss sums, …) is used from Mathlib instead.

1. `garefalakis_kapetanakis`: the Morgan–Mullen property for `n ≤ q`
   (T. Garefalakis, G. Kapetanakis, *On the existence of primitive completely normal bases of finite
   fields*, J. Pure Appl. Algebra 223 (2019) 909–921, Theorem 1.3; their Theorem 1.4 covers more
   generally the case that the `p`-free part `n'` of `n` satisfies `n' < q`). We only assume the case
   `n ≤ q`, which is all the proof uses (the proof of Theorem 8.6 in the paper).

2. `rosser_schoenfeld_psi`: `ψ(x) < 1.03883 x` for `x > 0`
   (J. B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
   Illinois J. Math. 6 (1962) 64–94, Theorem 12). Mathlib's `Chebyshev.psi x = ∑_{m ≤ x} Λ(m)`
   is the standard second Chebyshev function; `ψ(x) = log lcm(1, …, ⌊x⌋)`, so the axiom is the bound
   `log lcm(1, …, ⌊x⌋) < 1.03883 x` of the paper. Used in step (v) of the proof of Theorem 7.8.
-/

namespace MorganMullen

/-- **Cited result** (Garefalakis–Kapetanakis, JPAA 2019, Theorem 1.3): every extension
`𝔽_{q^n}/𝔽_q` with `n ≤ q` has the Morgan–Mullen property. -/
axiom garefalakis_kapetanakis (F E : Type*) [Field F] [Fintype F] [Field E] [Finite E]
    [Algebra F E] (h : Module.finrank F E ≤ Fintype.card F) : HasMMProperty F E

/-- **Cited result** (Rosser–Schoenfeld, Illinois J. Math. 1962, Theorem 12): `ψ(x) < 1.03883 x` for all `x > 0`. -/
axiom rosser_schoenfeld_psi (x : ℝ) (hx : 0 < x) : Chebyshev.psi x < 1.03883 * x

end MorganMullen
