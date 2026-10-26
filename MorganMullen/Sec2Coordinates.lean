import MorganMullen.Basic
import MorganMullen.ModelBasic
import MorganMullen.Sec3Components
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Section 2: coordinates by partial resolvents

* Lemma 2.1 (classical): normality via Lagrange resolvents `R_ξ`.
* Definition 2.2: the partial resolvents `F_η(w)(u)`.
* Lemma 2.3 (coordinates): `Sec2Lemma5.lean`.
* Definition 2.4 / Theorem 2.5: the fibre sums `C_{d,k}` and the fibre-sum criterion.
* Theorem 2.6: essential reduction.

Setting: `F` finite with `q = |F|`, `E/F` of degree `n`, `σ = frobeniusAlgHom F E` (`σ x = x^q`),
`Ω ⊇ E` a field (also an `F`-algebra, compatibly) containing a primitive `n'`-th root of unity `ζ`.
-/

set_option linter.unusedSectionVars false

namespace MorganMullen

open Module Finset FiniteField Polynomial

/-! ### Lemma 2.1

Notation: `L = 𝔽_Q`, `K = 𝔽_{Q^m}` (the paper's `𝔽_{Q^m}`), `M = [K:L]` (the paper's `m`), and
`τ = frobeniusAlgHom L K`, `τ(x) = x^Q` (the paper's `σ_Q`). -/

section Classical

variable {L K : Type*} [Field L] [Fintype L] [Field K] [Fintype K] [Algebra L K]
variable {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower L K Ω]

/-- The Lagrange resolvent `R_ξ(w) = ∑_{s ∈ ℤ/M} ξ^{-s} τ^s(w)` of `K/L`, `M = [K:L]`,
`τ(x) = x^Q`, `Q = |L|`. -/
noncomputable def lagrangeResolvent (ξ : Ω) : K →ₗ[L] Ω :=
  ∑ s ∈ range (finrank L K),
    (ξ⁻¹ ^ s) • ((IsScalarTower.toAlgHom L K Ω).toLinearMap ∘ₗ
      ((frobeniusAlgHom L K) ^ s).toLinearMap)

/-- `τ^M = 1`. -/
lemma frob_pow_finrank : (frobeniusAlgHom L K) ^ (finrank L K) = 1 := by
  rw [← orderOf_frobeniusAlgHom L K]; exact pow_orderOf_eq_one _

lemma frob_pow_apply (s : ℕ) (u : K) : ((frobeniusAlgHom L K) ^ s) u = u ^ (Fintype.card L ^ s) := by
  induction s generalizing u with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, coe_frobeniusAlgHom]
    show (u ^ Fintype.card L ^ s) ^ Fintype.card L = _
    rw [← pow_mul, pow_succ]

lemma lagrangeResolvent_apply (ξ : Ω) (u : K) :
    lagrangeResolvent (L := L) ξ u =
      ∑ s ∈ range (finrank L K), ξ⁻¹ ^ s * algebraMap K Ω (((frobeniusAlgHom L K) ^ s) u) := by
  simp [lagrangeResolvent, LinearMap.sum_apply]

/-- `R_ξ(τ u) = ξ R_ξ(u)` for `ξ^M = 1`. -/
lemma lagrangeResolvent_frob {ξ : Ω} (hξ : ξ ^ finrank L K = 1) (u : K) :
    lagrangeResolvent (L := L) ξ (frobeniusAlgHom L K u) = ξ * lagrangeResolvent (L := L) ξ u := by
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Module.finrank_pos (R := L) (M := K)).ne'] at hξ
    exact zero_ne_one hξ
  rw [lagrangeResolvent_apply, lagrangeResolvent_apply, Finset.mul_sum]
  -- shift the index
  have hshift : ∀ s, ξ⁻¹ ^ s * algebraMap K Ω (((frobeniusAlgHom L K) ^ s) (frobeniusAlgHom L K u)) =
      ξ * (ξ⁻¹ ^ (s + 1) * algebraMap K Ω (((frobeniusAlgHom L K) ^ (s + 1)) u)) := by
    intro s
    have hc : ξ⁻¹ ^ s = ξ * ξ⁻¹ ^ (s + 1) := by
      rw [pow_succ, mul_left_comm, mul_inv_cancel₀ hξ0, mul_one]
    rw [hc, pow_succ (frobeniusAlgHom L K) s, AlgHom.mul_apply, mul_assoc]
  simp_rw [hshift]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  set f : ℕ → Ω := fun i => ξ⁻¹ ^ i * algebraMap K Ω (((frobeniusAlgHom L K) ^ i) u) with hf
  have hM : f (finrank L K) = f 0 := by
    simp only [hf, frob_pow_finrank, AlgHom.one_apply, inv_pow, hξ, inv_one, pow_zero]
  have h1 := Finset.sum_range_succ f (finrank L K)
  have h2 := Finset.sum_range_succ' f (finrank L K)
  show ∑ i ∈ range (finrank L K), f (i + 1) = ∑ i ∈ range (finrank L K), f i
  rw [hM] at h1
  have := h1.symm.trans h2
  linear_combination -this

/-- `τ` as a linear endomorphism. -/
abbrev tauL (L K : Type*) [Field L] [Fintype L] [Field K] [Algebra L K] : Module.End L K :=
  (frobeniusAlgHom L K).toLinearMap

lemma tauL_pow_apply (s : ℕ) (u : K) : (tauL L K ^ s) u = ((frobeniusAlgHom L K) ^ s) u := by
  induction s generalizing u with
  | zero => simp
  | succ s ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, AlgHom.mul_apply]; rfl

lemma lagrangeResolvent_smul (ξ : Ω) (a : L) (u : K) :
    lagrangeResolvent (L := L) ξ (a • u) = algebraMap L Ω a * lagrangeResolvent (L := L) ξ u := by
  rw [map_smul, Algebra.smul_def]

/-- `R_ξ(f(τ) u) = f(ξ) R_ξ(u)` for `ξ^M = 1`. -/
lemma lagrangeResolvent_aeval {ξ : Ω} (hξ : ξ ^ finrank L K = 1) (f : L[X]) (u : K) :
    lagrangeResolvent (L := L) ξ (aeval (tauL L K) f u) = aeval ξ f * lagrangeResolvent (L := L) ξ u := by
  induction f using Polynomial.induction_on generalizing u with
  | C a =>
    rw [aeval_C, aeval_C, Module.algebraMap_end_apply, lagrangeResolvent_smul]
  | add p r hp hr =>
    rw [map_add, LinearMap.add_apply, map_add, hp, hr, map_add, add_mul]
  | monomial k a ih =>
    have e1 : aeval (tauL L K) (C a * X ^ (k + 1)) u =
        aeval (tauL L K) (C a * X ^ k) (frobeniusAlgHom L K u) := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]; rfl
    rw [e1, ih, lagrangeResolvent_frob hξ]
    simp only [map_mul, map_pow, aeval_X, aeval_C]; ring

/-- Dedekind: the Lagrange resolvent is not identically zero. -/
lemma exists_lagrangeResolvent_ne_zero (ξ : Ω) : ∃ u : K, lagrangeResolvent (L := L) ξ u ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  let φ : Fin (finrank L K) → (K →* Ω) := fun s =>
    (algebraMap K Ω : K →* Ω).comp (((frobeniusAlgHom L K) ^ (s : ℕ) : K →ₐ[L] K) : K →* K)
  have hφinj : Function.Injective φ := by
    intro s s' h
    apply (bijective_frobeniusAlgHom_pow L K).1
    ext x
    have := DFunLike.congr_fun h x
    simp only [φ, MonoidHom.comp_apply] at this
    exact (algebraMap K Ω).injective this
  have hli := (linearIndependent_monoidHom K Ω).comp φ hφinj
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (fun s => ξ⁻¹ ^ (s : ℕ)) (by
    funext u
    have := hall u
    rw [lagrangeResolvent_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this, ← Fin.sum_univ_eq_sum_range (fun s => ξ⁻¹ ^ s * algebraMap K Ω (((frobeniusAlgHom L K) ^ s) u))]
    rfl) ⟨0, Module.finrank_pos⟩
  simp at h0

/-- The normal basis theorem, in Frobenius form. -/
lemma exists_normal_frob :
    ∃ w₀ : K, LinearIndependent L (fun i : Fin (finrank L K) => ((frobeniusAlgHom L K) ^ (i : ℕ)) w₀) := by
  let nb := IsGalois.normalBasis L K
  have hw₀ : LinearIndependent L (fun σ : Gal(K/L) => σ (nb 1)) := by
    have := nb.linearIndependent
    convert this using 1
    funext σ
    exact (IsGalois.normalBasis_apply σ).symm
  refine ⟨nb 1, ?_⟩
  have hb := bijective_frobeniusAlgEquivOfAlgebraic_pow L K
  have := hw₀.comp _ hb.1
  convert this using 1
  funext i
  simp only [Function.comp_apply]
  rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate, frob_pow_apply]


/-- `τ^M = 1` as linear maps. -/
lemma tauL_pow_finrank : tauL L K ^ finrank L K = 1 := by
  ext u; rw [tauL_pow_apply, frob_pow_finrank]; rfl

/-- The polynomial `X^M - 1`. -/
noncomputable abbrev polyP (L K : Type*) [Field L] [Field K] [Algebra L K] : L[X] :=
  X ^ finrank L K - C 1

lemma polyP_monic : (polyP L K).Monic := monic_X_pow_sub_C 1 Module.finrank_pos.ne'

lemma natDegree_polyP : (polyP L K).natDegree = finrank L K := natDegree_X_pow_sub_C

lemma polyP_ne_one : polyP L K ≠ 1 := by
  intro h
  have := congrArg natDegree h
  rw [natDegree_X_pow_sub_C, natDegree_one] at this
  exact Module.finrank_pos.ne' this

lemma aeval_polyP : aeval (tauL L K) (polyP L K) = 0 := by
  simp [polyP, tauL_pow_finrank]

lemma aeval_modByMonic (f : L[X]) (w : K) :
    aeval (tauL L K) (f %ₘ polyP L K) w = aeval (tauL L K) f w := by
  conv_rhs => rw [← modByMonic_add_div f (polyP L K)]
  rw [map_add, map_mul, aeval_polyP, zero_mul, add_zero]

lemma aeval_eq_sum_fin (f : L[X]) (hf : f.natDegree < finrank L K) (w : K) :
    aeval (tauL L K) f w = ∑ i : Fin (finrank L K), f.coeff i • ((frobeniusAlgHom L K) ^ (i : ℕ)) w := by
  rw [aeval_eq_sum_range' hf, LinearMap.sum_apply,
    ← Fin.sum_univ_eq_sum_range (fun i => (f.coeff i • tauL L K ^ i) w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, tauL_pow_apply]

/-- `f ↦ ∑ c_i X^i` -/
noncomputable def polyOf (c : Fin (finrank L K) → L) : L[X] := ∑ i, C (c i) * X ^ (i : ℕ)

lemma aeval_polyOf (c : Fin (finrank L K) → L) (w : K) :
    aeval (tauL L K) (polyOf c) w = ∑ i, c i • ((frobeniusAlgHom L K) ^ (i : ℕ)) w := by
  simp only [polyOf, map_sum, map_mul, aeval_C, map_pow, aeval_X, LinearMap.sum_apply,
    Module.End.mul_apply, Module.algebraMap_end_apply, tauL_pow_apply]

lemma aeval_mem_span (f : L[X]) (w : K) :
    aeval (tauL L K) f w ∈
      Submodule.span L (Set.range fun i : Fin (finrank L K) => ((frobeniusAlgHom L K) ^ (i : ℕ)) w) := by
  rw [← aeval_modByMonic, aeval_eq_sum_fin _ ((natDegree_modByMonic_lt f polyP_monic polyP_ne_one).trans_eq natDegree_polyP)]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma exists_polyOf_of_mem_span {w v : K}
    (hv : v ∈ Submodule.span L (Set.range fun i : Fin (finrank L K) => ((frobeniusAlgHom L K) ^ (i : ℕ)) w)) :
    ∃ f : L[X], aeval (tauL L K) f w = v := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, hc⟩ := hv
  exact ⟨polyOf c, by rw [aeval_polyOf, hc]⟩

section NormalGen

variable {w₀ : K}
  (hw₀ : LinearIndependent L (fun i : Fin (finrank L K) => ((frobeniusAlgHom L K) ^ (i : ℕ)) w₀))
include hw₀

lemma span_normalGen :
    Submodule.span L (Set.range fun i : Fin (finrank L K) => ((frobeniusAlgHom L K) ^ (i : ℕ)) w₀) = ⊤ :=
  hw₀.span_eq_top_of_card_eq_finrank' (by simp)

lemma exists_aeval_eq (v : K) : ∃ f : L[X], aeval (tauL L K) f w₀ = v :=
  exists_polyOf_of_mem_span ((span_normalGen hw₀).symm ▸ Submodule.mem_top)

lemma polyP_dvd_of_aeval_eq_zero {f : L[X]} (hf : aeval (tauL L K) f w₀ = 0) : polyP L K ∣ f := by
  rw [← modByMonic_eq_zero_iff_dvd polyP_monic]
  set r := f %ₘ polyP L K with hr
  have hdeg : r.natDegree < finrank L K := (natDegree_modByMonic_lt f polyP_monic polyP_ne_one).trans_eq natDegree_polyP
  have h0 : aeval (tauL L K) r w₀ = 0 := by rw [hr, aeval_modByMonic, hf]
  rw [aeval_eq_sum_fin r hdeg] at h0
  have hc := Fintype.linearIndependent_iff.1 hw₀ (fun i => r.coeff i) h0
  ext i
  rw [coeff_zero]
  by_cases hi : i < finrank L K
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- `w = g(τ) w₀` generates iff `g` is coprime to `X^M - 1`. -/
lemma span_eq_top_iff_isCoprime (g : L[X]) :
    Submodule.span L (Set.range fun i : Fin (finrank L K) =>
        ((frobeniusAlgHom L K) ^ (i : ℕ)) (aeval (tauL L K) g w₀)) = ⊤ ↔
      IsCoprime g (polyP L K) := by
  constructor
  · intro h
    have hmem : w₀ ∈ Submodule.span L (Set.range fun i : Fin (finrank L K) =>
        ((frobeniusAlgHom L K) ^ (i : ℕ)) (aeval (tauL L K) g w₀)) := h ▸ Submodule.mem_top
    obtain ⟨f, hf⟩ := exists_polyOf_of_mem_span hmem
    have h1 : aeval (tauL L K) (f * g - 1) w₀ = 0 := by
      rw [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply, hf, map_one,
        Module.End.one_apply, sub_self]
    obtain ⟨k, hk⟩ := polyP_dvd_of_aeval_eq_zero hw₀ h1
    exact ⟨f, -k, by linear_combination hk⟩
  · rintro ⟨a, b, hab⟩
    rw [eq_top_iff]
    intro v _
    obtain ⟨h, rfl⟩ := exists_aeval_eq hw₀ v
    have : aeval (tauL L K) h w₀ = aeval (tauL L K) (h * a) (aeval (tauL L K) g w₀) := by
      have e : h = h * a * g + h * b * polyP L K := by linear_combination -h * hab
      conv_lhs => rw [e]
      rw [map_add, LinearMap.add_apply, map_mul (aeval _) (h * b), aeval_polyP, mul_zero,
        LinearMap.zero_apply, add_zero, map_mul, Module.End.mul_apply]
    rw [this]
    exact aeval_mem_span _ _

lemma lagrangeResolvent_normalGen_ne_zero (ξ : Ω) (hξ : ξ ^ finrank L K = 1) :
    lagrangeResolvent (L := L) ξ w₀ ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_lagrangeResolvent_ne_zero (L := L) (K := K) ξ
  obtain ⟨h, rfl⟩ := exists_aeval_eq hw₀ u
  rw [lagrangeResolvent_aeval hξ] at hu
  exact right_ne_zero_of_mul hu

end NormalGen


lemma range_galois_orbit (w : K) :
    Set.range (fun σ : Gal(K/L) => σ w) =
      Set.range fun i : Fin (finrank L K) => ((frobeniusAlgHom L K) ^ (i : ℕ)) w := by
  have hb := bijective_frobeniusAlgEquivOfAlgebraic_pow L K
  have e : ∀ i : Fin (finrank L K),
      (frobeniusAlgEquivOfAlgebraic L K ^ (i : ℕ)) w = ((frobeniusAlgHom L K) ^ (i : ℕ)) w := by
    intro i
    rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate, frob_pow_apply]
  ext x; constructor
  · rintro ⟨σ, rfl⟩
    obtain ⟨i, rfl⟩ := hb.2 σ
    exact ⟨i, (e i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, e i⟩

lemma isNormalElem_iff_span (w : K) :
    IsNormalElem L K w ↔
      Submodule.span L (Set.range fun i : Fin (finrank L K) => ((frobeniusAlgHom L K) ^ (i : ℕ)) w) = ⊤ := by
  unfold IsNormalElem
  rw [range_galois_orbit]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [range_galois_orbit, h]
  · rw [Fintype.card_eq_nat_card]; exact IsGalois.card_aut_eq_finrank L K

lemma pow_finrank_eq_one_of_pow_pfree {ξ : Ω} (hξ : ξ ^ pfree (ringChar L) (finrank L K) = 1) :
    ξ ^ finrank L K = 1 := by
  obtain ⟨k, hk⟩ := pfree_dvd (ringChar L) (finrank L K)
  rw [hk, pow_mul, hξ, one_pow]

lemma isCoprime_polyP_iff (hμ : ∃ ζ : Ω, IsPrimitiveRoot ζ (pfree (ringChar L) (finrank L K)))
    (g : L[X]) :
    IsCoprime g (polyP L K) ↔
      ∀ ξ : Ω, ξ ^ pfree (ringChar L) (finrank L K) = 1 → aeval ξ g ≠ 0 := by
  classical
  constructor
  · rintro ⟨a, b, hab⟩ ξ hξ hg
    have h1 := congrArg (aeval ξ) hab
    have hP : aeval ξ (polyP L K) = 0 := by
      simp only [polyP, map_sub, map_pow, aeval_X, map_one]
      rw [pow_finrank_eq_one_of_pow_pfree hξ, sub_self]
    rw [map_add, map_mul, map_mul, hg, hP, mul_zero, mul_zero, add_zero, map_one] at h1
    exact zero_ne_one h1
  · intro h
    obtain ⟨ζ, hζ⟩ := hμ
    set p := ringChar L with hpdef
    set M := finrank L K
    have hpM : p ^ M.factorization p * pfree p M = M := pow_mul_pfree p M
    have hM'pos : 0 < pfree p M := pfree_pos p Module.finrank_pos.ne'
    have : CharP L p := ringChar.charP L
    have hp : p.Prime := CharP.char_is_prime L p
    have := Fact.mk hp
    have : CharP Ω p := charP_of_injective_algebraMap (algebraMap L Ω).injective p
    rw [← isRelPrime_iff_isCoprime]
    intro d hdg hdP
    by_contra hdu
    have hPne : polyP L K ≠ 0 := polyP_monic.ne_zero
    have hd0 : d ≠ 0 := by rintro rfl; exact hPne (zero_dvd_iff.1 hdP)
    have hdΩu : ¬ IsUnit (d.map (algebraMap L Ω)) := by
      rw [Polynomial.isUnit_iff_degree_eq_zero, degree_map, ← Polynomial.isUnit_iff_degree_eq_zero]
      exact hdu
    have hdΩ0 : d.map (algebraMap L Ω) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap L Ω).injective).2 hd0
    obtain ⟨ρ, hρirr, hρd⟩ := WfDvdMonoid.exists_irreducible_factor hdΩu hdΩ0
    have hPΩ : (polyP L K).map (algebraMap L Ω) =
        ∏ ξ ∈ nthRootsFinset (pfree p M) (1 : Ω), (X - C ξ) ^ (p ^ M.factorization p) := by
      rw [Finset.prod_pow, ← X_pow_sub_one_eq_prod hM'pos hζ, sub_pow_char_pow, ← pow_mul,
        mul_comm, hpM, one_pow]
      simp [polyP, M]
    have hρP : ρ ∣ ∏ ξ ∈ nthRootsFinset (pfree p M) (1 : Ω), (X - C ξ) ^ (p ^ M.factorization p) :=
      hPΩ ▸ hρd.trans (Polynomial.map_dvd _ hdP)
    obtain ⟨ξ, hξmem, hξ⟩ := (hρirr.prime.dvd_finsetProd_iff _).1 hρP
    have hρξ : ρ ∣ X - C ξ := hρirr.prime.dvd_of_dvd_pow hξ
    have hXρ : X - C ξ ∣ ρ := hρirr.dvd_symm (irreducible_X_sub_C ξ) hρξ
    have hroot : (g.map (algebraMap L Ω)).IsRoot ξ :=
      dvd_iff_isRoot.1 (hXρ.trans (hρd.trans (Polynomial.map_dvd _ hdg)))
    apply h ξ ((mem_nthRootsFinset hM'pos 1).1 hξmem)
    rw [IsRoot, eval_map, ← aeval_def] at hroot
    exact hroot

/-- **Lemma 2.1** (classical), first part. Let `M = [K:L]` (the paper's `m`) and `M'` its `p`-free part, and
assume `Ω` contains a primitive `M'`-th root of unity. Then `w` is normal over `L` iff
`R_ξ(w) ≠ 0` for every `ξ ∈ μ_{M'}`. -/
theorem normal_iff_resolvent_ne_zero
    (hμ : ∃ ζ : Ω, IsPrimitiveRoot ζ (pfree (ringChar L) (finrank L K))) (w : K) :
    IsNormalElem L K w ↔
      ∀ ξ : Ω, ξ ^ pfree (ringChar L) (finrank L K) = 1 → lagrangeResolvent (L := L) ξ w ≠ 0 := by
  obtain ⟨w₀, hw₀⟩ := exists_normal_frob (L := L) (K := K)
  obtain ⟨g, rfl⟩ := exists_aeval_eq hw₀ w
  rw [isNormalElem_iff_span, span_eq_top_iff_isCoprime hw₀, isCoprime_polyP_iff hμ]
  refine forall_congr' fun ξ => imp_congr_right fun hξ => ?_
  have hξM := pow_finrank_eq_one_of_pow_pfree hξ
  rw [lagrangeResolvent_aeval hξM, mul_ne_zero_iff,
    and_iff_left (lagrangeResolvent_normalGen_ne_zero hw₀ ξ hξM)]


/-- **Lemma 2.1**, second part: `{w : R_ξ(w) = 0} = g_ξ(τ) K` (`τ = σ_Q`), `g_ξ` the minimal polynomial of `ξ`
over `L`. -/
theorem ker_lagrangeResolvent (ξ : Ω) (hξ : ξ ^ pfree (ringChar L) (finrank L K) = 1) :
    LinearMap.ker (lagrangeResolvent (L := L) (K := K) ξ) =
      LinearMap.range (Polynomial.aeval (frobeniusAlgHom L K).toLinearMap (minpoly L ξ)) := by
  obtain ⟨w₀, hw₀⟩ := exists_normal_frob (L := L) (K := K)
  have hξM := pow_finrank_eq_one_of_pow_pfree hξ
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hw
    obtain ⟨g, rfl⟩ := exists_aeval_eq hw₀ w
    rw [lagrangeResolvent_aeval hξM] at hw
    have hg : aeval ξ g = 0 :=
      (mul_eq_zero.1 hw).resolve_right (lagrangeResolvent_normalGen_ne_zero hw₀ ξ hξM)
    obtain ⟨k, rfl⟩ := minpoly.dvd L ξ hg
    exact ⟨aeval (tauL L K) k w₀, by rw [map_mul, Module.End.mul_apply]⟩
  · rintro ⟨u, rfl⟩
    rw [lagrangeResolvent_aeval hξM, minpoly.aeval, zero_mul]


lemma tauL_pow_aeval_comm (i : ℕ) (g : L[X]) (u : K) :
    ((frobeniusAlgHom L K) ^ i) (aeval (tauL L K) g u) = aeval (tauL L K) g (((frobeniusAlgHom L K) ^ i) u) := by
  have e : tauL L K ^ i = aeval (tauL L K) (X ^ i : L[X]) := by simp
  rw [← tauL_pow_apply, ← tauL_pow_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, e,
    ← map_mul, ← map_mul, mul_comm]

lemma aeval_aeval (f g : L[X]) (u : K) :
    aeval (tauL L K) f (aeval (tauL L K) g u) = aeval (tauL L K) (f * g) u := by
  rw [map_mul, Module.End.mul_apply]

lemma coeff_sum_fin {m : ℕ} (c : Fin m → L) (j : ℕ) :
    (∑ i : Fin m, C (c i) * X ^ (i : ℕ)).coeff j = if h : j < m then c ⟨j, h⟩ else 0 := by
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      rw [ite_eq_right]
      intro hjb; exact hb (Fin.ext hjb.symm)
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    intro hji; exact h (hji ▸ i.2)

lemma aeval_sum_fin {m : ℕ} (c : Fin m → L) (u : K) :
    aeval (tauL L K) (∑ i : Fin m, C (c i) * X ^ (i : ℕ)) u =
      ∑ i : Fin m, c i • ((frobeniusAlgHom L K) ^ (i : ℕ)) u := by
  simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X, LinearMap.sum_apply,
    Module.End.mul_apply, Module.algebraMap_end_apply, tauL_pow_apply]

/-- `dim_L g(τ) K = M - deg g` for a monic divisor `g` of `X^M - 1`. -/
lemma finrank_range_aeval {g : L[X]} (hg : g.Monic) (hdvd : g ∣ polyP L K) :
    finrank L (LinearMap.range (aeval (tauL L K) g)) = finrank L K - g.natDegree := by
  classical
  obtain ⟨w₀, hw₀⟩ := exists_normal_frob (L := L) (K := K)
  obtain ⟨h, hh⟩ := hdvd
  have hPm := polyP_monic (L := L) (K := K)
  have hhm : h.Monic := hg.of_mul_monic_left (hh ▸ hPm)
  have hdeg : h.natDegree = finrank L K - g.natDegree := by
    have := congrArg natDegree hh
    rw [natDegree_polyP, hg.natDegree_mul hhm] at this
    omega
  rw [← hdeg]
  set m := h.natDegree
  let b : Fin m → K := fun i => ((frobeniusAlgHom L K) ^ (i : ℕ)) (aeval (tauL L K) g w₀)
  have hspan : Submodule.span L (Set.range b) = LinearMap.range (aeval (tauL L K) g) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (tauL_pow_aeval_comm _ _ _).symm⟩
    · rintro v ⟨u, rfl⟩
      obtain ⟨f, rfl⟩ := exists_aeval_eq hw₀ u
      rw [aeval_aeval]
      have hf : g * f = g * (f %ₘ h) + polyP L K * (f /ₘ h) := by
        conv_lhs => rw [← modByMonic_add_div f h]
        rw [hh]; ring
      rw [hf, map_add, LinearMap.add_apply, map_mul (aeval _) (polyP L K), aeval_polyP, zero_mul,
        LinearMap.zero_apply, add_zero, mul_comm, ← aeval_aeval]
      set r := f %ₘ h
      rcases eq_or_ne h 1 with h1 | h1
      · have : r = 0 := by simp [r, h1]
        rw [this, map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
      have hr : r.natDegree < m := natDegree_modByMonic_lt f hhm h1
      rw [aeval_eq_sum_range' hr, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i hi => ?_
      rw [LinearMap.smul_apply, tauL_pow_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩)
  have hli : LinearIndependent L b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set cp : L[X] := ∑ i : Fin m, C (c i) * X ^ (i : ℕ)
    have h1 : aeval (tauL L K) (cp * g) w₀ = 0 := by
      rw [← aeval_aeval, aeval_sum_fin]
      exact hc
    obtain ⟨k, hk⟩ := polyP_dvd_of_aeval_eq_zero hw₀ h1
    have h2 : h ∣ cp := by
      have : g * cp = g * (h * k) := by rw [mul_comm g cp, hk, hh, mul_assoc]
      exact ⟨k, mul_left_cancel₀ hg.ne_zero this⟩
    have h3 : cp = 0 := by
      apply eq_zero_of_dvd_of_degree_lt h2
      rw [degree_eq_natDegree hhm.ne_zero]
      exact degree_sum_fin_lt _
    intro i
    have := congrArg (fun p => p.coeff i) h3
    simp only [cp, coeff_sum_fin, dite_eq_left i.2, coeff_zero] at this
    exact this
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]


lemma natCast_pow_eq_one_iff {o Q D : ℕ} (hQ : 1 ≤ Q) :
    ((Q : ZMod o)) ^ D = 1 ↔ o ∣ Q ^ D - 1 := by
  rw [← Nat.cast_pow, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hQ),
    Nat.cast_one, sub_eq_zero]

lemma pow_pow_eq_self_iff {Ω : Type*} [Field Ω] {ξ : Ω} (hξ0 : ξ ≠ 0) {Q D : ℕ} (hQ : 1 ≤ Q) :
    ξ ^ Q ^ D = ξ ↔ ((Q : ZMod (orderOf ξ))) ^ D = 1 := by
  rw [natCast_pow_eq_one_iff hQ, orderOf_dvd_iff_pow_eq_one]
  have h1 : 1 ≤ Q ^ D := Nat.one_le_pow _ _ hQ
  constructor
  · intro h
    rw [pow_sub₀ _ hξ0 h1, h, pow_one, mul_inv_cancel₀ hξ0]
  · intro h
    have : ξ ^ Q ^ D = ξ ^ (Q ^ D - 1) * ξ := by rw [← pow_succ, Nat.sub_add_cancel h1]
    rw [this, h, one_mul]

/-- The degree of the minimal polynomial of a root of unity over a finite field `L` is the order of
`|L|` modulo the order of the root of unity. -/
lemma natDegree_minpoly_eq_orderOf {Ω : Type*} [Field Ω] [Algebra L Ω] {ξ : Ω} {e : ℕ}
    (hξ : ξ ^ e = 1) (he : 0 < e) :
    (minpoly L ξ).natDegree = orderOf ((Fintype.card L : ZMod (orderOf ξ))) := by
  classical
  have hξ0 : ξ ≠ 0 := by rintro rfl; rw [zero_pow he.ne'] at hξ; exact zero_ne_one hξ
  have hint : IsIntegral L ξ := IsIntegral.of_pow he (by rw [hξ]; exact isIntegral_one)
  set Kx := IntermediateField.adjoin L {ξ}
  have hD : finrank L Kx = (minpoly L ξ).natDegree := IntermediateField.adjoin.finrank hint
  have : FiniteDimensional L Kx := IntermediateField.adjoin.finiteDimensional hint
  have : Finite Kx := Module.finite_of_finite L
  have : Fintype Kx := Fintype.ofFinite Kx
  have hQ : 1 ≤ Fintype.card L := Fintype.card_pos
  have hcard : Fintype.card Kx = Fintype.card L ^ finrank L Kx := Module.card_eq_pow_finrank
  have hmem : ξ ∈ Kx := IntermediateField.mem_adjoin_simple_self L ξ
  rw [← hD]
  apply Nat.dvd_antisymm
  · -- `D ∣ k`
    set k := orderOf ((Fintype.card L : ZMod (orderOf ξ)))
    have hk : ξ ^ Fintype.card L ^ k = ξ := (pow_pow_eq_self_iff hξ0 hQ).2 (pow_orderOf_eq_one _)
    have hφ : (frobeniusAlgHom L Kx) ^ k = 1 := by
      apply IntermediateField.algHom_ext_of_eq_adjoin L (S := Kx) (s := {ξ}) rfl
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [frob_pow_apply, AlgHom.one_apply]
      exact Subtype.ext (by simp [hk])
    rw [← orderOf_frobeniusAlgHom L Kx]
    exact orderOf_dvd_of_pow_eq_one hφ
  · -- `k ∣ D`
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_pow_eq_self_iff hξ0 hQ, ← hcard]
    have := FiniteField.pow_card (⟨ξ, hmem⟩ : Kx)
    exact congrArg Subtype.val this

/-- `dim_L ker R_ξ = M - ord_{ord ξ}(|L|)`. -/
lemma finrank_ker_lagrangeResolvent {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower L K Ω] (ξ : Ω) (hξ : ξ ^ pfree (ringChar L) (finrank L K) = 1) :
    finrank L (LinearMap.ker (lagrangeResolvent (L := L) (K := K) ξ)) =
      finrank L K - orderOf ((Fintype.card L : ZMod (orderOf ξ))) := by
  have hM' : 0 < pfree (ringChar L) (finrank L K) := pfree_pos _ Module.finrank_pos.ne'
  have hint : IsIntegral L ξ := IsIntegral.of_pow hM' (by rw [hξ]; exact isIntegral_one)
  rw [ker_lagrangeResolvent ξ hξ, ← natDegree_minpoly_eq_orderOf hξ hM']
  apply finrank_range_aeval (minpoly.monic hint)
  apply minpoly.dvd
  simp only [polyP, map_sub, map_pow, aeval_X, map_one]
  rw [pow_finrank_eq_one_of_pow_pfree hξ, sub_self]

end Classical

/-! ### The main setting -/

section Setting

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
variable {Ω : Type*} [Field Ω] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]

local notation "q" => Fintype.card F
local notation "n" => Module.finrank F E

instance finrank_neZero : NeZero (finrank F E) := ⟨Module.finrank_pos.ne'⟩

/-- **Definition 2.2**: the partial resolvent
`F_η(w)(u) = ∑_{t ∈ ℤ/n, t ≡ u (mod p^a)} η^{-t} σ^t(w)`. -/
noncomputable def resolvent (η : Ω) (u : ZMod (Model.pa q n)) : E →ₗ[F] Ω :=
  ∑ t ∈ (range n).filter (fun t : ℕ => (t : ZMod (Model.pa q n)) = u),
    (η⁻¹ ^ t) • ((IsScalarTower.toAlgHom F E Ω).toLinearMap ∘ₗ
      ((frobeniusAlgHom F E) ^ t).toLinearMap)

/-- **Definition 2.4**: the fibre sum `C_{d,k}(w) = ∑_{t ∈ ℤ/d'} ∑_{u ∈ p^c ℤ/p^a} F_{ζ^{k+tN}}(w)(u)`,
written with the target `x = d' k`: the `η = ζ^i` occurring are those with `d' i = x`. -/
noncomputable def fibreSum (ζ : Ω) (d : ℕ) (x : ZMod (Model.nfree q n)) : E →ₗ[F] Ω :=
  ∑ i ∈ univ.filter (fun i : ZMod (Model.nfree q n) => ((Model.dfree q d : ℕ) : ZMod _) * i = x),
    ∑ u ∈ Model.resSet q n d, resolvent (ζ ^ i.val) u

/-- The kernel `V_C = {w : C(w) = 0}` of a condition `C` (the same for all targets of the orbit,
see `condKer_eq`). -/
noncomputable def condKer (ζ : Ω) (C : Model.Cond q n) : Submodule F E :=
  ⨅ x ∈ C.2, LinearMap.ker (fibreSum (F := F) (E := E) ζ C.1 x)

/-- The intermediate field `𝔽_{q^d}` of `E/F`: the fixed field of `σ^d`. -/
noncomputable def levelField (d : ℕ) : IntermediateField F E :=
  IntermediateField.fixedField (Subgroup.zpowers ((frobeniusAlgEquivOfAlgebraic F E) ^ d))

lemma frobEquiv_pow_apply (d : ℕ) (x : E) :
    ((frobeniusAlgEquivOfAlgebraic F E) ^ d) x = x ^ q ^ d := by
  rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]

lemma mem_levelField {d : ℕ} {x : E} : x ∈ levelField (F := F) (E := E) d ↔ x ^ q ^ d = x := by
  unfold levelField
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    have := h _ (Subgroup.mem_zpowers _)
    rwa [frobEquiv_pow_apply] at this
  · intro h f hf
    have hg : (frobeniusAlgEquivOfAlgebraic F E) ^ d ∈ MulAction.stabilizer Gal(E/F) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, frobEquiv_pow_apply, h]
    have := (Subgroup.zpowers_le.2 hg) hf
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this

lemma finrank_levelField_top {d : ℕ} (hd : d ∣ n) :
    finrank (levelField (F := F) (E := E) d) E = n / d := by
  unfold levelField
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers,
    orderOf_pow' _ (by rintro rfl; simp at hd; exact Module.finrank_pos.ne' hd),
    orderOf_frobeniusAlgEquivOfAlgebraic, Nat.gcd_eq_right hd]

/-- `[𝔽_{q^d} : F] = d` for `d ∣ n`. -/
theorem finrank_levelField {d : ℕ} (hd : d ∣ n) : finrank F (levelField (F := F) (E := E) d) = d := by
  have h := Module.finrank_mul_finrank F (levelField (F := F) (E := E) d) E
  rw [finrank_levelField_top hd] at h
  have hn : 0 < n := Module.finrank_pos
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hd) hd0
  have : finrank F (levelField (F := F) (E := E) d) * (n / d) = d * (n / d) := by
    rw [h, Nat.mul_div_cancel' hd]
  exact Nat.eq_of_mul_eq_mul_right hnd this

/-- Every intermediate field of `E/F` is `𝔽_{q^d}` for `d = [K : F]`, a divisor of `n`. -/
theorem intermediateField_eq_levelField (K : IntermediateField F E) :
    finrank F K ∣ n ∧ K = levelField (finrank F K) := by
  have hdvd : finrank F K ∣ n := ⟨_, (Module.finrank_mul_finrank F K E).symm⟩
  refine ⟨hdvd, ?_⟩
  apply IntermediateField.eq_of_le_of_finrank_eq
  · intro x hx
    rw [mem_levelField]
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = q ^ finrank F K := Module.card_eq_pow_finrank
    have := FiniteField.pow_card (⟨x, hx⟩ : K)
    rw [hcard] at this
    exact congrArg Subtype.val this
  · rw [finrank_levelField hdvd]

/-- Complete normality means normality over `𝔽_{q^d}` for every `d ∣ n`. -/
theorem isCompletelyNormal_iff_levelField (w : E) :
    IsCompletelyNormal F E w ↔ ∀ d ∈ (finrank F E).divisors, IsNormalElem (levelField (F := F) (E := E) d) E w := by
  constructor
  · intro h d _
    exact h _
  · intro h K
    obtain ⟨hdvd, hK⟩ := intermediateField_eq_levelField K
    set e := finrank F K with he
    clear_value e
    subst hK
    exact h e (Nat.mem_divisors.2 ⟨hdvd, Module.finrank_pos.ne'⟩)


lemma chr_eq_ringChar : Model.chr q = ringChar F := by
  obtain ⟨k, hp, hk⟩ := FiniteField.card F (ringChar F)
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have h1 : Model.chr q ∣ ringChar F ^ (k : ℕ) := by rw [← hk]; exact Nat.minFac_dvd _
  exact (Nat.prime_dvd_prime_iff_eq (Model.chr_prime hq) hp).1 ((Model.chr_prime hq).dvd_of_dvd_pow h1)

lemma ringChar_intermediateField (K : IntermediateField F E) : ringChar K = ringChar F := by
  have : CharP F (ringChar F) := ringChar.charP F
  have : CharP K (ringChar F) := charP_of_injective_algebraMap (algebraMap F K).injective _
  exact ringChar.eq K _

lemma pfree_div {p a b : ℕ} (h : b ∣ a) : pfree p (a / b) = pfree p a / pfree p b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [pfree_zero]
  obtain ⟨c, rfl⟩ := h
  rw [Nat.mul_div_cancel_left _ hb, pfree_mul]
  rcases Nat.eq_zero_or_pos (pfree p b) with h0 | h0
  · exact absurd h0 (pfree_pos p hb.ne').ne'
  rw [Nat.mul_div_cancel_left _ h0]

/-- The resolvent at level `d`: `R^{(d)}_ξ(w) = ∑_{s < n/d} ξ^{-s} σ^{ds}(w)`. -/
noncomputable def levelRes (d : ℕ) (ξ : Ω) (w : E) : Ω :=
  ∑ s ∈ range (n / d), ξ⁻¹ ^ s * algebraMap E Ω (((frobeniusAlgHom F E) ^ (d * s)) w)

/-- **Lemma 2.1** at level `d`. -/
theorem normal_level_iff {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ} (hd : d ∣ n)
    (w : E) :
    IsNormalElem (levelField (F := F) (E := E) d) E w ↔
      ∀ ξ : Ω, ξ ^ Model.bigN q n d = 1 → levelRes (F := F) d ξ w ≠ 0 := by
  classical
  set L := levelField (F := F) (E := E) d
  have : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card L = q ^ d := by
    rw [Module.card_eq_pow_finrank (K := F), finrank_levelField hd]
  have hrank : finrank L E = n / d := finrank_levelField_top hd
  have hN : pfree (ringChar L) (finrank L E) = Model.bigN q n d := by
    rw [ringChar_intermediateField, hrank, ← chr_eq_ringChar, pfree_div hd]
    rfl
  have hμ : ∃ ζ' : Ω, IsPrimitiveRoot ζ' (pfree (ringChar L) (finrank L E)) := by
    refine ⟨ζ ^ Model.dfree q d, ?_⟩
    rw [hN]
    exact hζ.pow (Nat.pos_of_ne_zero (NeZero.ne _)) (Model.dfree_mul_bigN hd).symm
  rw [normal_iff_resolvent_ne_zero hμ w, hN]
  refine forall_congr' fun ξ => imp_congr_right fun _ => ?_
  rw [lagrangeResolvent_apply, hrank]
  unfold levelRes
  have : ∀ s, ((frobeniusAlgHom L E) ^ s) w = ((frobeniusAlgHom F E) ^ (d * s)) w := by
    intro s
    rw [frob_pow_apply, frob_pow_apply, hcardL, pow_mul]
  simp_rw [this]


lemma resolvent_apply (η : Ω) (u : ZMod (Model.pa q n)) (w : E) :
    resolvent (F := F) η u w =
      ∑ t ∈ (range n).filter (fun t : ℕ => (t : ZMod (Model.pa q n)) = u),
        η⁻¹ ^ t * algebraMap E Ω (((frobeniusAlgHom F E) ^ t) w) := by
  simp [resolvent, LinearMap.sum_apply]

lemma pow_eq_pow_of_cast_eq {m : ℕ} {ζ : Ω} (hζ : ζ ^ m = 1) {a b : ℕ}
    (h : (a : ZMod m) = (b : ZMod m)) : ζ ^ a = ζ ^ b := by
  have := (ZMod.natCast_eq_natCast_iff' a b m).1 h
  rw [← Nat.div_add_mod a m, ← Nat.div_add_mod b m, pow_add, pow_add, pow_mul, pow_mul, hζ,
    one_pow, one_pow, this]

lemma pow_val_add {m : ℕ} [NeZero m] {ζ : Ω} (hζ : ζ ^ m = 1) (a b : ZMod m) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add]
  exact pow_eq_pow_of_cast_eq hζ (by simp)

lemma pow_val_natCast {m : ℕ} [NeZero m] {ζ : Ω} (hζ : ζ ^ m = 1) (k : ℕ) :
    ζ ^ (k : ZMod m).val = ζ ^ k :=
  pow_eq_pow_of_cast_eq hζ (by simp)

lemma dval_le_a {d : ℕ} (hd : d ∣ n) : Model.dval q d ≤ Model.a q n := by
  have hn : n ≠ 0 := Module.finrank_pos.ne'
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.1 hd)
  exact (Nat.factorization_le_iff_dvd hd0 hn).2 hd _

lemma sum_resSet_resolvent {d : ℕ} (hd : d ∣ n) (η : Ω) (w : E) :
    ∑ u ∈ Model.resSet q n d, resolvent (F := F) η u w =
      ∑ t ∈ (range n).filter (fun t => Model.chr q ^ Model.dval q d ∣ t),
        η⁻¹ ^ t * algebraMap E Ω (((frobeniusAlgHom F E) ^ t) w) := by
  simp_rw [resolvent_apply]
  have hpc : Model.chr q ^ Model.dval q d ∣ Model.pa q n := pow_dvd_pow _ (dval_le_a hd)
  have key : ∀ t : ℕ, Model.chr q ^ Model.dval q d ∣ (t : ZMod (Model.pa q n)).val ↔
      Model.chr q ^ Model.dval q d ∣ t := by
    intro t; rw [ZMod.val_natCast]; exact Nat.dvd_mod_iff hpc
  rw [← Finset.sum_fiberwise_of_maps_to (t := Model.resSet q n d)
    (g := fun t : ℕ => (t : ZMod (Model.pa q n)))]
  · refine Finset.sum_congr rfl fun u hu => ?_
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ht, rfl⟩
      simp only [Model.resSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact ⟨⟨ht, (key t).1 hu⟩, rfl⟩
    · rintro ⟨⟨ht, _⟩, rfl⟩; exact ⟨ht, rfl⟩
  · intro t ht
    simp only [Finset.mem_filter] at ht
    simp only [Model.resSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (key t).2 ht.2

/-- Parametrisation of the fibre `{i : d' i = x}` by `j < d'`. -/
lemma fibre_eq_image {d : ℕ} (hd : d ∣ n) {x : ZMod (Model.nfree q n)} (hx : x ∈ Model.targets q n d) :
    univ.filter (fun i : ZMod (Model.nfree q n) => ((Model.dfree q d : ℕ) : ZMod _) * i = x) =
      (range (Model.dfree q d)).image
        (fun j : ℕ => ((x.val / Model.dfree q d : ℕ) : ZMod (Model.nfree q n)) +
          ((Model.bigN q n d : ℕ) : ZMod _) * (j : ZMod _)) := by
  have hNd : Model.bigN q n d * Model.dfree q d = Model.nfree q n := Model.bigN_mul_dfree hd
  have hd0 : d ≠ 0 := by rintro rfl; exact Module.finrank_pos.ne' (zero_dvd_iff.1 hd)
  have hd'0 : 0 < Model.dfree q d := Model.dfree_pos hd0
  have hN0 : 0 < Model.bigN q n d := Model.bigN_pos hd
  have hdx : Model.dfree q d ∣ x.val := by
    rw [Model.mem_targets] at hx
    have h1 : Model.nfree q n ∣ Model.bigN q n d * x.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast; rw [ZMod.natCast_zmod_val]; exact hx
    exact Nat.dvd_of_mul_dvd_mul_left hN0 ((dvd_of_eq hNd).trans h1)
  have hi0 : ((Model.dfree q d : ℕ) : ZMod (Model.nfree q n)) *
      ((x.val / Model.dfree q d : ℕ) : ZMod (Model.nfree q n)) = x := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdx, ZMod.natCast_zmod_val]
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
  constructor
  · intro hi
    obtain ⟨v, hv⟩ : ∃ v : ℕ, v = (i - ((x.val / Model.dfree q d : ℕ) : ZMod (Model.nfree q n))).val :=
      ⟨_, rfl⟩
    have hvcast : ((v : ℕ) : ZMod (Model.nfree q n)) =
        i - ((x.val / Model.dfree q d : ℕ) : ZMod (Model.nfree q n)) := by
      rw [hv, ZMod.natCast_zmod_val]
    have hv0 : ((Model.dfree q d * v : ℕ) : ZMod (Model.nfree q n)) = 0 := by
      rw [Nat.cast_mul, hvcast, mul_sub, hi, hi0, sub_self]
    rw [ZMod.natCast_eq_zero_iff, ← hNd, mul_comm (Model.bigN q n d)] at hv0
    have hNv : Model.bigN q n d ∣ v := Nat.dvd_of_mul_dvd_mul_left hd'0 hv0
    obtain ⟨j, hj⟩ := hNv
    have hvlt : v < Model.bigN q n d * Model.dfree q d := by rw [hNd, hv]; exact ZMod.val_lt _
    refine ⟨j, ?_, ?_⟩
    · by_contra h
      push Not at h
      have : Model.bigN q n d * Model.dfree q d ≤ Model.bigN q n d * j := Nat.mul_le_mul_left _ h
      omega
    · rw [hj, Nat.cast_mul] at hvcast
      rw [hvcast]; ring
  · rintro ⟨j, _, rfl⟩
    rw [mul_add, hi0, ← mul_assoc, ← Nat.cast_mul, mul_comm (Model.dfree q d), hNd,
      ZMod.natCast_self, zero_mul, add_zero]

lemma fibre_param_injOn {d : ℕ} (hd : d ∣ n) (i0 : ZMod (Model.nfree q n)) :
    Set.InjOn (fun j : ℕ => i0 + ((Model.bigN q n d : ℕ) : ZMod (Model.nfree q n)) * (j : ZMod _))
      (range (Model.dfree q d) : Set ℕ) := by
  intro j hj j' hj' h
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  simp only [add_right_inj] at h
  rw [← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff', ← Model.bigN_mul_dfree hd,
    Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h
  exact Nat.eq_of_mul_eq_mul_left (Model.bigN_pos hd) h


lemma dvd_iff_chr_dfree {d t : ℕ} (hq : IsPrimePow q) (hd0 : d ≠ 0) :
    d ∣ t ↔ Model.chr q ^ Model.dval q d ∣ t ∧ Model.dfree q d ∣ t := by
  have hd : Model.chr q ^ Model.dval q d * Model.dfree q d = d := pow_mul_pfree _ _
  constructor
  · intro h
    exact ⟨(Dvd.intro _ hd).trans h, (Dvd.intro_left _ hd).trans h⟩
  · rintro ⟨h1, h2⟩
    rw [← hd]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((coprime_pfree (Model.chr_prime hq) hd0).pow_left _) h1 h2

/-- The inner sum over the fibre. -/
lemma fibre_inner_sum {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ} (hd : d ∣ n)
    {x : ZMod (Model.nfree q n)} (hx : x ∈ Model.targets q n d) (t : ℕ)
    (ht : Model.chr q ^ Model.dval q d ∣ t) :
    ∑ j ∈ range (Model.dfree q d),
        (ζ ^ (((x.val / Model.dfree q d : ℕ) : ZMod (Model.nfree q n)) +
          ((Model.bigN q n d : ℕ) : ZMod _) * (j : ZMod _)).val)⁻¹ ^ t =
      if d ∣ t then (Model.dfree q d : Ω) * ((ζ ^ (Model.chr q ^ Model.dval q d * x.val))⁻¹) ^ (t / d)
      else 0 := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hζ1 : ζ ^ Model.nfree q n = 1 := hζ.pow_eq_one
  have hNd : Model.bigN q n d * Model.dfree q d = Model.nfree q n := Model.bigN_mul_dfree hd
  have hd0 : d ≠ 0 := by rintro rfl; exact Module.finrank_pos.ne' (zero_dvd_iff.1 hd)
  have hd'0 : 0 < Model.dfree q d := Model.dfree_pos hd0
  have hN0 : 0 < Model.bigN q n d := Model.bigN_pos hd
  have hdx : Model.dfree q d ∣ x.val := by
    rw [Model.mem_targets] at hx
    have h1 : Model.nfree q n ∣ Model.bigN q n d * x.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast; rw [ZMod.natCast_zmod_val]; exact hx
    exact Nat.dvd_of_mul_dvd_mul_left hN0 ((dvd_of_eq hNd).trans h1)
  -- split the terms
  have hterm : ∀ j : ℕ, (ζ ^ (((x.val / Model.dfree q d : ℕ) : ZMod (Model.nfree q n)) +
          ((Model.bigN q n d : ℕ) : ZMod _) * (j : ZMod _)).val)⁻¹ ^ t =
      (ζ ^ (x.val / Model.dfree q d))⁻¹ ^ t * ((ζ ^ (Model.bigN q n d * t))⁻¹) ^ j := by
    intro j
    rw [pow_val_add hζ1, ← Nat.cast_mul, pow_val_natCast hζ1, pow_val_natCast hζ1, mul_inv,
      mul_pow]
    congr 1
    simp only [inv_pow, ← pow_mul]
    ring_nf
  simp_rw [hterm, ← Finset.mul_sum]
  set ω := (ζ ^ (Model.bigN q n d * t))⁻¹ with hω
  split_ifs with hdt
  · -- `d ∣ t`: all terms are equal
    have hd't : Model.dfree q d ∣ t := ((dvd_iff_chr_dfree hq hd0).1 hdt).2
    have hω1 : ω = 1 := by
      obtain ⟨k, hk⟩ := hd't
      rw [hω, hk, ← mul_assoc, hNd, pow_mul, hζ1, one_pow, inv_one]
    rw [hω1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [mul_comm]
    congr 1
    obtain ⟨s, rfl⟩ := hdt
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
    simp only [inv_pow, ← pow_mul]
    congr 2
    obtain ⟨y, hy⟩ := hdx
    rw [hy, Nat.mul_div_cancel_left _ hd'0]
    conv_lhs => rw [← pow_mul_pfree (Model.chr q) d]
    simp only [Model.dval, Model.dfree]
    ring
  · -- `d ∤ t`: geometric sum
    have hd't : ¬ Model.dfree q d ∣ t := fun h => hdt ((dvd_iff_chr_dfree hq hd0).2 ⟨ht, h⟩)
    have hωd : ω ^ Model.dfree q d = 1 := by
      rw [hω, inv_pow, ← pow_mul, mul_right_comm, hNd, pow_mul, hζ1, one_pow, inv_one]
    have hω1 : ω ≠ 1 := by
      intro h
      rw [hω, inv_eq_one, hζ.pow_eq_one_iff_dvd, ← hNd] at h
      exact hd't (Nat.dvd_of_mul_dvd_mul_left hN0 h)
    rw [geom_sum_eq hω1, hωd, sub_self, zero_div, mul_zero]


/-- **Theorem 2.5**, key identity: `C_{d,k}(w) = d' · R^{(d)}_ξ(w)` with `ξ = ζ^{p^c x}`
(written `\hat ξ` in the paper: the `p^c`-th power of the target). -/
theorem fibreSum_eq_levelRes {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ} (hd : d ∣ n)
    {x : ZMod (Model.nfree q n)} (hx : x ∈ Model.targets q n d) (w : E) :
    fibreSum ζ d x w =
      (Model.dfree q d : Ω) * levelRes (F := F) d (ζ ^ (Model.chr q ^ Model.dval q d * x.val)) w := by
  classical
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hd0 : d ≠ 0 := by rintro rfl; exact Module.finrank_pos.ne' (zero_dvd_iff.1 hd)
  set ξ := ζ ^ (Model.chr q ^ Model.dval q d * x.val)
  set A := (range n).filter (fun t => Model.chr q ^ Model.dval q d ∣ t)
  have h1 : fibreSum ζ d x w = ∑ i ∈ univ.filter (fun i : ZMod (Model.nfree q n) =>
      ((Model.dfree q d : ℕ) : ZMod _) * i = x),
        ∑ t ∈ A, (ζ ^ i.val)⁻¹ ^ t * algebraMap E Ω (((frobeniusAlgHom F E) ^ t) w) := by
    simp only [fibreSum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact sum_resSet_resolvent hd _ w
  rw [h1, fibre_eq_image hd hx, Finset.sum_image (fibre_param_injOn hd _), Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [Finset.sum_congr rfl fun t ht => by
    rw [fibre_inner_sum hζ hd hx t (Finset.mem_filter.1 ht).2]]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilt : A.filter (fun t => d ∣ t) = (range (n / d)).image (fun s => d * s) := by
    ext t
    simp only [A, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨ht, _⟩, s, rfl⟩
      exact ⟨s, by
        have := Nat.mul_div_cancel' hd
        by_contra h; push Not at h
        have : d * (n / d) ≤ d * s := Nat.mul_le_mul_left _ h
        omega, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨?_, ((dvd_iff_chr_dfree hq hd0).1 (dvd_mul_right d s)).1⟩, dvd_mul_right d s⟩
      calc d * s < d * (n / d) := Nat.mul_lt_mul_of_pos_left hs (Nat.pos_of_ne_zero hd0)
        _ = n := Nat.mul_div_cancel' hd
  rw [hfilt, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) h)]
  unfold levelRes
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  ring


lemma charP_Ω : CharP Ω (ringChar F) := by
  have : CharP F (ringChar F) := ringChar.charP F
  exact charP_of_injective_algebraMap (algebraMap F Ω).injective _

lemma dfree_cast_ne_zero {d : ℕ} (hd0 : d ≠ 0) : ((Model.dfree q d : ℕ) : Ω) ≠ 0 := by
  have := charP_Ω (F := F) (Ω := Ω)
  rw [Ne, CharP.cast_eq_zero_iff Ω (ringChar F), ← chr_eq_ringChar]
  exact (Nat.Prime.coprime_iff_not_dvd (Model.chr_prime (FiniteField.isPrimePow_card F))).1
    (coprime_pfree (Model.chr_prime (FiniteField.isPrimePow_card F)) hd0)

lemma target_pow_eq_one {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ}
    {x : ZMod (Model.nfree q n)} (hx : x ∈ Model.targets q n d) :
    (ζ ^ (Model.chr q ^ Model.dval q d * x.val)) ^ Model.bigN q n d = 1 := by
  rw [Model.mem_targets] at hx
  have h1 : Model.nfree q n ∣ Model.bigN q n d * x.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast; rw [ZMod.natCast_zmod_val]; exact hx
  obtain ⟨k, hk⟩ := h1
  rw [← pow_mul, mul_assoc, mul_comm x.val, hk, mul_left_comm, pow_mul, hζ.pow_eq_one, one_pow]

lemma exists_target {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ} (hd : d ∣ n)
    {ξ : Ω} (hξ : ξ ^ Model.bigN q n d = 1) :
    ∃ x ∈ Model.targets q n d, ζ ^ (Model.chr q ^ Model.dval q d * x.val) = ξ := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have hNd : Model.bigN q n d * Model.dfree q d = Model.nfree q n := Model.bigN_mul_dfree hd
  have : NeZero (Model.bigN q n d) := ⟨(Model.bigN_pos hd).ne'⟩
  have hζd : IsPrimitiveRoot (ζ ^ Model.dfree q d) (Model.bigN q n d) :=
    hζ.pow (Nat.pos_of_ne_zero (NeZero.ne _)) (by rw [← hNd, mul_comm])
  obtain ⟨j, _, hj⟩ := hζd.eq_pow_of_pow_eq_one hξ
  have hcop : Nat.Coprime (Model.chr q ^ Model.dval q d) (Model.nfree q n) :=
    (Model.coprime_chr_nfree hq hn0).pow_left _
  set y : ZMod (Model.nfree q n) := (((ZMod.unitOfCoprime _ hcop)⁻¹ : (ZMod (Model.nfree q n))ˣ) :
    ZMod (Model.nfree q n))
  have hy : ((Model.chr q ^ Model.dval q d : ℕ) : ZMod (Model.nfree q n)) * y = 1 := by
    have := (ZMod.unitOfCoprime _ hcop).mul_inv
    rwa [ZMod.coe_unitOfCoprime] at this
  refine ⟨((Model.dfree q d * j : ℕ) : ZMod (Model.nfree q n)) * y, ?_, ?_⟩
  · rw [Model.mem_targets, ← mul_assoc, ← Nat.cast_mul]
    have e : Model.bigN q n d * (Model.dfree q d * j) = Model.nfree q n * j := by
      rw [← mul_assoc, hNd]
    rw [e, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]
  · rw [← hj, ← pow_mul]
    apply pow_eq_pow_of_cast_eq hζ.pow_eq_one
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    calc ((Model.chr q ^ Model.dval q d : ℕ) : ZMod (Model.nfree q n)) *
          (((Model.dfree q d * j : ℕ) : ZMod (Model.nfree q n)) * y)
        = ((Model.dfree q d * j : ℕ) : ZMod (Model.nfree q n)) *
          (((Model.chr q ^ Model.dval q d : ℕ) : ZMod (Model.nfree q n)) * y) := by ring
      _ = _ := by rw [hy, mul_one]

/-- **Theorem 2.5** (fibre-sum criterion), first part: for `d ∣ n`, `w` is normal over
`𝔽_{q^d}` iff `C_{d,k}(w) ≠ 0` for every `k ∈ ℤ/N` (i.e. for every target `x`). -/
theorem normal_iff_fibreSum {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ} (hd : d ∣ n)
    (w : E) :
    IsNormalElem (levelField (F := F) (E := E) d) E w ↔
      ∀ x ∈ Model.targets q n d, fibreSum ζ d x w ≠ 0 := by
  have hd0 : d ≠ 0 := by rintro rfl; exact Module.finrank_pos.ne' (zero_dvd_iff.1 hd)
  rw [normal_level_iff hζ hd]
  constructor
  · intro h x hx
    rw [fibreSum_eq_levelRes hζ hd hx]
    exact mul_ne_zero (dfree_cast_ne_zero hd0) (h _ (target_pow_eq_one hζ hx))
  · intro h ξ hξ
    obtain ⟨x, hx, rfl⟩ := exists_target hζ hd hξ
    have := h x hx
    rw [fibreSum_eq_levelRes hζ hd hx] at this
    exact right_ne_zero_of_mul this


lemma card_levelField {d : ℕ} (hd : d ∣ n) [Fintype (levelField (F := F) (E := E) d)] :
    Fintype.card (levelField (F := F) (E := E) d) = q ^ d := by
  rw [Module.card_eq_pow_finrank (K := F), finrank_levelField hd]

lemma lagrangeResolvent_levelField_eq {d : ℕ} (hd : d ∣ n)
    [Fintype (levelField (F := F) (E := E) d)] (ξ : Ω) (w : E) :
    lagrangeResolvent (L := levelField (F := F) (E := E) d) ξ w = levelRes (F := F) d ξ w := by
  rw [lagrangeResolvent_apply, finrank_levelField_top hd]
  unfold levelRes
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [frob_pow_apply, frob_pow_apply, card_levelField hd, pow_mul]

lemma levelRes_frob_shift {d : ℕ} (hd : d ∣ n) {ξ : Ω} (hξ : ξ ^ (n / d) = 1) (w : E) :
    levelRes (F := F) d ξ (((frobeniusAlgHom F E) ^ d) w) = ξ * levelRes (F := F) d ξ w := by
  have : Fintype (levelField (F := F) (E := E) d) := Fintype.ofFinite _
  have e : ((frobeniusAlgHom F E) ^ d) w = frobeniusAlgHom (levelField (F := F) (E := E) d) E w := by
    rw [frob_pow_apply, coe_frobeniusAlgHom, card_levelField hd]
  rw [← lagrangeResolvent_levelField_eq hd, ← lagrangeResolvent_levelField_eq hd, e,
    lagrangeResolvent_frob]
  rwa [finrank_levelField_top hd]

lemma levelRes_pow_card (d : ℕ) (ξ : Ω) (w : E) :
    (levelRes (F := F) d ξ w) ^ (q ^ d) =
      levelRes (F := F) d (ξ ^ q ^ d) (((frobeniusAlgHom F E) ^ d) w) := by
  obtain ⟨k, hp, hk⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hp⟩
  have := charP_Ω (F := F) (Ω := Ω)
  have hQ : q ^ d = ringChar F ^ ((k : ℕ) * d) := by rw [hk, pow_mul]
  unfold levelRes
  rw [hQ, sum_pow_char_pow, ← hQ]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_pow, ← map_pow, inv_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (q ^ d) s]
  congr 2
  rw [frob_pow_apply, frob_pow_apply, frob_pow_apply, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
    add_comm]

lemma levelRes_eq_zero_iff_pow {d : ℕ} (hd : d ∣ n) {ξ : Ω} (hξ : ξ ^ (n / d) = 1) (w : E) :
    levelRes (F := F) d ξ w = 0 ↔ levelRes (F := F) d (ξ ^ q ^ d) w = 0 := by
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.div_pos (Nat.le_of_dvd Module.finrank_pos hd)
      (Nat.pos_of_dvd_of_pos hd Module.finrank_pos)).ne'] at hξ
    exact zero_ne_one hξ
  have hξQ : (ξ ^ q ^ d) ^ (n / d) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ, one_pow]
  have h := levelRes_pow_card (F := F) d ξ w
  rw [levelRes_frob_shift hd hξQ] at h
  constructor
  · intro h0
    rw [h0, zero_pow (pow_pos Fintype.card_pos d).ne'] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (pow_ne_zero _ hξ0)
  · intro h0
    rw [h0, mul_zero] at h
    exact pow_eq_zero_iff (pow_pos Fintype.card_pos d).ne' |>.1 h

/-- `ker C_{d,x} = {w : R^{(d)}_ξ(w) = 0}`, with `ξ = ζ^{p^c x}` (the paper's `\hat ξ`). -/
lemma mem_ker_fibreSum_iff {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ} (hd : d ∣ n)
    {x : ZMod (Model.nfree q n)} (hx : x ∈ Model.targets q n d) (w : E) :
    w ∈ LinearMap.ker (fibreSum ζ d x) ↔
      levelRes (F := F) d (ζ ^ (Model.chr q ^ Model.dval q d * x.val)) w = 0 := by
  have hd0 : d ≠ 0 := by rintro rfl; exact Module.finrank_pos.ne' (zero_dvd_iff.1 hd)
  rw [LinearMap.mem_ker, fibreSum_eq_levelRes hζ hd hx, mul_eq_zero,
    or_iff_right (dfree_cast_ne_zero hd0)]

lemma bigN_dvd_div {d : ℕ} (hd : d ∣ n) : Model.bigN q n d ∣ n / d := by
  have h := pfree_dvd (Model.chr q) (n / d)
  rwa [pfree_div hd] at h

lemma levelRes_eq_zero_iff_pow_iter {d : ℕ} (hd : d ∣ n) {ξ : Ω} (hξ : ξ ^ (n / d) = 1) (w : E)
    (j : ℕ) :
    levelRes (F := F) d (ξ ^ (q ^ d) ^ j) w = 0 ↔ levelRes (F := F) d ξ w = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih, pow_succ, pow_mul]
    have hξj : (ξ ^ (q ^ d) ^ j) ^ (n / d) = 1 := by
      rw [pow_right_comm, hξ, one_pow]
    exact (levelRes_eq_zero_iff_pow hd hξj w).symm

lemma ker_fibreSum_orbit {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ} (hd : d ∣ n)
    {x : ZMod (Model.nfree q n)} (hx : x ∈ Model.targets q n d) (j : ℕ) :
    LinearMap.ker (fibreSum ζ d (((q : ZMod (Model.nfree q n)) ^ d) ^ j * x)) =
      LinearMap.ker (fibreSum ζ d x) := by
  have hx' : ((q : ZMod (Model.nfree q n)) ^ d) ^ j * x ∈ Model.targets q n d := by
    rw [← pow_mul]; exact Model.qpow_mul_mem_targets hx _
  have hξ : (ζ ^ (Model.chr q ^ Model.dval q d * x.val)) ^ (n / d) = 1 := by
    obtain ⟨k, hk⟩ := bigN_dvd_div (F := F) (E := E) hd
    rw [hk, pow_mul, target_pow_eq_one hζ hx, one_pow]
  have hpow : ζ ^ (Model.chr q ^ Model.dval q d * (((q : ZMod (Model.nfree q n)) ^ d) ^ j * x).val) =
      (ζ ^ (Model.chr q ^ Model.dval q d * x.val)) ^ (q ^ d) ^ j := by
    rw [← pow_mul ζ]
    apply pow_eq_pow_of_cast_eq hζ.pow_eq_one
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  ext w
  rw [mem_ker_fibreSum_iff hζ hd hx', mem_ker_fibreSum_iff hζ hd hx, hpow]
  exact levelRes_eq_zero_iff_pow_iter hd hξ w j

/-- The vanishing of a fibre sum only depends on the orbit of the target (by the Frobenius
equivariance of the level resolvents). -/
theorem condKer_eq {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {C : Model.Cond q n}
    (hC : C ∈ Model.conds q n) {x : ZMod (Model.nfree q n)} (hx : x ∈ C.2) :
    condKer ζ C = LinearMap.ker (fibreSum ζ C.1 x) := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  obtain ⟨d, hdn, x0, hx0, rfl⟩ := Model.mem_conds.1 hC
  have hd : d ∣ n := (Nat.mem_divisors.1 hdn).1
  have horb := Model.orbit_eq_of_mem hq hx
  have hxt : x ∈ Model.targets q n d := Model.orbit_subset_targets hq hx0 hx
  have key : ∀ y ∈ Model.orbit q n d x0, LinearMap.ker (fibreSum ζ d y) =
      LinearMap.ker (fibreSum ζ d x) := by
    intro y hy
    rw [← horb] at hy
    obtain ⟨j, rfl⟩ := (Model.mem_orbit_iff hq).1 hy
    exact ker_fibreSum_orbit hζ hd hxt j
  apply le_antisymm
  · exact iInf₂_le x hx
  · exact le_iInf₂ fun y hy => (key y hy).ge

lemma orderOf_target {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ}
    (x : ZMod (Model.nfree q n)) :
    orderOf (ζ ^ (Model.chr q ^ Model.dval q d * x.val)) = addOrderOf x := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have hcop : Nat.Coprime (Model.chr q ^ Model.dval q d) (Model.nfree q n) :=
    (Model.coprime_chr_nfree hq hn0).pow_left _
  have hζo : orderOf ζ = Model.nfree q n := hζ.eq_orderOf.symm
  rw [mul_comm, pow_mul, Nat.Coprime.orderOf_pow]
  · conv_rhs => rw [← ZMod.natCast_zmod_val x]
    rw [ZMod.addOrderOf_coe _ (NeZero.ne _)]
    rcases Nat.eq_zero_or_pos x.val with h0 | hpos
    · rw [h0]; simp only [pow_zero, orderOf_one, Nat.gcd_zero_right]
      exact (Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne _))).symm
    · rw [orderOf_pow' _ hpos.ne', hζo]
  · have h1 : orderOf (ζ ^ x.val) ∣ Model.nfree q n := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    exact (hcop.symm.coprime_dvd_left h1)


lemma pfree_levelField_eq {d : ℕ} (hd : d ∣ n) :
    pfree (ringChar (levelField (F := F) (E := E) d)) (finrank (levelField (F := F) (E := E) d) E) =
      Model.bigN q n d := by
  rw [ringChar_intermediateField, finrank_levelField_top hd, ← chr_eq_ringChar, pfree_div hd]
  rfl

/-- **Theorem 2.5**, second part, in cardinality form: `|V_{d,x}| = q^{n - lcm(d, o(d,x))}`. -/
theorem card_ker_fibreSum {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ} (hd : d ∣ n)
    {x : ZMod (Model.nfree q n)} (hx : x ∈ Model.targets q n d) :
    Nat.card (LinearMap.ker (fibreSum (F := F) (E := E) ζ d x)) =
        q ^ (n - Nat.lcm d (Model.tcodim q n x)) ∧ Nat.lcm d (Model.tcodim q n x) ≤ n := by
  classical
  have hd0 : d ≠ 0 := by rintro rfl; exact Module.finrank_pos.ne' (zero_dvd_iff.1 hd)
  set L := levelField (F := F) (E := E) d
  have : Fintype L := Fintype.ofFinite L
  set ξ := ζ ^ (Model.chr q ^ Model.dval q d * x.val) with hξdef
  have hξ : ξ ^ pfree (ringChar L) (finrank L E) = 1 := by
    rw [pfree_levelField_eq hd]; exact target_pow_eq_one hζ hx
  set KL := LinearMap.ker (lagrangeResolvent (L := L) (K := E) ξ)
  have hset : ((LinearMap.ker (fibreSum (F := F) (E := E) ζ d x) : Submodule F E) : Set E) =
      (KL : Set E) := by
    ext w
    simp only [SetLike.mem_coe, KL, LinearMap.mem_ker]
    rw [← LinearMap.mem_ker, mem_ker_fibreSum_iff hζ hd hx, lagrangeResolvent_levelField_eq hd]
  have hcard : Nat.card (LinearMap.ker (fibreSum (F := F) (E := E) ζ d x)) = Nat.card KL :=
    Nat.card_congr (Equiv.subtypeEquivProp (funext fun w => propext (Set.ext_iff.1 hset w)))
  have hk := finrank_ker_lagrangeResolvent (L := L) (K := E) ξ hξ
  rw [card_levelField hd, orderOf_target hζ x, finrank_levelField_top hd] at hk
  set k := orderOf (((q ^ d : ℕ) : ZMod (addOrderOf x)))
  have hkord : k = Model.tcodim q n x / Nat.gcd (Model.tcodim q n x) d := by
    simp only [k, Model.tcodim]
    rw [← ordMod_pow q _ hd0]
    simp [ordMod]
  have hdk : d * k = Nat.lcm d (Model.tcodim q n x) := by
    rw [hkord, Nat.lcm, Nat.gcd_comm (Model.tcodim q n x) d, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
  -- `k ≤ n/d` via the degree of the minimal polynomial
  have hkle : k ≤ n / d := by
    have hM' : 0 < pfree (ringChar L) (finrank L E) := pfree_pos _ Module.finrank_pos.ne'
    have hint : IsIntegral L ξ := IsIntegral.of_pow hM' (by rw [hξ]; exact isIntegral_one)
    have hdeg := natDegree_minpoly_eq_orderOf (L := L) hξ hM'
    rw [card_levelField hd, orderOf_target hζ x] at hdeg
    have hdvd : minpoly L ξ ∣ polyP L E := by
      apply minpoly.dvd
      simp only [polyP, map_sub, map_pow, aeval_X, map_one]
      rw [pow_finrank_eq_one_of_pow_pfree hξ, sub_self]
    have := natDegree_le_of_dvd hdvd (polyP_monic (L := L) (K := E)).ne_zero
    rw [natDegree_polyP, finrank_levelField_top hd, hdeg] at this
    exact this
  have hlcm : Nat.lcm d (Model.tcodim q n x) ≤ n := by
    rw [← hdk]
    calc d * k ≤ d * (n / d) := Nat.mul_le_mul_left _ hkle
      _ = n := Nat.mul_div_cancel' hd
  refine ⟨?_, hlcm⟩
  rw [hcard, Module.natCard_eq_pow_finrank (K := L), hk, Nat.card_eq_fintype_card, card_levelField hd,
    ← pow_mul, Nat.mul_sub, Nat.mul_div_cancel' hd, hdk]

/-- **Theorem 2.5**, second part: `V_{d,k}` is an `F`-subspace of codimension `lcm(d, o(d,k))`. -/
theorem finrank_ker_fibreSum {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ}
    (hd : d ∣ n) {x : ZMod (Model.nfree q n)} (hx : x ∈ Model.targets q n d) :
    finrank F (LinearMap.ker (fibreSum (F := F) (E := E) ζ d x)) =
      n - Nat.lcm d (Model.tcodim q n x) := by
  have hq2 : 2 ≤ q := (FiniteField.isPrimePow_card F).two_le
  have h := (card_ker_fibreSum hζ hd hx).1
  rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card] at h
  exact Nat.pow_right_injective hq2 h

/-- **Theorem 2.5**, for an essential condition: `V_C` has codimension `o(C)`, i.e.
`|V_C| = q^{n - o(C)}`. -/
theorem card_condKer {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {C : Model.Cond q n}
    (hC : C ∈ Model.essConds q n) :
    Nat.card (condKer (F := F) (E := E) ζ C) = q ^ (n - Model.codim q n C) ∧
      Model.codim q n C ≤ n := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hC' := Model.essConds_subset hC
  obtain ⟨d, hdn, x0, hx0, rfl⟩ := Model.mem_conds.1 hC'
  have hd : d ∣ n := (Nat.mem_divisors.1 hdn).1
  have hess : d ∣ Model.codim q n (d, Model.orbit q n d x0) := (Model.mem_essConds.1 hC).2
  rw [Model.codim_orbit hq] at hess ⊢
  rw [condKer_eq hζ hC' (Model.mem_orbit_self d x0)]
  have h := card_ker_fibreSum hζ hd hx0
  rwa [Nat.lcm_eq_right hess] at h

/-- Termwise Frobenius: `(R^{(d)}_ξ(w))^{q^j} = R^{(d)}_{ξ^{q^j}}(σ^j w)`. -/
lemma levelRes_pow_q (d : ℕ) (ξ : Ω) (w : E) (j : ℕ) :
    (levelRes (F := F) d ξ w) ^ (q ^ j) =
      levelRes (F := F) d (ξ ^ q ^ j) (((frobeniusAlgHom F E) ^ j) w) := by
  obtain ⟨k, hp, hk⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hp⟩
  have := charP_Ω (F := F) (Ω := Ω)
  have hQ : q ^ j = ringChar F ^ ((k : ℕ) * j) := by rw [hk, pow_mul]
  unfold levelRes
  rw [hQ, sum_pow_char_pow, ← hQ]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_pow, ← map_pow, inv_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (q ^ j) s]
  congr 2
  rw [frob_pow_apply, frob_pow_apply, frob_pow_apply, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
    add_comm]

lemma sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m k : ℕ) :
    ∑ t ∈ range (m * k), f t = ∑ s ∈ range k, ∑ r ∈ range m, f (m * s + r) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Splitting the sum of `R^{(c)}` along `t = m s + r`. -/
lemma levelRes_lower {c d : ℕ} (hd : d ∣ n) (hcd : c ∣ d) (hc0 : c ≠ 0) (ξ' : Ω) (w : E) :
    levelRes (F := F) c ξ' w = ∑ r ∈ range (d / c),
      ξ'⁻¹ ^ r * levelRes (F := F) d (ξ' ^ (d / c)) (((frobeniusAlgHom F E) ^ (c * r)) w) := by
  set m := d / c with hm
  have hcm : c * m = d := Nat.mul_div_cancel' hcd
  have hnc : n / c = m * (n / d) := by
    have e : n = c * (m * (n / d)) := by rw [← mul_assoc, hcm, Nat.mul_div_cancel' hd]
    conv_lhs => rw [e]
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hc0)]
  unfold levelRes
  rw [hnc, sum_range_mul_eq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show c * (m * s + r) = d * s + c * r by rw [mul_add, ← mul_assoc, hcm],
    pow_add (frobeniusAlgHom F E), AlgHom.mul_apply, inv_pow, inv_pow, inv_pow, ← pow_mul, pow_add]
  ring

/-- If `R^{(d)}_ξ(w) = 0`, then `R^{(d)}_ξ(σ^k w) = 0` whenever `ξ^{q^{da+k}} = ξ` for some `a`. -/
lemma levelRes_shift_zero {d : ℕ} (hd : d ∣ n) {ξ : Ω} (hξ : ξ ^ (n / d) = 1) {w : E}
    (hw : levelRes (F := F) d ξ w = 0) {k a : ℕ} (hk : ξ ^ q ^ (d * a + k) = ξ) :
    levelRes (F := F) d ξ (((frobeniusAlgHom F E) ^ k) w) = 0 := by
  have h1 : levelRes (F := F) d (ξ ^ (q ^ d) ^ a) w = 0 :=
    (levelRes_eq_zero_iff_pow_iter hd hξ w a).2 hw
  have h2 := levelRes_pow_q (F := F) d (ξ ^ (q ^ d) ^ a) w k
  rw [h1, zero_pow (pow_pos Fintype.card_pos k).ne', ← pow_mul, ← pow_mul, ← pow_add,
    mul_comm d a] at h2
  rw [mul_comm d a] at hk
  rw [hk] at h2
  exact h2.symm

lemma exists_exp_dvd {d o : ℕ} (ho : 1 ≤ o) (r : ℕ) : ∃ a : ℕ, o ∣ d * a + Nat.gcd d o * r := by
  have hle : Nat.gcd d o ≤ o := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right d o)
  rcases eq_or_lt_of_le hle with h | h
  · exact ⟨0, by rw [h]; simp⟩
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd h
    obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
    refine ⟨m * r * o', ?_⟩
    have e := Nat.div_add_mod (d * m) (o' + 1)
    rw [hm] at e
    refine ⟨(d * m / (o' + 1)) * r * o' + Nat.gcd d (o' + 1) * r, ?_⟩
    calc d * (m * r * o') + Nat.gcd d (o' + 1) * r
        = (d * m) * r * o' + Nat.gcd d (o' + 1) * r := by ring
      _ = ((o' + 1) * (d * m / (o' + 1)) + Nat.gcd d (o' + 1)) * r * o' +
            Nat.gcd d (o' + 1) * r := by rw [e]
      _ = (o' + 1) * ((d * m / (o' + 1)) * r * o' + Nat.gcd d (o' + 1) * r) := by ring

/-- The inclusion `V_{d,x} ⊆ V_{C'}` for a condition `C' = (c₀, x')` at level
`c₀ = gcd(d, o(d,x))`, and the essentiality of `C'` (proof of Theorem 2.6): the kernel is invariant under
`σ^{c₀}` (`levelRes_shift_zero`, the paper's first step), and the resolvent sum at level `c₀` is a
combination of the resolvent sums at level `d` of the elements `σ^{c₀ r}(w)` (`levelRes_lower`, the
paper's second step). Finally `c₀ ∣ o(C')`: in the model `x = (d'/c₀') x'` (the paper's
`ξ = ξ₁^{d/c₀}`), so `e = ord(x)` divides `e(C') = ord(x')`, hence `ord_e(q) ∣ ord_{e(C')}(q) = o(C')`, and
`c₀ ∣ ord_e(q)`. -/
lemma fibreSum_zero_lower {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) {d : ℕ} (hd : d ∣ n)
    {x : ZMod (Model.nfree q n)} (hx : x ∈ Model.targets q n d) {w : E}
    (h0 : fibreSum ζ d x w = 0) :
    ∃ x' ∈ Model.targets q n (Nat.gcd d (Model.tcodim q n x)),
      Nat.gcd d (Model.tcodim q n x) ∣ Model.tcodim q n x' ∧
        fibreSum ζ (Nat.gcd d (Model.tcodim q n x)) x' w = 0 := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hd0 : d ≠ 0 := by rintro rfl; exact Module.finrank_pos.ne' (zero_dvd_iff.1 hd)
  set o := Model.tcodim q n x with ho_def
  have ho : 1 ≤ o := Model.one_le_tcodim hq x
  set c := Nat.gcd d o with hc_def
  have hcd : c ∣ d := Nat.gcd_dvd_left d o
  have hc0 : c ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hd0)).ne'
  have hcn : c ∣ n := hcd.trans hd
  have hNd : Model.bigN q n d * Model.dfree q d = Model.nfree q n := Model.bigN_mul_dfree hd
  have hNc : Model.bigN q n c * Model.dfree q c = Model.nfree q n := Model.bigN_mul_dfree hcn
  have hdx : Model.dfree q d ∣ x.val := by
    rw [Model.mem_targets] at hx
    have h1 : Model.nfree q n ∣ Model.bigN q n d * x.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast; rw [ZMod.natCast_zmod_val]; exact hx
    exact Nat.dvd_of_mul_dvd_mul_left (Model.bigN_pos hd) ((dvd_of_eq hNd).trans h1)
  obtain ⟨y, hy⟩ := hdx
  set x' : ZMod (Model.nfree q n) := ((Model.dfree q c * y : ℕ) : ZMod (Model.nfree q n))
  have hx' : x' ∈ Model.targets q n c := by
    rw [Model.mem_targets, ← Nat.cast_mul, ← mul_assoc, hNc, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  -- `C'` is essential: `x = (d'/c₀') x'`, so `ord(x) ∣ ord(x')` and `o(d,x) ∣ o(C')`
  have hess : c ∣ Model.tcodim q n x' := by
    obtain ⟨t, ht⟩ : Model.dfree q c ∣ Model.dfree q d := pfree_dvd_pfree hcd (Model.chr q)
    have hxt : x = (t : ZMod (Model.nfree q n)) * x' := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      rw [hy, ht]
      simp only [x']
      push_cast
      ring
    have hord : addOrderOf x ∣ addOrderOf x' := by
      rw [hxt]
      exact Model.addOrderOf_mul_dvd t x'
    have htc : Model.tcodim q n x ∣ Model.tcodim q n x' := by
      unfold Model.tcodim
      exact ordMod_dvd_ordMod hord
    exact (Nat.gcd_dvd_right d o).trans htc
  refine ⟨x', hx', hess, ?_⟩
  set ξ := ζ ^ (Model.chr q ^ Model.dval q d * x.val) with hξdef
  set ξ' := ζ ^ (Model.chr q ^ Model.dval q c * x'.val) with hξ'def
  have hξ : ξ ^ (n / d) = 1 := by
    obtain ⟨k, hk⟩ := bigN_dvd_div (F := F) (E := E) hd
    rw [hk, pow_mul, target_pow_eq_one hζ hx, one_pow]
  have hrel : ξ' ^ (d / c) = ξ := by
    rw [hξ'def, hξdef, ← pow_mul]
    apply pow_eq_pow_of_cast_eq hζ.pow_eq_one
    have e1 : Model.chr q ^ Model.dval q c * Model.dfree q c = c := pow_mul_pfree _ _
    have e2 : Model.chr q ^ Model.dval q d * Model.dfree q d = d := pow_mul_pfree _ _
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hxy : x = ((Model.dfree q d * y : ℕ) : ZMod (Model.nfree q n)) := by
      rw [← hy, ZMod.natCast_zmod_val]
    rw [hxy]
    simp only [x']
    obtain ⟨m, hm⟩ := hcd
    have hm' : d / c = m := by rw [hm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hc0)]
    rw [hm']
    have : ((Model.chr q ^ Model.dval q c : ℕ) : ZMod (Model.nfree q n)) *
        ((Model.dfree q c * y : ℕ) : ZMod (Model.nfree q n)) * ((m : ℕ) : ZMod (Model.nfree q n)) =
        ((c * m * y : ℕ) : ZMod (Model.nfree q n)) := by
      have hnat : Model.chr q ^ Model.dval q c * (Model.dfree q c * y) * m = c * m * y := by
        rw [← mul_assoc, e1]; ring
      rw [← hnat]; push_cast; ring
    have hnat2 : c * m * y = Model.chr q ^ Model.dval q d * (Model.dfree q d * y) := by
      rw [← mul_assoc, e2, hm]
    rw [this, hnat2]
    push_cast; ring
  have hzero : levelRes (F := F) d ξ w = 0 := (mem_ker_fibreSum_iff hζ hd hx w).1 h0
  have hshift : ∀ r : ℕ, levelRes (F := F) d ξ (((frobeniusAlgHom F E) ^ (c * r)) w) = 0 := by
    intro r
    obtain ⟨a, ha⟩ := exists_exp_dvd (d := d) ho r
    apply levelRes_shift_zero hd hξ hzero (a := a)
    have hξ0 : ξ ≠ 0 := by
      intro h; rw [h, zero_pow (Nat.div_pos (Nat.le_of_dvd Module.finrank_pos hd)
        (Nat.pos_of_ne_zero hd0)).ne'] at hξ; exact zero_ne_one hξ
    rw [pow_pow_eq_self_iff hξ0 Fintype.card_pos, orderOf_target hζ x]
    exact orderOf_dvd_iff_pow_eq_one.1 ha
  have hfin : levelRes (F := F) c ξ' w = 0 := by
    rw [levelRes_lower hd hcd hc0, hrel]
    exact Finset.sum_eq_zero fun r _ => by rw [hshift r, mul_zero]
  exact LinearMap.mem_ker.1 ((mem_ker_fibreSum_iff hζ hcn hx' w).2 hfin)

/-- **Theorem 2.6** (essential reduction): `w` is completely normal iff `C(w) ≠ 0` for every
essential condition `C`. As in the paper, for a condition `(d, x)` that is not essential,
`V_{d,x} ⊆ V_{C'}` for the essential condition `C'` at level `c₀ = gcd(d, o(d,x))` of
`fibreSum_zero_lower`. -/
theorem isCompletelyNormal_iff_essential {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n))
    (w : E) :
    IsCompletelyNormal F E w ↔ ∀ C ∈ Model.essConds q n, w ∉ condKer (F := F) ζ C := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  rw [isCompletelyNormal_iff_levelField]
  constructor
  · intro h C hC
    have hC' := Model.essConds_subset hC
    obtain ⟨d, hdn, x0, hx0, rfl⟩ := Model.mem_conds.1 hC'
    rw [condKer_eq hζ hC' (Model.mem_orbit_self d x0), LinearMap.mem_ker]
    exact (normal_iff_fibreSum hζ (Nat.mem_divisors.1 hdn).1 w).1 (h d hdn) x0 hx0
  · intro h d hdn
    have hd : d ∣ n := (Nat.mem_divisors.1 hdn).1
    -- an essential condition `(c, x)` with `C(w) = 0` contradicts the hypothesis
    have hcontra : ∀ c, c ∣ n → ∀ x ∈ Model.targets q n c, c ∣ Model.tcodim q n x →
        fibreSum ζ c x w ≠ 0 := by
      intro c hc x hx hess h0
      have hC : (c, Model.orbit q n c x) ∈ Model.essConds q n := by
        rw [Model.mem_essConds, Model.codim_orbit hq]
        exact ⟨Model.mem_conds.2 ⟨c, Nat.mem_divisors.2 ⟨hc, Module.finrank_pos.ne'⟩, x, hx, rfl⟩,
          hess⟩
      apply h _ hC
      rw [condKer_eq hζ (Model.essConds_subset hC) (Model.mem_orbit_self c x), LinearMap.mem_ker]
      exact h0
    refine (normal_iff_fibreSum hζ hd w).2 fun x hx h0 => ?_
    by_cases hess : d ∣ Model.tcodim q n x
    · exact hcontra d hd x hx hess h0
    · -- `(d, x)` is not essential: `V_{d,x} ⊆ V_{C'}` with `C'` essential at level `gcd(d, o(d,x))`
      obtain ⟨x', hx', hess', h0'⟩ := fibreSum_zero_lower hζ hd hx h0
      exact hcontra _ ((Nat.gcd_dvd_left _ _).trans hd) x' hx' hess' h0'


end Setting

/-- A field `Ω ⊇ E` with a primitive `n'`-th root of unity exists: the algebraic closure. -/
theorem exists_primitiveRoot_algebraicClosure (E : Type*) [Field E] [Fintype E] (m : ℕ)
    (hm : (m : E) ≠ 0) : ∃ ζ : AlgebraicClosure E, IsPrimitiveRoot ζ m := by
  have : NeZero (m : E) := ⟨hm⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure E) m

end MorganMullen
