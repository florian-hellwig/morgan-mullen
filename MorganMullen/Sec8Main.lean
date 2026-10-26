import MorganMullen.Sec4Counting
import MorganMullen.Sec5Omega
import MorganMullen.Sec6NumberOfConditions
import MorganMullen.Sec7Weights
import MorganMullen.Sec8Certificates
import MorganMullen.Sec8Finite
import MorganMullen.Sec8Analytic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Section 8: the main theorem

* Theorem 8.1 (unconditional criterion): (a) `delta_ge_deltaStar` (`δ_n ≥ δ_*`), (b) `hasMM_of_star`
  (criterion `(*)`).
* Lemma 8.2 (analytic bounds), the function `F_k` of `(**)`.
* Proposition 8.3 (analytic range; the numerical inequalities `(**)` are in `Sec8Analytic.lean`),
  Proposition 8.4 (finite ranges), Proposition 8.5 (certificates).
* Theorem 8.6 (Main Theorem): every finite extension `E/F` has the Morgan–Mullen property.
-/

namespace MorganMullen

open Module Finset

/-- Concavity: `(1 - W)^{w/W} ≤ 1 - w` for `0 ≤ w ≤ W < 1`. -/
lemma rpow_div_le_one_sub {W w : ℝ} (hW0 : 0 < W) (hW1 : W < 1) (hw0 : 0 ≤ w) (hwW : w ≤ W) :
    (1 - W) ^ (w / W) ≤ 1 - w := by
  have ht0 : 0 ≤ w / W := div_nonneg hw0 hW0.le
  have ht1 : w / W ≤ 1 := (div_le_one hW0).mpr hwW
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - w / W) (w₂ := w / W) (p₁ := 1)
    (p₂ := 1 - W) (by linarith) ht0 zero_le_one (by linarith) (by ring)
  rw [Real.one_rpow, one_mul] at h
  have e : (1 - w / W) * 1 + w / W * (1 - W) = 1 - w := by field_simp; ring
  linarith

section Components

variable {q n : ℕ} [NeZero n]

/-- A component of the essential conditions containing a condition of codimension `1` is the
singleton of that condition. -/
lemma eq_singleton_of_codim_one (hq : IsPrimePow q) {K : Finset (Model.Cond q n)}
    (hK : K ∈ Model.components q n (Model.essConds q n)) {C : Model.Cond q n} (hCK : C ∈ K)
    (h1 : Model.codim q n C = 1) : K = {C} := by
  have hC : C ∈ Model.essConds q n := (Model.components_partition _).1 K hK hCK
  rw [eq_of_mem_components hK (component_mem_components hC) hCK (mem_component_self hC),
    (Model.codim_one_singleton hq hC h1).2]

/-- A component that is not made of conditions of codimension `≥ 2` is a singleton `{C}` with
`o(C) = 1`. -/
lemma exists_codim_one_of_not (hq : IsPrimePow q) {K : Finset (Model.Cond q n)}
    (hK : K ∈ Model.components q n (Model.essConds q n))
    (hK2 : ¬ ∀ C ∈ K, 2 ≤ Model.codim q n C) :
    ∃ C ∈ Model.essConds q n, Model.codim q n C = 1 ∧ K = {C} := by
  push Not at hK2
  obtain ⟨C, hCK, hlt⟩ := hK2
  have hC : C ∈ Model.essConds q n := (Model.components_partition _).1 K hK hCK
  have h1 : Model.codim q n C = 1 := by
    have := Model.one_le_codim hq (Model.essConds_subset hC); omega
  exact ⟨C, hC, h1, eq_singleton_of_codim_one hq hK hCK h1⟩

/-- The components consisting of conditions of codimension `≥ 2` partition the essential conditions
of codimension `≥ 2`, hence their weights add up to `S`. -/
lemma sum_weight_codim_ge_two (hq : IsPrimePow q) :
    ∑ K ∈ (Model.components q n (Model.essConds q n)).filter
        (fun K => ∀ C ∈ K, 2 ≤ Model.codim q n C), Model.weight q n K = Model.sumS q n := by
  classical
  set comps := Model.components q n (Model.essConds q n) with hcomps
  set K₂ := comps.filter (fun K => ∀ C ∈ K, 2 ≤ Model.codim q n C) with hK₂
  have hdisj : (K₂ : Set (Finset (Model.Cond q n))).PairwiseDisjoint id := by
    intro K hK K' hK' hne
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro C hCK hCK'
    have hK1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hK)).1
    have hK1' := (Finset.mem_filter.mp (Finset.mem_coe.mp hK')).1
    exact hne (eq_of_mem_components hK1 hK1' hCK hCK')
  have hU : K₂.biUnion id = (Model.essConds q n).filter fun C => 2 ≤ Model.codim q n C := by
    ext C
    simp only [Finset.mem_biUnion, id, Finset.mem_filter, hK₂]
    constructor
    · rintro ⟨K, ⟨hK, hK2⟩, hCK⟩
      exact ⟨(Model.components_partition _).1 K hK hCK, hK2 C hCK⟩
    · rintro ⟨hC, h2⟩
      exact ⟨Model.component q n (Model.essConds q n) C,
        ⟨component_mem_components hC, Model.codim_ge_two_component hq hC h2⟩, mem_component_self hC⟩
  unfold Model.sumS
  rw [← hU]
  unfold Model.weight
  rw [Finset.sum_biUnion hdisj]
  rfl

lemma card_codim_one_comps_le (hq : IsPrimePow q) :
    ((Model.components q n (Model.essConds q n)).filter
        (fun K => ¬ ∀ C ∈ K, 2 ≤ Model.codim q n C)).card ≤
      ((Model.essConds q n).filter fun C => Model.codim q n C = 1).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le
    (s := (Model.essConds q n).filter fun C => Model.codim q n C = 1) (f := fun C => {C}))
  intro K hK
  obtain ⟨hK, hK2⟩ := Finset.mem_filter.mp hK
  obtain ⟨C, hC, h1, rfl⟩ := exists_codim_one_of_not hq hK hK2
  exact Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨hC, h1⟩, rfl⟩

/-- Every factor `1 - w_K` is positive (if the components without a condition of codimension `1`
have weight `≤ W < 1`; the others are codimension-one singletons, of weight `1/q`). -/
lemma one_sub_weight_pos (hq : IsPrimePow q) {W : ℝ} (hW1 : W < 1)
    (hcomp : ∀ K ∈ Model.components q n (Model.essConds q n),
      (∀ C ∈ K, 2 ≤ Model.codim q n C) → (Model.weight q n K : ℝ) ≤ W) :
    ∀ K ∈ Model.components q n (Model.essConds q n), 0 < 1 - Model.weight q n K := by
  intro K hK
  by_cases hKP : ∀ C ∈ K, 2 ≤ Model.codim q n C
  · have h1 := hcomp K hK hKP
    have h2 : (Model.weight q n K : ℝ) < 1 := by linarith
    have h3 : Model.weight q n K < 1 := by exact_mod_cast h2
    linarith
  · obtain ⟨C, -, h1, rfl⟩ := exists_codim_one_of_not hq hK hKP
    have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hq.two_le
    have : Model.weight q n {C} = (q : ℚ)⁻¹ := by
      unfold Model.weight; rw [Finset.sum_singleton, h1, pow_one]
    rw [this, sub_pos]
    exact inv_lt_one_of_one_lt₀ (by linarith)

/-- The product bound of the proof of Theorem 8.1 (a): if every component without a condition of
codimension `1` has weight `≤ W`, `0 < W < 1`, then `(1 - 1/q)^{M_1} (1 - W)^{S/W} ≤ ∏_K (1 - w_K)`.
The codimension-one singletons (Lemma 3.3 (c)) give the factor `(1 - 1/q)^{M_1}`; for the other
components, `1 - w_K ≥ (1 - W)^{w_K/W}` (concavity, `rpow_div_le_one_sub`) and `∑_K w_K = S`. -/
lemma deltaStar_le_prod (hq : IsPrimePow q) {W : ℝ} (hW0 : 0 < W) (hW1 : W < 1)
    (hcomp : ∀ K ∈ Model.components q n (Model.essConds q n),
      (∀ C ∈ K, 2 ≤ Model.codim q n C) → (Model.weight q n K : ℝ) ≤ W) :
    (1 - 1 / (q : ℝ)) ^ ((Model.essConds q n).filter fun C => Model.codim q n C = 1).card *
        (1 - W) ^ ((Model.sumS q n : ℝ) / W) ≤
      ∏ K ∈ Model.components q n (Model.essConds q n), (1 - (Model.weight q n K : ℝ)) := by
  classical
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hqpos : (0 : ℝ) < q := by linarith
  have hW' : 0 < 1 - W := by linarith
  set comps := Model.components q n (Model.essConds q n) with hcomps
  set P : Finset (Model.Cond q n) → Prop := fun K => ∀ C ∈ K, 2 ≤ Model.codim q n C with hP
  set g := ((Model.essConds q n).filter fun C => Model.codim q n C = 1).card with hg
  set a : ℝ := 1 - 1 / (q : ℝ) with ha
  have ha0 : 0 < a := by
    have : 1 / (q : ℝ) < 1 := by rw [div_lt_one hqpos]; linarith
    linarith
  have ha1 : a ≤ 1 := by
    have : 0 ≤ 1 / (q : ℝ) := by positivity
    linarith
  -- weights of the codimension-one singletons
  have hw1 : ∀ K ∈ comps.filter (fun K => ¬ P K), (Model.weight q n K : ℝ) = 1 / (q : ℝ) := by
    intro K hK
    obtain ⟨hK, hKP⟩ := Finset.mem_filter.mp hK
    obtain ⟨C, -, h1, rfl⟩ := exists_codim_one_of_not hq hK hKP
    unfold Model.weight
    rw [Finset.sum_singleton, h1]
    push_cast
    rw [pow_one, one_div]
  rw [← Finset.prod_filter_mul_prod_filter_not comps P]
  -- the codimension-one singletons
  have hK1 : ∏ K ∈ comps.filter (fun K => ¬ P K), (1 - (Model.weight q n K : ℝ)) =
      a ^ (comps.filter (fun K => ¬ P K)).card := by
    rw [Finset.prod_congr rfl (g := fun _ => a), Finset.prod_const]
    intro K hK
    rw [hw1 K hK]
  have hcard : (comps.filter (fun K => ¬ P K)).card ≤ g := card_codim_one_comps_le hq
  have hK1' : a ^ g ≤ ∏ K ∈ comps.filter (fun K => ¬ P K), (1 - (Model.weight q n K : ℝ)) := by
    rw [hK1]
    exact pow_le_pow_of_le_one ha0.le ha1 hcard
  -- the other components
  have hK2 : (1 - W) ^ ((Model.sumS q n : ℝ) / W) ≤
      ∏ K ∈ comps.filter P, (1 - (Model.weight q n K : ℝ)) := by
    have hsum : ∑ K ∈ comps.filter P, Model.weight q n K = Model.sumS q n :=
      sum_weight_codim_ge_two hq
    have hsumR : ∑ K ∈ comps.filter P, (Model.weight q n K : ℝ) = Model.sumS q n := by
      rw [← hsum]; push_cast; rfl
    calc (1 - W) ^ ((Model.sumS q n : ℝ) / W)
        = ∏ K ∈ comps.filter P, (1 - W) ^ ((Model.weight q n K : ℝ) / W) := by
          rw [← Real.rpow_sum_of_pos hW', ← Finset.sum_div, hsumR]
      _ ≤ ∏ K ∈ comps.filter P, (1 - (Model.weight q n K : ℝ)) := by
          refine Finset.prod_le_prod₀ (fun K _ => (Real.rpow_pos_of_pos hW' _).le) fun K hK => ?_
          obtain ⟨hK, hKP⟩ := Finset.mem_filter.mp hK
          have hw0 : (0 : ℝ) ≤ Model.weight q n K := by
            have : (0 : ℚ) ≤ Model.weight q n K :=
              Finset.sum_nonneg fun C _ => by positivity
            exact_mod_cast this
          exact rpow_div_le_one_sub hW0 hW1 hw0 (hcomp K hK hKP)
  have h0 : 0 ≤ (1 - W) ^ ((Model.sumS q n : ℝ) / W) := (Real.rpow_pos_of_pos hW' _).le
  calc a ^ g * (1 - W) ^ ((Model.sumS q n : ℝ) / W) =
        (1 - W) ^ ((Model.sumS q n : ℝ) / W) * a ^ g := mul_comm _ _
    _ ≤ (∏ K ∈ comps.filter P, (1 - (Model.weight q n K : ℝ))) *
        ∏ K ∈ comps.filter (fun K => ¬ P K), (1 - (Model.weight q n K : ℝ)) :=
      mul_le_mul hK2 hK1' (pow_pos ha0 _).le (h0.trans hK2)

end Components

/-- The real-arithmetic core of Theorem 8.1 (b): `(*)` gives `2^ω q^{n/2} 2^M ≤ (q^n - 1)(1 - W)^{S/W}`. -/
lemma star_key (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) {W : ℝ} (hW0 : 0 < W) (hW1 : W < 1)
    {ω M S ω' M' : ℝ} (hω : ω' ≤ ω) (hM : M' ≤ M) (h : StarHolds q n W ω M S) :
    (2 : ℝ) ^ ω' * Real.sqrt ((q : ℝ) ^ n) * (2 : ℝ) ^ M' ≤
      ((q : ℝ) ^ n - 1) * (1 - W) ^ (S / W) := by
  unfold StarHolds cW at h
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hqn : (2 : ℝ) ≤ (q : ℝ) ^ n := by
    calc (2 : ℝ) ≤ q := hq'
      _ = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ n := pow_le_pow_right₀ (by linarith) hn
  have hW' : 0 < 1 - W := by linarith
  have hc : Real.logb 2 (1 / (1 - W)) / W * S = -(S / W * Real.logb 2 (1 - W)) := by
    rw [one_div, Real.logb_inv]; ring
  rw [hc] at h
  -- exponents
  have hsq : Real.sqrt ((q : ℝ) ^ n) = (2 : ℝ) ^ ((n : ℝ) / 2 * Real.logb 2 q) := by
    rw [show (n : ℝ) / 2 * Real.logb 2 q = Real.logb 2 q * ((n : ℝ) / 2) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_logb (by norm_num) (by norm_num) hqpos,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
    congr 1
    ring
  have hW2 : (1 - W) ^ (S / W) = (2 : ℝ) ^ (S / W * Real.logb 2 (1 - W)) := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hW']
  have hq1 : ((q : ℝ) ^ n - 1) = (2 : ℝ) ^ (Real.logb 2 ((q : ℝ) ^ n - 1)) :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
  rw [hsq, hW2, hq1, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
    ← Real.rpow_add (by norm_num)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

section Setting

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

local notation "q" => Fintype.card F
local notation "n" => Module.finrank F E

/-- **Theorem 8.1 (a)** (unconditional criterion): let `0 < W < 1` bound the weight of every component
without a condition of codimension `1`. Then `δ_n ≥ δ_* = (1 - 1/q)^{M_1} (1 - W)^{S/W}`
(`= (1 - 1/q)^{M_1} 2^{-c(W) S}`, by the identity `(1 - W)^{S/W} = 2^{-c(W) S}` used in `star_key` and
`pcn_error_le_star`), where `M_1` is the number of essential conditions of codimension `1` and
`S` the total weight of the essential conditions of codimension `≥ 2` (product formula, Theorem 3.2, and
`deltaStar_le_prod`). -/
theorem delta_ge_deltaStar (W : ℝ) (hW0 : 0 < W) (hW1 : W < 1)
    (hcomp : ∀ K ∈ Model.components q n (Model.essConds q n),
      (∀ C ∈ K, 2 ≤ Model.codim q n C) → (Model.weight q n K : ℝ) ≤ W) :
    (1 - 1 / (q : ℝ)) ^ ((Model.essConds q n).filter fun C => Model.codim q n C = 1).card *
        (1 - W) ^ ((Model.sumS q n : ℝ) / W) ≤ (cnCount F E : ℝ) / Fintype.card E := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hdelta := delta_ge_prod (F := F) (E := E) (one_sub_weight_pos hq hW1 hcomp)
  have hdeltaR := (Rat.cast_le (K := ℝ)).mpr hdelta
  push_cast at hdeltaR
  exact (deltaStar_le_prod hq hW0 hW1 hcomp).trans hdeltaR

/-- **Theorem 8.1 (b)** (unconditional criterion): let `0 < W < 1` bound the weight of every
component without a condition of codimension `1`. If `(*)` holds with upper bounds `ω`, `M`, `S` for
`ω(q^n - 1)`, the number of essential conditions and the total weight of the essential conditions of
codimension `≥ 2`, then `(q, n)` has the Morgan–Mullen property. As in the paper: `0 < δ_* ≤ δ_n` by (a)
(with the upper bound `S`), `L ≤ 2^M (1 - 1/q)^{M_1}` (`lFactor_le`), and `(*)` gives
`(q^n - 1) δ_* ≥ 2^ω q^{n/2} 2^M (1 - 1/q)^{M_1}` (`star_key`, taking `log₂`); this is the sufficient
condition of Theorem 4.2 (b) (`hasMM_of_counting`). -/
theorem hasMM_of_star (W : ℝ) (hW0 : 0 < W) (hW1 : W < 1)
    (hcomp : ∀ K ∈ Model.components q n (Model.essConds q n),
      (∀ C ∈ K, 2 ≤ Model.codim q n C) → (Model.weight q n K : ℝ) ≤ W)
    {ω M S : ℝ} (hω : ((q ^ n - 1).primeFactors.card : ℝ) ≤ ω) (hM : (Model.numM q n : ℝ) ≤ M)
    (hS : (Model.sumS q n : ℝ) ≤ S) (h : StarHolds q n W ω M S) :
    HasMMProperty F E := by
  classical
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hq2 : 2 ≤ q := hq.two_le
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hqpos : (0 : ℝ) < q := by linarith
  have hn : 1 ≤ n := Module.finrank_pos
  have hW' : 0 < 1 - W := by linarith
  set g := ((Model.essConds q n).filter fun C => Model.codim q n C = 1).card with hg
  set a : ℝ := 1 - 1 / (q : ℝ) with ha
  have ha0 : 0 < a := by
    have : 1 / (q : ℝ) < 1 := by rw [div_lt_one hqpos]; linarith
    linarith
  -- the lower bound `δ_*` of (a), with the upper bound `S` in place of the exact `S`
  set δs : ℝ := a ^ g * (1 - W) ^ (S / W) with hδs
  have hδs0 : 0 < δs := mul_pos (pow_pos ha0 _) (Real.rpow_pos_of_pos hW' _)
  have hδ : δs ≤ (cnCount F E : ℝ) / Fintype.card E := by
    refine le_trans ?_ (delta_ge_deltaStar W hW0 hW1 hcomp)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hW' (by linarith) (div_le_div_of_nonneg_right hS hW0.le))
      (pow_pos ha0 _).le
  refine hasMM_of_counting δs hδs0 hδ ?_
  -- the final inequality
  have hE : Fintype.card E = q ^ n := Module.card_eq_pow_finrank
  have hkey := star_key q n hq2 hn hW0 hW1 hω hM h
  rw [Real.rpow_natCast, Real.rpow_natCast] at hkey
  have hL := lFactor_le (F := F) (E := E)
  have hEq : (Fintype.card E : ℝ) = (q : ℝ) ^ n := by rw [hE]; push_cast; ring
  unfold twoPowOmega
  rw [hEq, hE]
  have hsq0 : 0 ≤ (2 : ℝ) ^ (q ^ n - 1).primeFactors.card * Real.sqrt ((q : ℝ) ^ n) := by positivity
  calc (2 : ℝ) ^ (q ^ n - 1).primeFactors.card * Real.sqrt ((q : ℝ) ^ n) * lFactor F E
      ≤ (2 : ℝ) ^ (q ^ n - 1).primeFactors.card * Real.sqrt ((q : ℝ) ^ n) *
          ((2 : ℝ) ^ Model.numM q n * a ^ g) := mul_le_mul_of_nonneg_left hL hsq0
    _ = ((2 : ℝ) ^ (q ^ n - 1).primeFactors.card * Real.sqrt ((q : ℝ) ^ n) *
          (2 : ℝ) ^ Model.numM q n) * a ^ g := by ring
    _ ≤ (((q : ℝ) ^ n - 1) * (1 - W) ^ (S / W)) * a ^ g :=
        mul_le_mul_of_nonneg_right hkey (pow_pos ha0 _).le
    _ = ((q : ℝ) ^ n - 1) * δs := by rw [hδs]; ring

end Setting

/-- `C_k = ∏_{ℓ < 2^k prime} 2 ℓ^{-1/k}`. -/
noncomputable def Ck (k : ℕ) : ℝ :=
  ∏ ℓ ∈ (range (2 ^ k)).filter Nat.Prime, 2 * (ℓ : ℝ) ^ (-(1 / (k : ℝ)))

/-- For a prime `ℓ < 2^k` the factor `2 ℓ^{-1/k}` is `≥ 1`, for `ℓ ≥ 2^k` it is `≤ 1`. -/
lemma two_mul_rpow_neg_ge_one {k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (h : ℓ < 2 ^ k) :
    1 ≤ 2 * (ℓ : ℝ) ^ (-(1 / (k : ℝ))) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hlt : (ℓ : ℝ) ^ (1 / (k : ℝ)) < 2 := by
    have h' : (ℓ : ℝ) < (2 : ℝ) ^ (k : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast h
    calc (ℓ : ℝ) ^ (1 / (k : ℝ)) < ((2 : ℝ) ^ (k : ℝ)) ^ (1 / (k : ℝ)) :=
          Real.rpow_lt_rpow hℓpos.le h' (by positivity)
      _ = 2 := by rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hkpos.ne', Real.rpow_one]
  rw [Real.rpow_neg hℓpos.le]
  have hp : 0 < (ℓ : ℝ) ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hℓpos _
  rw [← div_eq_mul_inv, le_div_iff₀ hp, one_mul]
  exact hlt.le

lemma two_mul_rpow_neg_le_one {k ℓ : ℕ} (hk : 1 ≤ k) (h : 2 ^ k ≤ ℓ) :
    2 * (ℓ : ℝ) ^ (-(1 / (k : ℝ))) ≤ 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hℓ1 : 1 ≤ ℓ := le_trans (Nat.one_le_two_pow) h
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hge : 2 ≤ (ℓ : ℝ) ^ (1 / (k : ℝ)) := by
    have h' : (2 : ℝ) ^ (k : ℝ) ≤ (ℓ : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast h
    calc (2 : ℝ) = ((2 : ℝ) ^ (k : ℝ)) ^ (1 / (k : ℝ)) := by
          rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hkpos.ne', Real.rpow_one]
      _ ≤ (ℓ : ℝ) ^ (1 / (k : ℝ)) := Real.rpow_le_rpow (by positivity) h' (by positivity)
  rw [Real.rpow_neg hℓpos.le]
  have hp : 0 < (ℓ : ℝ) ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hℓpos _
  rw [← div_eq_mul_inv, div_le_one hp]
  exact hge

/-- **Lemma 8.2 (a)**: `2^{ω(N)} ≤ C_k N^{1/k}` for `N ≥ 1`, `k ≥ 1`. -/
theorem two_pow_omega_le (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    (2 : ℝ) ^ N.primeFactors.card ≤ Ck k * (N : ℝ) ^ (1 / (k : ℝ)) := by
  classical
  set P := N.primeFactors with hP
  set f : ℕ → ℝ := fun ℓ => 2 * (ℓ : ℝ) ^ (-(1 / (k : ℝ))) with hf
  have hprime : ∀ ℓ ∈ P, ℓ.Prime := fun ℓ hℓ => Nat.prime_of_mem_primeFactors hℓ
  -- `2^{ω} = ∏ f(ℓ) · (∏ ℓ)^{1/k}`
  have hsplit : (2 : ℝ) ^ P.card = (∏ ℓ ∈ P, f ℓ) * (∏ ℓ ∈ P, (ℓ : ℝ)) ^ (1 / (k : ℝ)) := by
    rw [← Real.finsetProd_rpow _ _ (fun ℓ _ => by positivity), ← Finset.prod_mul_distrib,
      ← Finset.prod_const]
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (hprime ℓ hℓ).pos
    simp only [hf]
    rw [mul_assoc, ← Real.rpow_add hℓpos, neg_add_cancel, Real.rpow_zero, mul_one]
  -- `∏_{ℓ ∈ P} f ℓ ≤ C_k`
  have hC : ∏ ℓ ∈ P, f ℓ ≤ Ck k := by
    rw [← Finset.prod_filter_mul_prod_filter_not P (fun ℓ => ℓ < 2 ^ k)]
    have h1 : ∏ ℓ ∈ P.filter (fun ℓ => ¬ ℓ < 2 ^ k), f ℓ ≤ 1 := by
      refine Finset.prod_le_one₀ (fun ℓ _ => by positivity) fun ℓ hℓ => ?_
      rw [Finset.mem_filter] at hℓ
      exact two_mul_rpow_neg_le_one hk (by omega)
    have h2 : ∏ ℓ ∈ P.filter (fun ℓ => ℓ < 2 ^ k), f ℓ ≤ Ck k := by
      unfold Ck
      refine Finset.prod_le_prod_of_subset_of_one_le₀ ?_ (fun ℓ _ => by positivity) ?_
      · intro ℓ hℓ
        rw [Finset.mem_filter] at hℓ ⊢
        exact ⟨Finset.mem_range.mpr hℓ.2, hprime ℓ hℓ.1⟩
      · intro ℓ hℓ _
        rw [Finset.mem_filter, Finset.mem_range] at hℓ
        exact two_mul_rpow_neg_ge_one hk hℓ.2.one_lt.le hℓ.1
    have h0 : 0 ≤ ∏ ℓ ∈ P.filter (fun ℓ => ℓ < 2 ^ k), f ℓ :=
      Finset.prod_nonneg fun ℓ _ => by positivity
    calc (∏ ℓ ∈ P.filter (fun ℓ => ℓ < 2 ^ k), f ℓ) * ∏ ℓ ∈ P.filter (fun ℓ => ¬ ℓ < 2 ^ k), f ℓ
        ≤ (∏ ℓ ∈ P.filter (fun ℓ => ℓ < 2 ^ k), f ℓ) * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ ≤ Ck k := by rw [mul_one]; exact h2
  -- `(∏ ℓ)^{1/k} ≤ N^{1/k}`
  have hN' : (∏ ℓ ∈ P, (ℓ : ℝ)) ^ (1 / (k : ℝ)) ≤ (N : ℝ) ^ (1 / (k : ℝ)) := by
    have hle : ∏ ℓ ∈ P, ℓ ≤ N := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
    have hle' : (∏ ℓ ∈ P, (ℓ : ℝ)) ≤ N := by rw [← Nat.cast_prod]; exact_mod_cast hle
    exact Real.rpow_le_rpow (Finset.prod_nonneg fun ℓ _ => by positivity) hle' (by positivity)
  rw [hsplit]
  exact mul_le_mul hC hN' (by positivity) (le_trans (Finset.prod_nonneg fun ℓ _ => by positivity) hC)

/-- `g_q(x) = (π²/6) x - 1 + (1 + ln(x + 1)) q/(q-1) + q/(q-1)²`. -/
noncomputable def gq (q : ℕ) (x : ℝ) : ℝ :=
  Real.pi ^ 2 / 6 * x - 1 + (1 + Real.log (x + 1)) * (q / (q - 1 : ℝ)) + q / ((q : ℝ) - 1) ^ 2

/-! ### Lemma 8.2 (b): auxiliary bounds -/

/-- `σ_1(o)/o = ∑_{e ∣ o} 1/e`. -/
lemma sigma_div_eq_sum (o : ℕ) :
    (ArithmeticFunction.sigma 1 o : ℝ) / o = ∑ e ∈ o.divisors, (e : ℝ)⁻¹ := by
  have h2 : ∑ e ∈ o.divisors, (e : ℝ)⁻¹ = ∑ d ∈ o.divisors, ((o / d : ℕ) : ℝ)⁻¹ :=
    (Nat.sum_div_divisors o (fun e => (e : ℝ)⁻¹)).symm
  rw [h2, ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdo : d ∣ o := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  rw [Nat.cast_div hdo (by exact_mod_cast hdpos.ne'), inv_div]

/-- `σ_1(o)/o ≤ H_o ≤ 1 + ln o`. -/
lemma sigma_div_le_log (o : ℕ) :
    (ArithmeticFunction.sigma 1 o : ℝ) / o ≤ 1 + Real.log o := by
  rw [sigma_div_eq_sum o]
  refine le_trans ?_ (harmonic_le_one_add_log o)
  rw [harmonic_eq_sum_Icc]
  push_cast
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro e he
  rw [Finset.mem_Icc]
  exact ⟨Nat.pos_of_mem_divisors he, Nat.divisor_le he⟩

/-- `∑_{o=1}^{J} σ_1(o)/o ≤ (π²/6) J`. -/
lemma sum_sigma_div_le (J : ℕ) :
    ∑ i ∈ range J, (ArithmeticFunction.sigma 1 (i + 1) : ℝ) / ((i + 1 : ℕ) : ℝ) ≤
      Real.pi ^ 2 / 6 * J := by
  have h1 : ∑ i ∈ range J, (ArithmeticFunction.sigma 1 (i + 1) : ℝ) / ((i + 1 : ℕ) : ℝ) =
      ∑ i ∈ range J, ∑ e ∈ (i + 1).divisors, (e : ℝ)⁻¹ :=
    Finset.sum_congr rfl fun i _ => sigma_div_eq_sum (i + 1)
  rw [h1, Finset.sum_comm' (t' := Ioc 0 J) (s' := fun e => (range J).filter (fun i => e ∣ i + 1))]
  · simp only [Finset.sum_const, Nat.card_multiples, nsmul_eq_mul]
    calc ∑ e ∈ Ioc 0 J, ((J / e : ℕ) : ℝ) * (e : ℝ)⁻¹
        ≤ ∑ e ∈ Ioc 0 J, (J : ℝ) * (1 / (e : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun e _ => ?_
          have : ((J / e : ℕ) : ℝ) ≤ (J : ℝ) / e := Nat.cast_div_le
          calc ((J / e : ℕ) : ℝ) * (e : ℝ)⁻¹ ≤ (J : ℝ) / e * (e : ℝ)⁻¹ :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = (J : ℝ) * (1 / (e : ℝ) ^ 2) := by ring
      _ = J * ∑ e ∈ Ioc 0 J, 1 / (e : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ J * (Real.pi ^ 2 / 6) := by
          gcongr
          exact sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two
      _ = _ := by ring
  · intro i e
    simp only [Finset.mem_range, Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hi, hdvd, -⟩
      exact ⟨⟨hi, hdvd⟩, Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos i),
        (Nat.le_of_dvd (Nat.succ_pos i) hdvd).trans hi⟩
    · rintro ⟨⟨hi, hdvd⟩, -, -⟩
      exact ⟨hi, hdvd, Nat.succ_ne_zero i⟩

/-- The terms `σ_1(o)/o · min(n/q^o, 1)` (`o ≥ 2`) of Lemma 8.2 (b). -/
noncomputable def sTerm (q n o : ℕ) : ℝ :=
  if 2 ≤ o then (ArithmeticFunction.sigma 1 o : ℝ) / o * min ((n : ℝ) / (q : ℝ) ^ o) 1 else 0

lemma sTerm_nonneg (q n o : ℕ) : 0 ≤ sTerm q n o := by
  unfold sTerm
  split_ifs
  · exact mul_nonneg (by positivity) (le_min (by positivity) zero_le_one)
  · exact le_rfl

lemma sTerm_le_sigma (q n o : ℕ) (ho : 2 ≤ o) :
    sTerm q n o ≤ (ArithmeticFunction.sigma 1 o : ℝ) / o := by
  unfold sTerm
  simp only [ho, ↓reduceIte]
  exact mul_le_of_le_one_right (by positivity) (min_le_right _ _)

/-- Tail bound: if `n < q^{J+1}` then `σ_1(o)/o · min(n/q^o, 1) ≤ (1 + ln(J+1) + j) q^{-j}` for
`o = J + 1 + j`. -/
lemma sTerm_tail_le (q n J : ℕ) (hq : 2 ≤ q) (hnJ : n < q ^ (J + 1)) (j : ℕ) :
    sTerm q n (j + (J + 1)) ≤ (1 + Real.log ((J : ℝ) + 1) + j) * (1 / (q : ℝ)) ^ j := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hJ1 : (1 : ℝ) ≤ (J : ℝ) + 1 := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hlogJ : 0 ≤ Real.log ((J : ℝ) + 1) := Real.log_nonneg hJ1
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hB : 0 ≤ 1 + Real.log ((J : ℝ) + 1) + j := by linarith
  unfold sTerm
  split_ifs with h2
  swap
  · positivity
  set o := j + (J + 1) with ho
  -- `σ_1(o)/o ≤ 1 + ln(J+1) + j`
  have hσ : (ArithmeticFunction.sigma 1 o : ℝ) / o ≤ 1 + Real.log ((J : ℝ) + 1) + j := by
    refine (sigma_div_le_log o).trans ?_
    have hoR : (o : ℝ) = j + ((J : ℝ) + 1) := by rw [ho]; push_cast; ring
    have hle : (o : ℝ) ≤ ((J : ℝ) + 1) * ((j : ℝ) + 1) := by
      rw [hoR]; nlinarith
    have hlog1 : Real.log (o : ℝ) ≤ Real.log (((J : ℝ) + 1) * ((j : ℝ) + 1)) :=
      Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by positivity) (by positivity)] at hlog1
    have hlog2 : Real.log ((j : ℝ) + 1) ≤ j := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1)
      linarith
    linarith
  -- `min(n/q^o, 1) ≤ q^{-j}`
  have hmin : min ((n : ℝ) / (q : ℝ) ^ o) 1 ≤ (1 / (q : ℝ)) ^ j := by
    refine (min_le_left _ _).trans ?_
    have hn : (n : ℝ) ≤ (q : ℝ) ^ (J + 1) := by exact_mod_cast hnJ.le
    rw [div_le_iff₀ (by positivity), ho, pow_add, ← mul_assoc, ← mul_pow, one_div_mul_cancel hqpos.ne',
      one_pow, one_mul]
    exact hn
  exact mul_le_mul hσ hmin (le_min (by positivity) zero_le_one) hB

lemma hasSum_tail_bound (q : ℕ) (hq : 2 ≤ q) (A : ℝ) :
    HasSum (fun j : ℕ => (A + j) * (1 / (q : ℝ)) ^ j)
      (A * (q / (q - 1 : ℝ)) + q / ((q : ℝ) - 1) ^ 2) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  have hr1 : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h1 := (hasSum_geometric_of_lt_one hr0 hr1).mul_left A
  have h2 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / (q : ℝ))
    (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  have := h1.add h2
  convert this using 1
  · funext j; ring
  · field_simp

/-- `∑_{o ≥ 2} σ_1(o)/o · min(n/q^o, 1) ≤ (π²/6) J - 1 + (1 + ln(J+1)) q/(q-1) + q/(q-1)²` with
`J = ⌊log_q n⌋`, and the series is summable. -/
lemma tsum_sTerm_le (q n : ℕ) (hq : 2 ≤ q) :
    Summable (sTerm q n) ∧
    ∑' o, sTerm q n o ≤ Real.pi ^ 2 / 6 * (Nat.log q n : ℝ) - 1 +
      ((1 + Real.log ((Nat.log q n : ℝ) + 1)) * (q / (q - 1 : ℝ)) + q / ((q : ℝ) - 1) ^ 2) := by
  set J := Nat.log q n with hJ
  have hnJ : n < q ^ (J + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hb := hasSum_tail_bound q hq (1 + Real.log ((J : ℝ) + 1))
  have htail_sum : Summable fun j => sTerm q n (j + (J + 1)) :=
    Summable.of_nonneg_of_le (fun j => sTerm_nonneg q n _) (sTerm_tail_le q n J hq hnJ)
      hb.summable
  have hsum : Summable (sTerm q n) := (summable_nat_add_iff (J + 1)).mp htail_sum
  refine ⟨hsum, ?_⟩
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · -- `J = 0`, i.e. `n < q`
    rw [← hsum.sum_add_tsum_nat_add 2]
    have h01 : ∑ i ∈ range 2, sTerm q n i = 0 := by
      simp [Finset.sum_range_succ, sTerm]
    have hb' := (hasSum_nat_add_iff' 1).mpr hb
    have hb0 : ∑ i ∈ range 1, (1 + Real.log ((J : ℝ) + 1) + (i : ℝ)) * (1 / (q : ℝ)) ^ i = 1 := by
      have : (J : ℝ) = 0 := by exact_mod_cast hJ0
      simp [this]
    rw [hb0] at hb'
    have hle : ∀ j, sTerm q n (j + 2) ≤
        (1 + Real.log ((J : ℝ) + 1) + ((j + 1 : ℕ) : ℝ)) * (1 / (q : ℝ)) ^ (j + 1) := by
      intro j
      have h := sTerm_tail_le q n J hq hnJ (j + 1)
      rwa [show j + 1 + (J + 1) = j + 2 by omega] at h
    have hcmp := ((summable_nat_add_iff 2).mpr hsum).tsum_le_tsum hle hb'.summable
    rw [hb'.tsum_eq] at hcmp
    rw [h01, zero_add]
    have : (J : ℝ) = 0 := by exact_mod_cast hJ0
    rw [this] at hcmp ⊢
    linarith
  · -- `J ≥ 1`
    rw [← hsum.sum_add_tsum_nat_add (J + 1)]
    have hhead : ∑ i ∈ range (J + 1), sTerm q n i ≤ Real.pi ^ 2 / 6 * J - 1 := by
      obtain ⟨J', hJ'⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
      rw [hJ', Finset.sum_range_succ', Finset.sum_range_succ']
      have h0 : sTerm q n 0 = 0 := by simp [sTerm]
      have h1 : sTerm q n (0 + 1) = 0 := by simp [sTerm]
      have hs := sum_sigma_div_le (J' + 1)
      rw [Finset.sum_range_succ'] at hs
      have hσ1 : (ArithmeticFunction.sigma 1 (0 + 1) : ℝ) / ((0 + 1 : ℕ) : ℝ) = 1 := by simp
      rw [hσ1] at hs
      have hle : ∑ i ∈ range J', sTerm q n (i + 1 + 1) ≤
          ∑ i ∈ range J', (ArithmeticFunction.sigma 1 (i + 1 + 1) : ℝ) / ((i + 1 + 1 : ℕ) : ℝ) :=
        Finset.sum_le_sum fun i _ => sTerm_le_sigma q n (i + 1 + 1) (by omega)
      rw [h0, h1]
      linarith
    have htail : ∑' j, sTerm q n (j + (J + 1)) ≤
        (1 + Real.log ((J : ℝ) + 1)) * (q / (q - 1 : ℝ)) + q / ((q : ℝ) - 1) ^ 2 :=
      (htail_sum.tsum_le_tsum (sTerm_tail_le q n J hq hnJ) hb.summable).trans_eq hb.tsum_eq
    linarith

lemma le_gq (q : ℕ) (hq : 2 ≤ q) {J x : ℝ} (hJ : 0 ≤ J) (hJx : J ≤ x) :
    Real.pi ^ 2 / 6 * J - 1 + ((1 + Real.log (J + 1)) * (q / (q - 1 : ℝ)) + q / ((q : ℝ) - 1) ^ 2)
      ≤ gq q x := by
  unfold gq
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hc : 0 ≤ (q : ℝ) / (q - 1 : ℝ) := div_nonneg (by linarith) (by linarith)
  have hlog : Real.log (J + 1) ≤ Real.log (x + 1) := Real.log_le_log (by linarith) (by linarith)
  have h1 : Real.pi ^ 2 / 6 * J ≤ Real.pi ^ 2 / 6 * x :=
    mul_le_mul_of_nonneg_left hJx (by positivity)
  have h2 : (1 + Real.log (J + 1)) * (q / (q - 1 : ℝ)) ≤ (1 + Real.log (x + 1)) * (q / (q - 1 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hc
  linarith

lemma tsum_sTerm_le_gq (q n : ℕ) (hq : 2 ≤ q) (hn : n ≠ 0) :
    ∑' o, sTerm q n o ≤ gq q (Real.logb q n) := by
  obtain ⟨-, h⟩ := tsum_sTerm_le q n hq
  refine h.trans (le_gq q hq (Nat.cast_nonneg _) ?_)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Real.le_logb_iff_rpow_le hq1 hn0, Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self q hn

lemma nfree_le (q n : ℕ) : Model.nfree q n ≤ n := by
  unfold Model.nfree pfree
  exact Nat.div_le_self _ _

lemma sumS_le_tsum_sTerm (q n : ℕ) [NeZero n] (hq : IsPrimePow q) (hsum : Summable (sTerm q n)) :
    (Model.sumS q n : ℝ) ≤ ∑' o, sTerm q n o := by
  classical
  have hq2 : 2 ≤ q := hq.two_le
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set A := (Model.essConds q n).filter fun C => 2 ≤ Model.codim q n C with hA
  have hS : (Model.sumS q n : ℝ) = ∑ C ∈ A, ((q : ℝ) ^ Model.codim q n C)⁻¹ := by
    unfold Model.sumS Model.weight
    push_cast
    rfl
  rw [hS, Finset.sum_comp (fun o => ((q : ℝ) ^ o)⁻¹) (Model.codim q n)]
  refine le_trans (Finset.sum_le_sum fun o ho => ?_)
    (hsum.sum_le_tsum _ (fun o _ => sTerm_nonneg q n o))
  obtain ⟨C, hCA, rfl⟩ := Finset.mem_image.mp ho
  have ho2 : 2 ≤ Model.codim q n C := (Finset.mem_filter.mp hCA).2
  set o := Model.codim q n C with hoC
  obtain ⟨hc1, hc2⟩ := Model.card_codim_le (n := n) hq o (by omega)
  set c' := ((Model.essConds q n).filter fun C => Model.codim q n C = o).card with hc'
  set Y := ((univ : Finset (ZMod (Model.nfree q n))).filter
    fun i => Model.tcodim q n i = o).card with hY
  have hsub : A.filter (fun a => Model.codim q n a = o) ⊆
      (Model.essConds q n).filter (fun a => Model.codim q n a = o) := by
    intro a ha
    simp only [hA, Finset.mem_filter] at ha ⊢
    exact ⟨ha.1.1, ha.2⟩
  have hcc : (#(A.filter (fun a => Model.codim q n a = o)) : ℝ) ≤ c' := by
    exact_mod_cast Finset.card_le_card hsub
  have hσ : (ArithmeticFunction.sigma 1 o : ℝ) = ((∑ d ∈ o.divisors, d : ℕ) : ℝ) := by
    rw [ArithmeticFunction.sigma_one_apply]
  have h1 : (c' : ℝ) ≤ (ArithmeticFunction.sigma 1 o : ℝ) / o * (Y : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hc1
    push_cast at h
    rw [hσ]; push_cast; exact h
  have h2 : (Y : ℝ) ≤ min (Model.nfree q n : ℝ) ((q : ℝ) ^ o - 1) := by
    exact_mod_cast hc2
  have hσo : 0 ≤ (ArithmeticFunction.sigma 1 o : ℝ) / o := by positivity
  have hqo : (0 : ℝ) < (q : ℝ) ^ o := by positivity
  have hmin : min (Model.nfree q n : ℝ) ((q : ℝ) ^ o - 1) * ((q : ℝ) ^ o)⁻¹ ≤
      min ((n : ℝ) / (q : ℝ) ^ o) 1 := by
    refine le_min ?_ ?_
    · refine (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans ?_
      rw [← div_eq_mul_inv]
      have : (Model.nfree q n : ℝ) ≤ n := by exact_mod_cast nfree_le q n
      exact div_le_div_of_nonneg_right this hqo.le
    · refine (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans ?_
      rw [← div_eq_mul_inv, div_le_one hqo]
      linarith
  rw [nsmul_eq_mul]
  unfold sTerm
  simp only [ho2, ↓reduceIte]
  calc (#(A.filter (fun a => Model.codim q n a = o)) : ℝ) * ((q : ℝ) ^ o)⁻¹
      ≤ ((ArithmeticFunction.sigma 1 o : ℝ) / o *
          min (Model.nfree q n : ℝ) ((q : ℝ) ^ o - 1)) * ((q : ℝ) ^ o)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact hcc.trans (h1.trans (mul_le_mul_of_nonneg_left h2 hσo))
    _ = (ArithmeticFunction.sigma 1 o : ℝ) / o *
          (min (Model.nfree q n : ℝ) ((q : ℝ) ^ o - 1) * ((q : ℝ) ^ o)⁻¹) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmin hσo

/-- **Lemma 8.2 (b)**: `S ≤ ∑_{o ≥ 2} σ_1(o)/o · min(n/q^o, 1) ≤ g_q(log_q n)`. -/
theorem sumS_le_gq (q n : ℕ) [NeZero n] (hq : IsPrimePow q) :
    (Model.sumS q n : ℝ) ≤ ∑' o : ℕ, (if 2 ≤ o then
        (ArithmeticFunction.sigma 1 o : ℝ) / o * min ((n : ℝ) / (q : ℝ) ^ o) 1 else 0) ∧
      ∑' o : ℕ, (if 2 ≤ o then
        (ArithmeticFunction.sigma 1 o : ℝ) / o * min ((n : ℝ) / (q : ℝ) ^ o) 1 else 0) ≤
        gq q (Real.logb q n) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hsum := (tsum_sTerm_le q n hq2).1
  exact ⟨sumS_le_tsum_sTerm q n hq hsum, tsum_sTerm_le_gq q n hq2 (NeZero.ne n)⟩

/-- `F_k(n) = n [(1/2 - 1/k) log₂ q - λ] - log₂ C_k - c(W) g_q(log_q n) - 1` (inequality `(**)`).
Here and below the paper's `λ` (the coefficient in `M ≤ λ n`) is called `μ`, since `λ` is reserved in Lean. -/
noncomputable def Fk (q k : ℕ) (μ W : ℝ) (x : ℝ) : ℝ :=
  x * ((1 / 2 - 1 / (k : ℝ)) * Real.logb 2 q - μ) - Real.logb 2 (Ck k) - cW W * gq q (Real.logb q x) - 1

/-- `log₂(q^n - 1) ≥ n log₂ q - 1`. -/
lemma logb_pow_sub_one_ge (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    (n : ℝ) * Real.logb 2 q - 1 ≤ Real.logb 2 ((q : ℝ) ^ n - 1) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (2 : ℝ) ≤ (q : ℝ) ^ n := by
    calc (2 : ℝ) ≤ q := hq'
      _ = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ n := pow_le_pow_right₀ (by linarith) hn
  have hpos : (0 : ℝ) < (q : ℝ) ^ n / 2 := by positivity
  have h1 : (q : ℝ) ^ n / 2 ≤ (q : ℝ) ^ n - 1 := by linarith
  have h2 : Real.logb 2 ((q : ℝ) ^ n / 2) = (n : ℝ) * Real.logb 2 q - 1 := by
    rw [Real.logb_div (by positivity) (by norm_num), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
  rw [← h2]
  exact Real.logb_le_logb_of_le (by norm_num) hpos h1

/-- `(**)` implies `(*)`: if `M ≤ λ n` and `F_k(n) ≥ 0` then `(*)` holds with
`ω = log₂ C_k + (n/k) log₂ q`, `M = λ n`, `S = g_q(log_q n)` (`λ` is the argument `μ`). -/
theorem star_of_Fk (q n k : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (μ W : ℝ)
    (h : 0 ≤ Fk q k μ W n) :
    StarHolds q n W (Real.logb 2 (Ck k) + n / k * Real.logb 2 q) (μ * n) (gq q (Real.logb q n)) := by
  unfold StarHolds
  unfold Fk at h
  have hlog := logb_pow_sub_one_ge q n hq hn
  have e : (n : ℝ) * ((1 / 2 - 1 / (k : ℝ)) * Real.logb 2 q - μ) =
      n / 2 * Real.logb 2 q - n / k * Real.logb 2 q - μ * n := by ring
  rw [e] at h
  linarith

/-- `F_k` of `(**)` is the function `FkE` of `Sec8Analytic.lean`. -/
lemma Fk_eq_FkE (q k : ℕ) (μ W x : ℝ) : Fk q k μ W x = Analytic.FkE q k μ W x := rfl

/-- Lemma 8.2 (a) in logarithmic form: `ω(q^n - 1) ≤ log₂ C_k + (n/k) log₂ q`. -/
lemma omega_le_logb (q n k : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ((q ^ n - 1).primeFactors.card : ℝ) ≤ Real.logb 2 (Ck k) + n / k * Real.logb 2 q := by
  have hqn : q ≤ q ^ n := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
  have hN : 1 ≤ q ^ n - 1 := by omega
  have h := two_pow_omega_le (q ^ n - 1) k hN hk
  have hCpos : 0 < Ck k := by
    unfold Ck
    refine Finset.prod_pos fun ℓ hℓ => ?_
    have : (0 : ℝ) < ℓ := by exact_mod_cast (Finset.mem_filter.1 hℓ).2.pos
    positivity
  have hNR : (0 : ℝ) < ((q ^ n - 1 : ℕ) : ℝ) := by exact_mod_cast hN
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := Real.log_le_log (by positivity) h
  rw [Real.log_mul hCpos.ne' (Real.rpow_pos_of_pos hNR _).ne', Real.log_rpow hNR, Real.log_pow] at h1
  have h2 : Real.log ((q ^ n - 1 : ℕ) : ℝ) ≤ n * Real.log q := by
    rw [← Real.log_pow]
    refine Real.log_le_log hNR ?_
    have : ((q ^ n - 1 : ℕ) : ℝ) ≤ ((q ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
    rw [Nat.cast_pow] at this
    exact this
  have h3 : 1 / (k : ℝ) * Real.log ((q ^ n - 1 : ℕ) : ℝ) ≤ 1 / (k : ℝ) * (n * Real.log q) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  unfold Real.logb
  rw [show Real.log (Ck k) / Real.log 2 + n / k * (Real.log q / Real.log 2) =
      (Real.log (Ck k) + 1 / (k : ℝ) * (n * Real.log q)) / Real.log 2 by ring, le_div_iff₀ hl2]
  linarith

/-- One row of Proposition 8.3: if `M ≤ λ n` (`λ` is the argument `μ`) and `F_k(n) ≥ 0` (with `W = W(q)`), then `(q, n)` has
the Morgan–Mullen property (Theorem 8.1 (b) with Lemma 8.2 and `(**)`). -/
theorem hasMM_of_row {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (k : ℕ) (hk : 1 ≤ k) (μ : ℝ) {q : ℕ} (hqF : Fintype.card F = q)
    (hM : (Model.numM q (finrank F E) : ℝ) ≤ μ * finrank F E)
    (hF : 0 ≤ Analytic.FkE q k μ (Wq q) (finrank F E)) : HasMMProperty F E := by
  subst hqF
  have hq : IsPrimePow (Fintype.card F) := FiniteField.isPrimePow_card F
  have hq2 : 2 ≤ Fintype.card F := hq.two_le
  have hn : 1 ≤ finrank F E := Module.finrank_pos
  obtain ⟨hW0, hW1⟩ := Wq_pos_lt_one (Fintype.card F)
  rw [← Fk_eq_FkE] at hF
  have hstar := star_of_Fk _ _ k hq2 hn μ _ hF
  refine hasMM_of_star (Wq (Fintype.card F)) (by exact_mod_cast hW0) (by exact_mod_cast hW1)
    (fun K hK hK2 => by exact_mod_cast weight_le_Wq _ _ hq hK hK2) ?_ hM ?_ hstar
  · exact omega_le_logb _ _ k hq2 hn hk
  · obtain ⟨h1, h2⟩ := sumS_le_gq (Fintype.card F) (finrank F E) hq
    exact h1.trans h2

lemma Wq_of_ge_32 {q : ℕ} (h : 32 ≤ q) : Wq q = 0.0118 := by
  unfold Wq
  split <;> first | omega | rfl

lemma eq_of_primePow_8_31 {q : ℕ} (hq : IsPrimePow q) (h1 : 8 ≤ q) (h2 : q ≤ 31) :
    q = 8 ∨ q = 9 ∨ q = 11 ∨ q = 13 ∨ q = 16 ∨ q = 17 ∨ q = 19 ∨ q = 23 ∨ q = 25 ∨ q = 27 ∨
      q = 29 ∨ q = 31 := by
  have h15 : q ≠ 15 := by
    rintro rfl
    exact Fin32.not_isPrimePow_of_dvd Nat.prime_three Nat.prime_five (by norm_num) (by norm_num)
      (by norm_num) hq
  have h21 : q ≠ 21 := by
    rintro rfl
    exact Fin32.not_isPrimePow_of_dvd Nat.prime_three Nat.prime_seven (by norm_num)
      (by norm_num) (by norm_num) hq
  interval_cases q <;> first | omega | exact absurd hq (by decide)

/-- **Proposition 8.3** (analytic range): every pair in the ranges of the table
has the Morgan–Mullen property. -/
theorem analytic_range (F E : Type*) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (h : InAnalyticRange (Fintype.card F) (finrank F E)) : HasMMProperty F E := by
  have hq : IsPrimePow (Fintype.card F) := FiniteField.isPrimePow_card F
  have hnR : ∀ m : ℕ, m ≤ finrank F E → (m : ℝ) ≤ finrank F E := fun m hm => by exact_mod_cast hm
  have hM1 : (Model.numM (Fintype.card F) (finrank F E) : ℝ) ≤ 1 * finrank F E := by
    rw [one_mul]; exact_mod_cast Model.numM_le_n hq
  rcases h with ⟨hq2, hn⟩ | ⟨hq3, h3, hn⟩ | ⟨hq3, h3, hn⟩ | ⟨hq4, hn⟩ |
    ⟨hq5, hn⟩ | ⟨hq7, hn⟩ | ⟨h8, h31, hn⟩ | ⟨h32, hn⟩
  · -- `q = 2`
    refine hasMM_of_row 13 (by norm_num) ((41 : ℝ) / 100) hq2 ?_
      (Analytic.row_q2 _ (by exact_mod_cast hn))
    have := Model.numM_le_q2 (n := finrank F E) (by omega)
    have := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at this
    linarith
  · -- `q = 3`, `3 ∣ n`
    refine hasMM_of_row 11 (by norm_num) ((5983 : ℝ) / 10000) hq3 ?_
      (Analytic.row_q3div _ (by exact_mod_cast hn))
    have := Model.numM_le_q3_div (n := finrank F E) h3
    have := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at this
    linarith
  · -- `q = 3`, `3 ∤ n`, `n ≥ 131200`
    refine hasMM_of_row 12 (by norm_num) ((31 : ℝ) / 50) hq3 ?_
      (Analytic.row_q3ndiv _ (by
        have h2769 : 2769 ≤ finrank F E := by omega
        exact_mod_cast h2769))
    have := Model.numM_le_q3_ndiv_large (n := finrank F E) h3 hn
    have := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at this
    linarith
  · -- `q = 4` (all `n ≥ 1010`)
    refine hasMM_of_row 10 (by norm_num) ((3 : ℝ) / 4) hq4 ?_
      (Analytic.row_q4 _ (by exact_mod_cast hn))
    have := Model.numM_le_q4 (n := finrank F E) (by omega)
    have := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at this
    linarith
  · -- `q = 5`
    exact hasMM_of_row 16 (by norm_num) 1 hq5 (hq5 ▸ hM1) (Analytic.row_q5 _ (by exact_mod_cast hn))
  · -- `q = 7`
    exact hasMM_of_row 9 (by norm_num) 1 hq7 (hq7 ▸ hM1) (Analytic.row_q7 _ (by exact_mod_cast hn))
  · -- `8 ≤ q ≤ 31`
    rcases eq_of_primePow_8_31 hq h8 h31 with hq' | hq' | hq' | hq' | hq' | hq' | hq' | hq' | hq' |
      hq' | hq' | hq' <;> rw [hq'] at hn hM1 <;> simp only [thresholdN] at hn
    · exact hasMM_of_row 9 (by norm_num) 1 hq' hM1 (Analytic.row_q8 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 8 (by norm_num) 1 hq' hM1 (Analytic.row_q9 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 7 (by norm_num) 1 hq' hM1 (Analytic.row_q11 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 7 (by norm_num) 1 hq' hM1 (Analytic.row_q13 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 7 (by norm_num) 1 hq' hM1 (Analytic.row_q16 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 7 (by norm_num) 1 hq' hM1 (Analytic.row_q17 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 6 (by norm_num) 1 hq' hM1 (Analytic.row_q19 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 6 (by norm_num) 1 hq' hM1 (Analytic.row_q23 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 6 (by norm_num) 1 hq' hM1 (Analytic.row_q25 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 6 (by norm_num) 1 hq' hM1 (Analytic.row_q27 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 6 (by norm_num) 1 hq' hM1 (Analytic.row_q29 _ (by exact_mod_cast hn))
    · exact hasMM_of_row 6 (by norm_num) 1 hq' hM1 (Analytic.row_q31 _ (by exact_mod_cast hn))
  · -- `q ≥ 32`
    refine hasMM_of_row 6 (by norm_num) 1 rfl hM1 ?_
    rw [Wq_of_ge_32 h32]
    exact Analytic.row_big _ h32 _ (by exact_mod_cast hn)

/-- **Theorem 8.6** (Main Theorem; using the two cited results): for every finite field `F` and
every finite extension `E/F` (i.e. every prime power `q` and every `n ≥ 1`), `E` contains a primitive
element that is completely normal over `F`. -/
theorem morgan_mullen (F E : Type*) [Field F] [Field E] [Finite E] [Algebra F E] :
    HasMMProperty F E := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have : Finite F := Finite.of_injective _ (algebraMap F E).injective
  have : Fintype F := Fintype.ofFinite F
  by_cases hsmall : finrank F E ≤ Fintype.card F
  · exact garefalakis_kapetanakis F E hsmall
  push Not at hsmall
  have hq : IsPrimePow (Fintype.card F) := FiniteField.isPrimePow_card F
  by_cases hA : InAnalyticRange (Fintype.card F) (finrank F E)
  · exact analytic_range F E hA
  by_cases hC : (Fintype.card F, finrank F E) ∈ certPairs
  · exact certificates F E hC
  have hq32 : Fintype.card F < 32 := by
    by_contra h
    push Not at h
    exact hA (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨h, by omega⟩)
  have hstar := finite_ranges (Fintype.card F) (finrank F E) hq hq32 hsmall hA hC
  obtain ⟨hW0, hW1⟩ := Wq_pos_lt_one (Fintype.card F)
  refine hasMM_of_star (Wq (Fintype.card F)) (by exact_mod_cast hW0) (by exact_mod_cast hW1)
    (fun K hK hK2 => by exact_mod_cast weight_le_Wq _ _ hq hK hK2) ?_ le_rfl le_rfl hstar
  have h2 : 2 ≤ Fintype.card F := hq.two_le
  have hω : (((Fintype.card F) ^ (finrank F E) - 1).primeFactors.card : ℝ) ≤
      (omegaBd (Fintype.card F) (finrank F E) : ℝ) := by
    exact_mod_cast omega_le_omegaBd h2 Module.finrank_pos
  linarith

end MorganMullen
