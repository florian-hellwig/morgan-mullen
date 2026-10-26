import MorganMullen.Sec8Defs
import MorganMullen.Sec8Certificates
import MorganMullen.Sec7Weights
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Proposition 8.3: the analytic inequality `(**)`, verified with rational bounds

For `F_k(x) = x [(1/2 - 1/k) log₂ q - λ] - log₂ C_k - c(W) g_q(log_q x) - 1` (`FkE`, definitionally
equal to `Fk` of `Sec8Main.lean`) we prove `F_k(x) ≥ 0` for all real `x ≥ N` for each row of the
table of Proposition 8.3.

The paper's `λ` (the coefficient in `M ≤ λ n`) is called `μ` in the code, since `λ` is reserved in Lean.

* `core_ineq`: if `lam ≤ log₂ q`, `log₂ C_k ≤ L_C`, `c(W) ≤ c`, `q/(q-1) ≤ ρ₁`, `q/(q-1)² ≤ ρ₂`,
  `log₂ N ≤ u_N`, `ln(u_N/lam + 1) ≤ l_T` and the two rational inequalities
  `N A - L_C - c (Z u_N/lam - 1 + (1 + l_T) ρ₁ + ρ₂) - 1 ≥ 0` (value at `N`) and
  `c (Z + ρ₁) ≤ A N lam l₂` (derivative bound) hold, with `A = (1/2 - 1/k) lam - λ`,
  `Z = 1.644935 ≥ π²/6`, `l₂ = 0.6931471803 ≤ ln 2`, then
  `F_k(x) ≥ 0` for `x ≥ N`. As in the paper, the monotonicity in `x` is obtained from
  `ln(x/N) ≤ x/N - 1`: `F_k(x) ≥ F_k(N) + (x - N) [a_k - c(W)(π²/6 + q/(q-1))/(N ln q)]`.
* `CkE`: `log₂ C_k = π(2^k) - log₂(∏_{ℓ < 2^k} ℓ)/k`; the prime count and a lower bound
  `2^a ≤ (∏ ℓ)^b` are checked by computation (`ckCheck_eq`, via `Lean.ofReduceBool`).
* The rational bounds for `log₂ q`, `log₂ N`, `log₂ T`, `c(W)` come from integer inequalities
  `2^a ≤ m^b` checked by the kernel (`decide +kernel`); `π²/6 ≤ 1.644935` follows from
  `ζ(2) = π²/6` and `∑_{n > 50} 1/n² ≤ 2/101`, and `ln 2 ∈ (0.6931471803, 0.6931471808)` from the
  series of `log(1 - x)` at `x = 1/2`.
-/

namespace MorganMullen

namespace Analytic

open Finset

/-- `C_k` (as in `Sec8Main.lean`). -/
noncomputable def CkE (k : ℕ) : ℝ :=
  ∏ ℓ ∈ (range (2 ^ k)).filter Nat.Prime, 2 * (ℓ : ℝ) ^ (-(1 / (k : ℝ)))

/-- `g_q(x)` (as in `Sec8Main.lean`). -/
noncomputable def gqE (q : ℕ) (x : ℝ) : ℝ :=
  Real.pi ^ 2 / 6 * x - 1 + (1 + Real.log (x + 1)) * (q / (q - 1 : ℝ)) + q / ((q : ℝ) - 1) ^ 2

/-- `F_k(x)` (as in `Sec8Main.lean`). -/
noncomputable def FkE (q k : ℕ) (μ W : ℝ) (x : ℝ) : ℝ :=
  x * ((1 / 2 - 1 / (k : ℝ)) * Real.logb 2 q - μ) - Real.logb 2 (CkE k) - cW W * gqE q (Real.logb q x) - 1

/-! ### Constants -/

/-- `ln 2 ∈ (0.6931471803, 0.6931471808)`, from `∑_{i<36} 2^{-(i+1)}/(i+1)`. -/
lemma log_two_bounds : (0.6931471803 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6931471808 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 2) (by norm_num) 36
  have e : Real.log (1 - 1 / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [e, abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

/-- `∑_{i < K} 1/i² ≤ ∑_{i ≤ 50} 1/i² + 2/101 - 2/(2K-1)` for `K ≥ 51`. -/
lemma sum_inv_sq_le (K : ℕ) (hK : 51 ≤ K) :
    ∑ i ∈ range K, (1 : ℝ) / (i : ℝ) ^ 2 ≤
      ∑ i ∈ range 51, (1 : ℝ) / (i : ℝ) ^ 2 + 2 / 101 - 2 / (2 * (K : ℝ) - 1) := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    rw [Finset.sum_range_succ]
    have hK' : (51 : ℝ) ≤ K := by exact_mod_cast hK
    have h1 : (1 : ℝ) / (K : ℝ) ^ 2 ≤ 2 / (2 * (K : ℝ) - 1) - 2 / (2 * ((K + 1 : ℕ) : ℝ) - 1) := by
      push_cast
      rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    linarith

/-- `π²/6 ≤ 1.644935`. -/
lemma pi_sq_div_six_le : Real.pi ^ 2 / 6 ≤ 1644935 / 10 ^ 6 := by
  have hS : ∑ i ∈ range 51, (1 : ℝ) / (i : ℝ) ^ 2 + 2 / 101 ≤ 1644935 / 10 ^ 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  refine le_of_tendsto' hasSum_zeta_two.tendsto_sum_nat fun K => ?_
  rcases le_or_gt 51 K with hK | hK
  · have h := sum_inv_sq_le K hK
    have hK' : (51 : ℝ) ≤ K := by exact_mod_cast hK
    have : 0 ≤ 2 / (2 * (K : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
    linarith
  · have h : ∑ i ∈ range K, (1 : ℝ) / (i : ℝ) ^ 2 ≤ ∑ i ∈ range 51, (1 : ℝ) / (i : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hK.le)
        (fun _ _ _ => by positivity)
    linarith

/-! ### Elementary bounds from integer inequalities -/

lemma div_le_logb_of_pow {x : ℝ} {a b : ℕ} (hb : 0 < b) (h : (2 : ℝ) ^ a ≤ x ^ b) :
    (a : ℝ) / b ≤ Real.logb 2 x := by
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  linarith

lemma logb_le_div_of_pow {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b) (h : x ^ b ≤ (2 : ℝ) ^ a) :
    Real.logb 2 x ≤ (a : ℝ) / b := by
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  linarith

lemma log_le_of_pow {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b) (h : x ^ b ≤ (2 : ℝ) ^ a) :
    Real.log x ≤ (a : ℝ) / b * 0.6931471808 := by
  have h1 := logb_le_div_of_pow hx hb h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : Real.log x = Real.logb 2 x * Real.log 2 := by
    unfold Real.logb; field_simp
  rw [h2]
  have h3 : 0 ≤ (a : ℝ) / b := by positivity
  calc Real.logb 2 x * Real.log 2 ≤ (a : ℝ) / b * Real.log 2 :=
        mul_le_mul_of_nonneg_right h1 hl2.le
    _ ≤ (a : ℝ) / b * 0.6931471808 :=
        mul_le_mul_of_nonneg_left log_two_bounds.2.le h3

/-- `0 ≤ c(W) ≤ r/s / W` for `W = w₁/w₂` with `w₂^s ≤ 2^r (w₂ - w₁)^s`. -/
lemma cW_le_of {W : ℝ} {w1 w2 r s : ℕ} (hW : W = (w1 : ℝ) / w2) (hw1 : 0 < w1) (hw12 : w1 < w2)
    (hs : 0 < s) (h : w2 ^ s ≤ 2 ^ r * (w2 - w1) ^ s) :
    0 ≤ cW W ∧ cW W ≤ (r : ℝ) / s / ((w1 : ℝ) / w2) := by
  have hw1R : (0 : ℝ) < w1 := by exact_mod_cast hw1
  have hw2R : (0 : ℝ) < w2 := by exact_mod_cast (hw1.trans hw12)
  have hdR : (0 : ℝ) < ((w2 - w1 : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hw12)
  have hWpos : (0 : ℝ) < W := by rw [hW]; positivity
  have hx : 1 / (1 - W) = (w2 : ℝ) / ((w2 - w1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hw12.le, hW]
    have : (w2 : ℝ) - w1 ≠ 0 := by
      have : (w1 : ℝ) < w2 := by exact_mod_cast hw12
      linarith
    field_simp
  have hx1 : 1 ≤ 1 / (1 - W) := by
    rw [hx, le_div_iff₀ hdR, one_mul, Nat.cast_sub hw12.le]; linarith
  have hpow : (1 / (1 - W)) ^ s ≤ (2 : ℝ) ^ r := by
    rw [hx, div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast h
  have hl := logb_le_div_of_pow (by linarith) hs hpow
  have hnn : 0 ≤ Real.logb 2 (1 / (1 - W)) := Real.logb_nonneg (by norm_num) hx1
  unfold cW
  refine ⟨div_nonneg hnn hWpos.le, ?_⟩
  rw [← hW]
  exact div_le_div_of_nonneg_right hl hWpos.le

/-! ### The constant `C_k` -/

/-- `log₂ C_k ≤ π(2^k) - (a/b)/k` when `2^a ≤ (∏_{ℓ < 2^k prime} ℓ)^b`. -/
lemma logb_CkE_le (k : ℕ) (hk : 1 ≤ k) (cc ca cb : ℕ) (hcb : 0 < cb)
    (hc : ((range (2 ^ k)).filter Nat.Prime).card = cc)
    (hP : 2 ^ ca ≤ (∏ ℓ ∈ (range (2 ^ k)).filter Nat.Prime, ℓ) ^ cb) :
    Real.logb 2 (CkE k) ≤ (cc : ℝ) - (ca : ℝ) / cb / k := by
  set S := (range (2 ^ k)).filter Nat.Prime with hS
  have hpos : ∀ ℓ ∈ S, (0 : ℝ) < ℓ := fun ℓ hℓ => by
    exact_mod_cast (Finset.mem_filter.1 hℓ).2.pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set P : ℕ := ∏ ℓ ∈ S, ℓ with hPdef
  have hPpos : (0 : ℝ) < P := by
    rw [hPdef, Nat.cast_prod]; exact Finset.prod_pos hpos
  have h1 : Real.log (CkE k) = cc * Real.log 2 - 1 / k * Real.log P := by
    unfold CkE
    rw [Real.log_prod (fun ℓ hℓ => (mul_pos (by norm_num) (Real.rpow_pos_of_pos (hpos ℓ hℓ) _)).ne')]
    rw [hPdef, Nat.cast_prod, Real.log_prod (fun ℓ hℓ => (hpos ℓ hℓ).ne'), Finset.mul_sum, ← hc,
      ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos (hpos ℓ hℓ) _).ne', Real.log_rpow (hpos ℓ hℓ)]
    ring
  have h2 : (ca : ℝ) / cb * Real.log 2 ≤ Real.log P := by
    have h3 : ((2 : ℝ) ^ ca) ≤ (P : ℝ) ^ cb := by exact_mod_cast hP
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow, Real.log_pow] at h4
    rw [div_mul_eq_mul_div, div_le_iff₀ (by exact_mod_cast hcb)]
    linarith
  unfold Real.logb
  rw [h1, div_le_iff₀ hl2]
  have h5 : (ca : ℝ) / cb / k * Real.log 2 ≤ 1 / k * Real.log P := by
    rw [div_mul_eq_mul_div, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right h2 hkR.le
  nlinarith

/-- The table `(k, π(2^k), a, b)` with `2^a ≤ (∏_{ℓ < 2^k prime} ℓ)^b`. -/
def ckTable : List (ℕ × ℕ × ℕ × ℕ) :=
  [(6, 18, 352365, 4598), (7, 31, 22927, 142), (8, 54, 89747, 268), (9, 97, 214294, 305),
   (10, 172, 160406, 113), (11, 309, 845022, 295), (12, 564, 7971759, 1372),
   (13, 1028, 500266, 43), (14, 1900, 2087151, 89), (16, 6542, 6111728, 65)]

/-- The Boolean check of `ckTable`. -/
def ckCheck : Bool := ckTable.all fun e =>
  ((range (2 ^ e.1)).filter Nat.Prime).card == e.2.1 &&
    decide (2 ^ e.2.2.1 ≤ (∏ ℓ ∈ (range (2 ^ e.1)).filter Nat.Prime, ℓ) ^ e.2.2.2)

/-- **The computation**: the table `ckTable` is correct. -/
theorem ckCheck_eq : ckCheck = true := by of_reduce_bool

lemma logb_CkE_le_of_mem {k cc ca cb : ℕ} (h : (k, cc, ca, cb) ∈ ckTable) :
    Real.logb 2 (CkE k) ≤ (cc : ℝ) - (ca : ℝ) / cb / k := by
  have hall := ckCheck_eq
  simp only [ckCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
  obtain ⟨h1, h2⟩ := hall _ h
  have hk : 1 ≤ k ∧ 0 < cb := by
    simp only [ckTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    omega
  exact logb_CkE_le k hk.1 cc ca cb hk.2 h1 h2

/-! ### The core inequality -/

/-- The bound for `g`: for `0 ≤ y ≤ Y₀ + δ` (`Y₀, δ ≥ 0`), `ln(Y₀ + 1) ≤ l_T`, `π²/6 ≤ p`,
`1 ≤ ρ ≤ ρ₁`, `0 ≤ ρ' ≤ ρ₂`. -/
lemma g_bound {y Y0 δ lT p ρ ρ' ρ1 ρ2 : ℝ} (hy0 : 0 ≤ y) (hyY : y ≤ Y0 + δ) (hY0 : 0 ≤ Y0)
    (hδ : 0 ≤ δ) (hlT : Real.log (Y0 + 1) ≤ lT) (hπ : Real.pi ^ 2 / 6 ≤ p) (hρ : 1 ≤ ρ)
    (hρ1 : ρ ≤ ρ1) (hρ' : 0 ≤ ρ') (hρ2 : ρ' ≤ ρ2) :
    0 ≤ Real.pi ^ 2 / 6 * y - 1 + (1 + Real.log (y + 1)) * ρ + ρ' ∧
    Real.pi ^ 2 / 6 * y - 1 + (1 + Real.log (y + 1)) * ρ + ρ' ≤
      p * Y0 - 1 + (1 + lT) * ρ1 + ρ2 + δ * (p + ρ1) := by
  have hlogy0 : 0 ≤ Real.log (y + 1) := Real.log_nonneg (by linarith)
  have hπ0 : 0 ≤ Real.pi ^ 2 / 6 := by positivity
  have hlogy : Real.log (y + 1) ≤ lT + δ := by
    have h1 : Real.log (y + 1) ≤ Real.log (Y0 + δ + 1) := Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (Y0 + δ + 1) - Real.log (Y0 + 1) ≤ δ := by
      rw [← Real.log_div (by linarith) (by linarith)]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have h1 : Real.pi ^ 2 / 6 * y ≤ p * (Y0 + δ) := mul_le_mul hπ hyY hy0 (by linarith)
  have h2 : (1 + Real.log (y + 1)) * ρ ≤ (1 + (lT + δ)) * ρ1 :=
    mul_le_mul (by linarith) hρ1 (by linarith) (by linarith)
  have h3 : 0 ≤ Real.pi ^ 2 / 6 * y := mul_nonneg hπ0 hy0
  have h4 : 1 * ρ ≤ (1 + Real.log (y + 1)) * ρ := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  constructor <;> linarith

/-- `log₂ x ≤ log₂ N + (x - N)/N/l₂` for `x ≥ N > 0`, `0 < l₂ ≤ ln 2`. -/
lemma logb_two_le_add {x N l2 : ℝ} (hN : 0 < N) (hx : N ≤ x) (hl2 : 0 < l2) (hl2' : l2 ≤ Real.log 2) :
    Real.logb 2 x ≤ Real.logb 2 N + (x - N) / N / l2 := by
  have hx0 : 0 < x := by linarith
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : Real.log x - Real.log N ≤ (x - N) / N := by
    rw [← Real.log_div hx0.ne' hN.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hx0 hN)).trans (le_of_eq ?_)
    field_simp
  have e : Real.logb 2 x = Real.logb 2 N + (Real.log x - Real.log N) / Real.log 2 := by
    unfold Real.logb; field_simp; ring
  rw [e]
  have h1 : (Real.log x - Real.log N) / Real.log 2 ≤ (x - N) / N / Real.log 2 :=
    div_le_div_of_nonneg_right hlogx hl2pos.le
  have h2 : (x - N) / N / Real.log 2 ≤ (x - N) / N / l2 :=
    div_le_div_of_nonneg_left (div_nonneg (by linarith) hN.le) hl2 hl2'
  linarith

theorem core_ineq (q k : ℕ) (μ cv C : ℝ) (N : ℕ) (lam Lc c ρ1 ρ2 uN lT : ℝ)
    (hq : 2 ≤ q) (hk : 2 ≤ k) (hlam0 : 0 < lam) (hlam : lam ≤ Real.logb 2 q)
    (hLc : Real.logb 2 C ≤ Lc) (hc0 : 0 ≤ cv) (hc : cv ≤ c)
    (hρ1 : (q : ℝ) / (q - 1) ≤ ρ1) (hρ2 : (q : ℝ) / ((q : ℝ) - 1) ^ 2 ≤ ρ2)
    (hN : 1 ≤ N) (huN : Real.logb 2 N ≤ uN) (hlT : Real.log (uN / lam + 1) ≤ lT)
    (hG : 0 ≤ N * ((1 / 2 - 1 / (k : ℝ)) * lam - μ) - Lc -
      c * (1644935 / 10 ^ 6 * (uN / lam) - 1 + (1 + lT) * ρ1 + ρ2) - 1)
    (hD : c * (1644935 / 10 ^ 6 + ρ1) ≤
      ((1 / 2 - 1 / (k : ℝ)) * lam - μ) * N * lam * 0.6931471803)
    (x : ℝ) (hx : (N : ℝ) ≤ x) :
    0 ≤ x * ((1 / 2 - 1 / (k : ℝ)) * Real.logb 2 q - μ) - Real.logb 2 C -
      cv * gqE q (Real.logb q x) - 1 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hx1 : 1 ≤ x := hN1.trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨l2, hl2def⟩ : ∃ l2 : ℝ, l2 = 0.6931471803 := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ p2 : ℝ, p2 = 1644935 / 10 ^ 6 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 / 2 - 1 / (k : ℝ)) * lam - μ := ⟨_, rfl⟩
  rw [← hl2def, ← hA, ← hp2] at hD
  rw [← hA, ← hp2] at hG
  have hl2lo : l2 ≤ Real.log 2 := hl2def ▸ log_two_bounds.1.le
  have hl2 : 0 < l2 := by rw [hl2def]; norm_num
  have hπ : Real.pi ^ 2 / 6 ≤ p2 := hp2 ▸ pi_sq_div_six_le
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x - N := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by linarith
  -- `A ≤ a`
  have hkk : 0 ≤ 1 / 2 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
    linarith
  have hAa : A ≤ (1 / 2 - 1 / (k : ℝ)) * Real.logb 2 q - μ := by
    have := mul_le_mul_of_nonneg_left hlam hkk
    rw [hA]; linarith
  -- `y = log_q x ≤ (u_N + t/N/l₂)/lam`
  have hy0 : 0 ≤ Real.logb q x := Real.logb_nonneg (by linarith) hx1
  have hlog2x : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  have hlog2q : 0 < Real.logb 2 q := hlam0.trans_le hlam
  have hyeq : Real.logb q x = Real.logb 2 x / Real.logb 2 q := by
    have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold Real.logb; field_simp
  have hy1 : Real.logb q x ≤ Real.logb 2 x / lam := by
    rw [hyeq]; exact div_le_div_of_nonneg_left hlog2x hlam0 hlam
  have hlog2x' : Real.logb 2 x ≤ uN + t / N / l2 := by
    have := logb_two_le_add hNpos hx hl2 hl2lo
    rw [ht]; linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = t / N / l2 / lam := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have huN0 : 0 ≤ uN := (Real.logb_nonneg (by norm_num) hN1).trans huN
  have hY00 : 0 ≤ uN / lam := by positivity
  have hyY : Real.logb q x ≤ uN / lam + δ := by
    refine hy1.trans ?_
    rw [hδ, ← add_div]
    exact div_le_div_of_nonneg_right hlog2x' hlam0.le
  -- bounds for `g`
  have hρ1' : 1 ≤ (q : ℝ) / (q - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hρ'0 : 0 ≤ (q : ℝ) / ((q : ℝ) - 1) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  obtain ⟨hg0, hgle⟩ := g_bound hy0 hyY hY00 hδ0 hlT hπ hρ1' hρ1 hρ'0 hρ2
  have hg : gqE q (Real.logb q x) = Real.pi ^ 2 / 6 * Real.logb q x - 1 +
      (1 + Real.log (Real.logb q x + 1)) * ((q : ℝ) / (q - 1)) + (q : ℝ) / ((q : ℝ) - 1) ^ 2 := rfl
  rw [← hg] at hg0 hgle
  -- assemble
  have hc' : 0 ≤ c := hc0.trans hc
  have hcg := mul_le_mul hc hgle hg0 hc'
  have hxa : x * A ≤ x * ((1 / 2 - 1 / (k : ℝ)) * Real.logb 2 q - μ) :=
    mul_le_mul_of_nonneg_left hAa hx0.le
  -- the derivative part: `c δ (p2 + ρ1) ≤ t A`
  have hder : c * (δ * (p2 + ρ1)) ≤ t * A := by
    have e : c * (δ * (p2 + ρ1)) = t / (N * lam * l2) * (c * (p2 + ρ1)) := by
      rw [hδ]; field_simp
    have e2 : t * A = t / (N * lam * l2) * (A * N * lam * l2) := by
      field_simp
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left hD (by positivity)
  have hxN : x * A = N * A + t * A := by rw [ht]; ring
  linarith

/-! ### `F_k ≥ 0` from integer data -/

/-- `F_k(x) ≥ 0` for `x ≥ N` from integer data: `2^{la} ≤ q^{lb}` (`log₂ q ≥ la/lb`), an entry of
`ckTable`, `W = w₁/w₂` with `w₂^s ≤ 2^r (w₂-w₁)^s` (`c(W) ≤ r/s/W`), `N^{nb} ≤ 2^{na}`
(`log₂ N ≤ na/nb`), `T = u_N/lam + 1 ≤ tu/tv` with `tu^{tb} ≤ 2^{ta} tv^{tb}`, and the two rational
inequalities `hG`, `hD`. -/
theorem FkE_nonneg (q k : ℕ) (μ W : ℝ) (N la lb cc ca cb w1 w2 r s na nb tu tv ta tb : ℕ)
    (ρ1 ρ2 : ℝ)
    (hq : 2 ≤ q) (hk : 2 ≤ k) (hla : 0 < la) (hlb : 0 < lb) (hlq : 2 ^ la ≤ q ^ lb)
    (hck : (k, cc, ca, cb) ∈ ckTable)
    (hW : W = (w1 : ℝ) / w2) (hw1 : 0 < w1) (hw12 : w1 < w2) (hs : 0 < s)
    (hrs : w2 ^ s ≤ 2 ^ r * (w2 - w1) ^ s)
    (hρ1 : (q : ℝ) / (q - 1) ≤ ρ1) (hρ2 : (q : ℝ) / ((q : ℝ) - 1) ^ 2 ≤ ρ2)
    (hN : 1 ≤ N) (hnb : 0 < nb) (hNpow : N ^ nb ≤ 2 ^ na)
    (htv : 0 < tv) (htb : 0 < tb)
    (hT : ((na : ℝ) / nb / ((la : ℝ) / lb) + 1) * tv ≤ tu) (hTpow : tu ^ tb ≤ 2 ^ ta * tv ^ tb)
    (hG : 0 ≤ N * ((1 / 2 - 1 / (k : ℝ)) * ((la : ℝ) / lb) - μ) - ((cc : ℝ) - (ca : ℝ) / cb / k) -
      (r : ℝ) / s / ((w1 : ℝ) / w2) * (1644935 / 10 ^ 6 * ((na : ℝ) / nb / ((la : ℝ) / lb)) - 1 +
        (1 + (ta : ℝ) / tb * 0.6931471808) * ρ1 + ρ2) - 1)
    (hD : (r : ℝ) / s / ((w1 : ℝ) / w2) * (1644935 / 10 ^ 6 + ρ1) ≤
      ((1 / 2 - 1 / (k : ℝ)) * ((la : ℝ) / lb) - μ) * N * ((la : ℝ) / lb) * 0.6931471803)
    (x : ℝ) (hx : (N : ℝ) ≤ x) : 0 ≤ FkE q k μ W x := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlam0 : (0 : ℝ) < (la : ℝ) / lb := by
    have : (0 : ℝ) < la := by exact_mod_cast hla
    positivity
  have hlam : (la : ℝ) / lb ≤ Real.logb 2 q :=
    div_le_logb_of_pow hlb (by exact_mod_cast hlq)
  obtain ⟨hc0, hc⟩ := cW_le_of hW hw1 hw12 hs hrs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have huN : Real.logb 2 N ≤ (na : ℝ) / nb :=
    logb_le_div_of_pow hNpos hnb (by exact_mod_cast hNpow)
  have hlT : Real.log ((na : ℝ) / nb / ((la : ℝ) / lb) + 1) ≤ (ta : ℝ) / tb * 0.6931471808 := by
    have hT0 : 0 < (na : ℝ) / nb / ((la : ℝ) / lb) + 1 := by positivity
    have htvR : (0 : ℝ) < tv := by exact_mod_cast htv
    have h1 : (na : ℝ) / nb / ((la : ℝ) / lb) + 1 ≤ (tu : ℝ) / tv := by
      rw [le_div_iff₀ htvR]; exact hT
    refine (Real.log_le_log hT0 h1).trans (log_le_of_pow (hT0.trans_le h1) htb ?_)
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast hTpow
  have := core_ineq q k μ (cW W) (CkE k) N ((la : ℝ) / lb) ((cc : ℝ) - (ca : ℝ) / cb / k)
    ((r : ℝ) / s / ((w1 : ℝ) / w2)) ρ1 ρ2 ((na : ℝ) / nb) ((ta : ℝ) / tb * 0.6931471808)
    hq hk hlam0 hlam (logb_CkE_le_of_mem hck) hc0 hc hρ1 hρ2 hN huN hlT hG hD x hx
  unfold FkE
  exact this

/-! ### The rows of Proposition 8.3, with their rational data -/

/-- Row `q2` of Proposition 8.3 (`q = 2`, `k = 13`, `N = 16674`). -/
theorem row_q2 (x : ℝ) (hx : (16674 : ℝ) ≤ x) :
    0 ≤ FkE 2 13 ((41 : ℝ) / 100) ((Wq 2 : ℚ) : ℝ) x :=
  FkE_nonneg 2 13 ((41 : ℝ) / 100) _ 16674 1 1 1028 500266 43 3 4 2 1 1108 79 75127 5000 1466 375
    (2 : ℝ) (2 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q3div` of Proposition 8.3 (`q = 3`, `k = 11`, `N = 1575`). -/
theorem row_q3div (x : ℝ) (hx : (1575 : ℝ) ≤ x) :
    0 ≤ FkE 3 11 ((5983 : ℝ) / 10000) ((Wq 3 : ℚ) : ℝ) x :=
  FkE_nonneg 3 11 ((5983 : ℝ) / 10000) _ 1575 1054 665 309 845022 295 4 9 106 125 701 66 3851 500 162 55
    ((3 : ℝ) / 2) ((3 : ℝ) / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q3ndiv` of Proposition 8.3 (`q = 3`, `k = 12`, `N = 2769`; the row is applied for
`n ≥ 131200` only, where `M ≤ 0.62 n` is available). -/
theorem row_q3ndiv (x : ℝ) (hx : (2769 : ℝ) ≤ x) :
    0 ≤ FkE 3 12 ((31 : ℝ) / 50) ((Wq 3 : ℚ) : ℝ) x :=
  FkE_nonneg 3 12 ((31 : ℝ) / 50) _ 2769 1054 665 564 7971759 1372 4 9 106 125 1235 108 419 51 79 26
    ((3 : ℝ) / 2) ((3 : ℝ) / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q4` of Proposition 8.3 (`q = 4`, all `n`, `k = 10`, `N = 1010`). -/
theorem row_q4 (x : ℝ) (hx : (1010 : ℝ) ≤ x) :
    0 ≤ FkE 4 10 ((3 : ℝ) / 4) ((Wq 4 : ℚ) : ℝ) x :=
  FkE_nonneg 4 10 ((3 : ℝ) / 4) _ 1010 2 1 172 160406 113 1473 5000 72 143 1008 101 5991 1000 811 314
    ((4 : ℝ) / 3) ((4 : ℝ) / 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q5` of Proposition 8.3 (`q = 5`, `k = 16`, `N = 43618`). -/
theorem row_q5 (x : ℝ) (hx : (43618 : ℝ) ≤ x) :
    0 ≤ FkE 5 16 (1 : ℝ) ((Wq 5 : ℚ) : ℝ) x :=
  FkE_nonneg 5 16 (1 : ℝ) _ 43618 9297 4004 6542 6111728 65 212 625 471 788 971 63 3819 500 44 15
    ((5 : ℝ) / 4) ((5 : ℝ) / 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q7` of Proposition 8.3 (`q = 7`, `k = 9`, `N = 336`). -/
theorem row_q7 (x : ℝ) (hx : (336 : ℝ) ≤ x) :
    0 ≤ FkE 7 9 (1 : ℝ) ((Wq 7 : ℚ) : ℝ) x :=
  FkE_nonneg 7 9 (1 : ℝ) _ 336 6718 2393 97 214294 305 1683 10000 67 252 663 79 7979 2000 527 264
    ((7 : ℝ) / 6) ((7 : ℝ) / 36)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q8` of Proposition 8.3 (`q = 8`, `k = 9`, `N = 171`). -/
theorem row_q8 (x : ℝ) (hx : (171 : ℝ) ≤ x) :
    0 ≤ FkE 8 9 (1 : ℝ) ((Wq 8 : ℚ) : ℝ) x :=
  FkE_nonneg 8 9 (1 : ℝ) _ 171 3 1 97 214294 305 469 10000 107 1544 497 67 34727 10000 185 103
    ((8 : ℝ) / 7) ((8 : ℝ) / 49)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q9` of Proposition 8.3 (`q = 9`, `k = 8`, `N = 111`). -/
theorem row_q9 (x : ℝ) (hx : (111 : ℝ) ≤ x) :
    0 ≤ FkE 9 8 (1 : ℝ) ((Wq 9 : ℚ) : ℝ) x :=
  FkE_nonneg 9 8 (1 : ℝ) _ 111 2108 665 54 89747 268 503 5000 67 438 34 5 1573 500 43 26
    ((9 : ℝ) / 8) ((9 : ℝ) / 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q11` of Proposition 8.3 (`q = 11`, `k = 7`, `N = 65`). -/
theorem row_q11 (x : ℝ) (hx : (65 : ℝ) ≤ x) :
    0 ≤ FkE 11 7 (1 : ℝ) ((Wq 11 : ℚ) : ℝ) x :=
  FkE_nonneg 11 7 (1 : ℝ) _ 65 3283 949 31 22927 142 67 1000 196 1959 265 44 2741 1000 835 574
    ((11 : ℝ) / 10) ((11 : ℝ) / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q13` of Proposition 8.3 (`q = 13`, `k = 7`, `N = 45`). -/
theorem row_q13 (x : ℝ) (hx : (45 : ℝ) ≤ x) :
    0 ≤ FkE 13 7 (1 : ℝ) ((Wq 13 : ℚ) : ℝ) x :=
  FkE_nonneg 13 7 (1 : ℝ) _ 45 37 10 31 22927 142 239 5000 7 99 11 2 249 100 179 136
    ((13 : ℝ) / 12) ((13 : ℝ) / 144)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q16` of Proposition 8.3 (`q = 16`, `k = 7`, `N = 32`). -/
theorem row_q16 (x : ℝ) (hx : (32 : ℝ) ≤ x) :
    0 ≤ FkE 16 7 (1 : ℝ) ((Wq 16 : ℚ) : ℝ) x :=
  FkE_nonneg 16 7 (1 : ℝ) _ 32 4 1 31 22927 142 59 5000 3 175 5 1 9 4 55 47
    ((16 : ℝ) / 15) ((16 : ℝ) / 225)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q17` of Proposition 8.3 (`q = 17`, `k = 7`, `N = 29`). -/
theorem row_q17 (x : ℝ) (hx : (29 : ℝ) ≤ x) :
    0 ≤ FkE 17 7 (1 : ℝ) ((Wq 17 : ℚ) : ℝ) x :=
  FkE_nonneg 17 7 (1 : ℝ) _ 29 94 23 31 22927 142 279 10000 117 2866 821 169 2189 1000 26 23
    ((17 : ℝ) / 16) ((17 : ℝ) / 256)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q19` of Proposition 8.3 (`q = 19`, `k = 6`, `N = 25`). -/
theorem row_q19 (x : ℝ) (hx : (25 : ℝ) ≤ x) :
    0 ≤ FkE 19 6 (1 : ℝ) ((Wq 19 : ℚ) : ℝ) x :=
  FkE_nonneg 19 6 (1 : ℝ) _ 25 497 117 18 352365 4598 223 10000 3 92 14 3 21 10 15 14
    ((19 : ℝ) / 18) ((19 : ℝ) / 324)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q23` of Proposition 8.3 (`q = 23`, `k = 6`, `N = 19`). -/
theorem row_q23 (x : ℝ) (hx : (19 : ℝ) ≤ x) :
    0 ≤ FkE 23 6 (1 : ℝ) ((Wq 23 : ℚ) : ℝ) x :=
  FkE_nonneg 23 6 (1 : ℝ) _ 19 864 191 18 352365 4598 19 1250 4 181 17 4 97 50 22 23
    ((23 : ℝ) / 22) ((23 : ℝ) / 484)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q25` of Proposition 8.3 (`q = 25`, `k = 6`, `N = 18`). -/
theorem row_q25 (x : ℝ) (hx : (18 : ℝ) ≤ x) :
    0 ≤ FkE 25 6 (1 : ℝ) ((Wq 25 : ℚ) : ℝ) x :=
  FkE_nonneg 25 6 (1 : ℝ) _ 18 65 14 18 352365 4598 129 10000 1 53 21 5 191 100 253 271
    ((25 : ℝ) / 24) ((25 : ℝ) / 576)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q27` of Proposition 8.3 (`q = 27`, `k = 6`, `N = 16`). -/
theorem row_q27 (x : ℝ) (hx : (16 : ℝ) ≤ x) :
    0 ≤ FkE 27 6 (1 : ℝ) ((Wq 27 : ℚ) : ℝ) x :=
  FkE_nonneg 27 6 (1 : ℝ) _ 16 252 53 18 352365 4598 11 1000 665 41673 4 1 921 500 15 17
    ((27 : ℝ) / 26) ((27 : ℝ) / 676)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q29` of Proposition 8.3 (`q = 29`, `k = 6`, `N = 15`). -/
theorem row_q29 (x : ℝ) (hx : (15 : ℝ) ≤ x) :
    0 ≤ FkE 29 6 (1 : ℝ) ((Wq 29 : ℚ) : ℝ) x :=
  FkE_nonneg 29 6 (1 : ℝ) _ 15 34 7 18 352365 4598 6 625 6 431 43 11 361 200 6 7
    ((29 : ℝ) / 28) ((29 : ℝ) / 784)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q31` of Proposition 8.3 (`q = 31`, `k = 6`, `N = 14`). -/
theorem row_q31 (x : ℝ) (hx : (14 : ℝ) ≤ x) :
    0 ≤ FkE 31 6 (1 : ℝ) ((Wq 31 : ℚ) : ℝ) x :=
  FkE_nonneg 31 6 (1 : ℝ) _ 14 540 109 18 352365 4598 21 2500 1 82 99 26 1769 1000 14 17
    ((31 : ℝ) / 30) ((31 : ℝ) / 900)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide)
    (by norm_num [Wq]) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x (by exact_mod_cast hx)

/-- Row `q ≥ 32` of Proposition 8.3 (`k = 6`, `N = 14`, `W = 0.0118`), with `log₂ q ≥ 5`,
`q/(q-1) ≤ 32/31`, `q/(q-1)² ≤ 32/961` (the values at `q = 32`), as in the paper. -/
theorem row_big (q : ℕ) (hq : 32 ≤ q) (x : ℝ) (hx : (14 : ℝ) ≤ x) :
    0 ≤ FkE q 6 1 (((0.0118 : ℚ)) : ℝ) x := by
  have hq' : (32 : ℝ) ≤ q := by exact_mod_cast hq
  refine FkE_nonneg q 6 1 _ 14 5 1 18 352365 4598 59 5000 1 58 99 26 177 100 5 6
    ((32 : ℝ) / 31) ((32 : ℝ) / 961)
    (by omega) (by norm_num) (by norm_num) (by norm_num) ?_ (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    ?_ ?_ (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) x hx
  · rw [pow_one]; exact le_trans (by norm_num) hq
  · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  · rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hq') (by linarith : (0 : ℝ) ≤ 32 * q - 1)]

end Analytic

end MorganMullen
