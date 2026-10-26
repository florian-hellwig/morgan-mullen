import MorganMullen.Sec8Corollary

/-!
# Section 8: primitive completely normal elements (Corollary 8.9)

**Corollary 8.9** (paper). Let
`θ = φ(q^n - 1)/(q^n - 1)`, `ω = ω(q^n - 1)`, `L` as in Theorem 4.2, `W = W(q)` as in Theorem 7.8 and
`c(W)` as in Theorem 8.1; `M` is the number of essential conditions and `S` the total weight of the
essential conditions of codimension `≥ 2`.

* **(a)** For every pair `(q, n)`,
  `|PCN_q(n) - θ CN_q(n)| ≤ θ 2^ω q^{n/2} L ≤ 2^{ω + M + c(W) S} q^{-n/2} θ CN_q(n)`
  (`pcn_sub_theta_cn_abs_le`, `pcn_error_le_star`, both together `pcn_theta_cn`). The first inequality
  uses no computation.
* **(b)** `PCN_q(n) / (θ CN_q(n)) → 1` as `q^n → ∞`: for every `ε > 0` there is an `X` such that the relative
  error is `< ε` for all pairs with `q^n ≥ X` (`pcn_ratio_tendsto_one`).

Proof of (a), as in the paper: `θ CN_q(n) = θ (q^n - 1) δ_n + θ δ_n` and Theorem 4.2 (a) give
`|PCN_q(n) - θ CN_q(n)| ≤ θ β (L - δ_n) + θ δ_n ≤ θ β L ≤ θ 2^ω q^{n/2} L`; then `L ≤ 2^M (1 - 1/q)^{M_1}`
(Theorem 4.2) and `(1 - 1/q)^{M_1} ≤ 2^{c(W) S} δ_n` (Theorems 7.8 and 8.1 (a)).

Proof of (b), as in the paper (`CN_q(n) > 0` by Corollary 8.8):
* *large `n`* (`relErr_lt_large`): for `n ≥ 131200`, `M ≤ λ_q n` with `(1/2 - 1/16) log₂ q - λ_q ≥ 1/100`
  (`exists_lambda`: Proposition 6.5 for `q ≤ 4`, Corollary 6.4 for `q ≥ 5`), `ω ≤ log₂ C₁₆ + (n/16) log₂ q`
  (Lemma 8.2 (a)), `S ≤ g_q(log_q n) ≤ g_2(log₂ n)` (Lemma 8.2 (b), `gq_logb_le`) and `c(W) ≤ c(3/4) = 8/3`
  (`cW_le_cW`), so the relative error is `< 2^{-h(n)}`, `h(n) = n/100 - log₂ C₁₆ - (8/3) g_2(log₂ n) - 1`
  (`hPCN`), and `h(n) → ∞` (`exists_hPCN_ge`);
* *bounded `n`* (`relErr_le_bounded`): `L ≤ 2^M ≤ 2^n`, `CN_q(n) ≥ q^n (1 - 1/q)^{n'} ≥ q^n 2^{-n}` and
  `2^ω ≤ C₄ q^{n/4}` bound the relative error by `C₄ 4^n q^{-n/4}`;
* finally, if `q^n ≥ Q^N`, then `n ≥ N` or `q ≥ Q`.
-/

set_option linter.unusedSectionVars false

universe u v

namespace MorganMullen

open Module Finset

/-! ### Real-analytic facts -/

/-- `|P/(θ C) - 1| ≤ B` if `|P - θ C| ≤ B θ C` and `θ C > 0`. -/
lemma abs_div_sub_one_le {P θ C B : ℝ} (hA : 0 < θ * C) (h : |P - θ * C| ≤ B * θ * C) :
    |P / (θ * C) - 1| ≤ B := by
  rw [div_sub_one hA.ne', abs_div, abs_of_pos hA, div_le_iff₀ hA, ← mul_assoc]
  exact h

/-- `c(W) = log₂(1/(1-W))/W` is increasing on `(0, 1)` (concavity of `log(1 - w)`,
`rpow_div_le_one_sub`). -/
lemma cW_le_cW {W W' : ℝ} (hW0 : 0 < W) (hWW' : W ≤ W') (hW'1 : W' < 1) : cW W ≤ cW W' := by
  have hW'0 : 0 < W' := lt_of_lt_of_le hW0 hWW'
  have h1W' : 0 < 1 - W' := by linarith
  have h := rpow_div_le_one_sub hW'0 hW'1 hW0.le hWW'
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos h1W' _) h
  rw [Real.log_rpow h1W'] at hlog
  -- `W log(1 - W') ≤ W' log(1 - W)`
  have hlog' : W * Real.log (1 - W') ≤ W' * Real.log (1 - W) := by
    have := mul_le_mul_of_nonneg_left hlog hW'0.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hW'0.ne'] at this
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold cW Real.logb
  simp only [one_div, Real.log_inv]
  rw [div_div, div_div, div_le_div_iff₀ (mul_pos hl2 hW0) (mul_pos hl2 hW'0)]
  linarith [mul_le_mul_of_nonneg_left hlog' hl2.le]

/-- `c(3/4) = 8/3`. -/
lemma cW_three_quarters : cW (3 / 4) = 8 / 3 := by
  unfold cW
  rw [show (1 : ℝ) / (1 - 3 / 4) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- `c(W) ≥ 0` for `0 < W < 1`. -/
lemma cW_nonneg {W : ℝ} (hW0 : 0 < W) (hW1 : W < 1) : 0 ≤ cW W := by
  unfold cW
  refine div_nonneg (Real.logb_nonneg (by norm_num) ?_) hW0.le
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `W(q) ≤ 3/4` (Theorem 7.8). -/
lemma Wq_le_three_quarters (q : ℕ) : (Wq q : ℝ) ≤ 3 / 4 := by
  have h := Model.Wq_le_Wb q
  have h' : Model.Wb q ≤ 3 / 4 := by unfold Model.Wb; split_ifs <;> norm_num
  linarith

/-- `C_k > 0`. -/
lemma Ck_pos (k : ℕ) : 0 < Ck k := by
  unfold Ck
  refine Finset.prod_pos fun ℓ hℓ => ?_
  have : (0 : ℝ) < ℓ := by exact_mod_cast (Finset.mem_filter.1 hℓ).2.pos
  positivity

/-- `g_2(y) = (π²/6) y + 3 + 2 ln(y + 1)`. -/
lemma gq_two (y : ℝ) : gq 2 y = Real.pi ^ 2 / 6 * y + 3 + 2 * Real.log (y + 1) := by
  unfold gq
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
  ring

/-- `g_q(log_q n) ≤ g_2(log₂ n)` for `q ≥ 2`, `n ≥ 1`: each term of `g_q(log_q n)` decreases with `q`. -/
lemma gq_logb_le (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    gq q (Real.logb q n) ≤ gq 2 (Real.logb 2 n) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq'
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hx0 : 0 ≤ Real.logb q n := div_nonneg hln (hl2.trans_le hlq).le
  have hxy : Real.logb q n ≤ Real.logb 2 n := div_le_div_of_nonneg_left hln hl2 hlq
  have hlog : Real.log (Real.logb q n + 1) ≤ Real.log (Real.logb 2 n + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog0 : 0 ≤ Real.log (Real.logb q n + 1) := Real.log_nonneg (by linarith)
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hr1 : (q : ℝ) / (q - 1) ≤ 2 := by rw [div_le_iff₀ hq1]; linarith
  have hr2 : (q : ℝ) / ((q : ℝ) - 1) ^ 2 ≤ 2 := by rw [div_le_iff₀ (pow_pos hq1 2)]; nlinarith
  have hpi : 0 ≤ Real.pi ^ 2 / 6 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hxy hpi
  have h2 := mul_le_mul_of_nonneg_left hr1 (by linarith : (0 : ℝ) ≤ 1 + Real.log (Real.logb q n + 1))
  rw [gq_two]
  unfold gq
  linarith

/-- `log₂ q ≥ a/b` if `2^a ≤ q^b`. -/
lemma logb_two_ge_of_pow_le {q a b : ℕ} (hb : 0 < b) (h : 2 ^ a ≤ q ^ b) :
    (a : ℝ) / b ≤ Real.logb 2 q := by
  have h' : (2 : ℝ) ^ a ≤ (q : ℝ) ^ b := by exact_mod_cast h
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h'
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hl
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  linarith

/-- `S ≥ 0`. -/
lemma sumS_nonneg (q n : ℕ) [NeZero n] : (0 : ℝ) ≤ Model.sumS q n := by
  have : (0 : ℚ) ≤ Model.sumS q n := Finset.sum_nonneg fun C _ => by positivity
  exact_mod_cast this

/-- The constants `λ_q` of the proof of Corollary 8.9 (b): for `n ≥ 131200`, `M ≤ λ n` with
`(1/2 - 1/16) log₂ q - λ ≥ 1/100`; `λ = 0.41, 0.62, 0.75` for `q = 2, 3, 4` (Proposition 6.5) and `λ = 1`
for `q ≥ 5` (Corollary 6.4). -/
lemma exists_lambda {q n : ℕ} [NeZero n] (hq : IsPrimePow q) (hn : 131200 ≤ n) :
    ∃ μ : ℝ, (Model.numM q n : ℝ) ≤ μ * n ∧ 1 / 100 ≤ (1 / 2 - 1 / 16) * Real.logb 2 q - μ := by
  have hq2 : 2 ≤ q := hq.two_le
  rcases (by omega : q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q) with rfl | rfl | rfl | hq5
  · refine ⟨41 / 100, ?_, ?_⟩
    · have h := (Rat.cast_le (K := ℝ)).mpr (Model.numM_le_q2 (n := n) (by omega))
      push_cast at h
      exact h
    · rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, Real.logb_self_eq_one (by norm_num)]
      norm_num
  · refine ⟨62 / 100, ?_, ?_⟩
    · have hn0 : (0 : ℝ) ≤ n := by positivity
      by_cases h3 : 3 ∣ n
      · have h := (Rat.cast_le (K := ℝ)).mpr (Model.numM_le_q3_div (n := n) h3)
        push_cast at h
        linarith
      · have h := (Rat.cast_le (K := ℝ)).mpr (Model.numM_le_q3_ndiv_large (n := n) h3 hn)
        push_cast at h
        exact h
    · have h := logb_two_ge_of_pow_le (q := 3) (a := 3) (b := 2) (by norm_num) (by norm_num)
      rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, show ((2 : ℕ) : ℝ) = 2 by norm_num] at h
      rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]
      linarith
  · refine ⟨3 / 4, ?_, ?_⟩
    · have h := (Rat.cast_le (K := ℝ)).mpr (Model.numM_le_q4 (n := n) (by omega))
      push_cast at h
      exact h
    · have h := logb_two_ge_of_pow_le (q := 4) (a := 2) (b := 1) (by norm_num) (by norm_num)
      rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, show ((2 : ℕ) : ℝ) = 2 by norm_num,
        show ((1 : ℕ) : ℝ) = 1 by norm_num] at h
      rw [show ((4 : ℕ) : ℝ) = 4 by norm_num]
      linarith
  · refine ⟨1, ?_, ?_⟩
    · have h : (Model.numM q n : ℝ) ≤ n := by exact_mod_cast Model.numM_le_n hq
      linarith
    · have h := logb_two_ge_of_pow_le (q := 5) (a := 37) (b := 16) (by norm_num) (by norm_num)
      have h5 : Real.logb 2 ((5 : ℕ) : ℝ) ≤ Real.logb 2 q :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hq5)
      rw [show ((37 : ℕ) : ℝ) = 37 by norm_num, show ((16 : ℕ) : ℝ) = 16 by norm_num] at h
      have h' := h.trans h5
      linarith

/-- `h(n) = n/100 - log₂ C₁₆ - (8/3) g_2(log₂ n) - 1` (proof of Corollary 8.9 (b)). -/
noncomputable def hPCN (n : ℕ) : ℝ :=
  n / 100 - Real.logb 2 (Ck 16) - 8 / 3 * gq 2 (Real.logb 2 n) - 1

/-- `h(n) → ∞`: for every `T` there is an `N` with `h(n) ≥ T` for all `n ≥ N` (via
`g_2(log₂ n) ≤ (14/3) log₂ n + 3` and `log₂ n ≤ 4 √n`). -/
lemma exists_hPCN_ge (T : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → T ≤ hPCN n := by
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = 5100 + |T| + |Real.logb 2 (Ck 16)| + 9 := ⟨_, rfl⟩
  have hT := le_abs_self T
  have hc := le_abs_self (Real.logb 2 (Ck 16))
  have hTa := abs_nonneg T
  have hca := abs_nonneg (Real.logb 2 (Ck 16))
  have ht₀0 : 0 ≤ t₀ := by linarith
  refine ⟨⌈t₀ ^ 2⌉₊, fun n hn => ?_⟩
  have hn' : t₀ ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have hst : t₀ ≤ Real.sqrt n := by
    have := Real.sqrt_le_sqrt hn'
    rwa [Real.sqrt_sq ht₀0] at this
  have hn1 : (1 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ t₀ ^ 2 := one_le_pow₀ (by linarith)
    linarith
  -- `log n ≤ 2 √n` and `log₂ n ≤ 4 √n`
  have hlog : Real.log n ≤ 2 * Real.sqrt n := by
    have h := Real.log_le_rpow_div hn0 (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  -- `log 2 ≥ 1/2`, from `log(1/2) ≤ 1/2 - 1`
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [one_div, Real.log_inv] at h
    linarith
  have hlogb : Real.logb 2 n ≤ 4 * Real.sqrt n := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have := mul_le_mul_of_nonneg_left hl2 (Real.sqrt_nonneg (n : ℝ))
    linarith
  have hlogb0 : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hn1
  -- `g_2(y) ≤ (14/3) y + 3` for `y ≥ 0`
  have hg : gq 2 (Real.logb 2 n) ≤ 14 / 3 * Real.logb 2 n + 3 := by
    rw [gq_two]
    have h1 := Real.log_le_sub_one_of_pos (x := Real.logb 2 n + 1) (by linarith)
    have hpi : Real.pi ^ 2 ≤ 16 := by
      have := Real.pi_le_four
      have := Real.pi_pos
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right hpi hlogb0
    linarith
  have hkey : 0 ≤ (Real.sqrt n - 5100) * Real.sqrt n :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  unfold hPCN
  linarith

/-- `θ > 0`. -/
lemma thetaFrac_pos (E : Type*) [Field E] [Fintype E] : 0 < thetaFrac (Fintype.card E - 1) := by
  have hQ2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
  unfold thetaFrac
  apply div_pos
  · exact_mod_cast Nat.totient_pos.2 (by omega)
  · exact_mod_cast (by omega : 0 < Fintype.card E - 1)

section Setting

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

local notation "q" => Fintype.card F
local notation "n" => Module.finrank F E

/-- `L ≥ 0`. -/
lemma lFactor_nonneg : 0 ≤ lFactor F E := by
  unfold lFactor
  refine Finset.prod_nonneg fun C _ => ?_
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Fintype.card_pos
  have : ((q : ℝ) ^ Model.codim q n C)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq1)
  linarith

/-- `CN_q(n) > 0` (Corollary 8.8). -/
lemma cnCount_pos : (0 : ℝ) < cnCount F E := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (FiniteField.isPrimePow_card F).two_le
  have ha : 0 < 1 - 1 / (q : ℝ) := by
    have : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have h := delta_ge_hachenberger (F := F) (E := E)
  have hQ : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  exact (div_pos_iff_of_pos_right hQ).1 (lt_of_lt_of_le (pow_pos ha _) h)

/-- **Corollary 8.9 (a)**, first inequality (no computation):
`|PCN_q(n) - θ CN_q(n)| ≤ θ 2^ω q^{n/2} L`. As in the paper, from Theorem 4.2 (a), since
`θ CN_q(n) = θ (q^n - 1) δ_n + θ δ_n`, `β ≥ 1` and `β ≤ 2^ω q^{n/2}`. -/
theorem pcn_sub_theta_cn_abs_le :
    |(pcnCount F E : ℝ) - thetaFrac (Fintype.card E - 1) * cnCount F E| ≤
      thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
        Real.sqrt (Fintype.card E) * lFactor F E := by
  have key := pcn_sub_main_abs_le (F := F) (E := E)
  have hQ2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
  have hQpos : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hθ : 0 ≤ thetaFrac (Fintype.card E - 1) := (thetaFrac_pos E).le
  have hT1 : 1 ≤ twoPowOmega (Fintype.card E - 1) := by
    unfold twoPowOmega; exact one_le_pow₀ (by norm_num)
  have hsq : 1 ≤ Real.sqrt (Fintype.card E) := Real.one_le_sqrt.2 (by exact_mod_cast (by omega : 1 ≤ Fintype.card E))
  have hL0 : 0 ≤ lFactor F E := lFactor_nonneg
  have hCN : (cnCount F E : ℝ) =
      Fintype.card E * ((cnCount F E : ℝ) / Fintype.card E) := (mul_div_cancel₀ _ hQpos.ne').symm
  have hδ0 : 0 ≤ (cnCount F E : ℝ) / Fintype.card E := by positivity
  rw [hCN]
  set θ := thetaFrac (Fintype.card E - 1) with hθdef
  set T := twoPowOmega (Fintype.card E - 1) with hTdef
  set s := Real.sqrt (Fintype.card E) with hsdef
  set δ := (cnCount F E : ℝ) / Fintype.card E with hδdef
  set Q : ℝ := (Fintype.card E : ℝ) with hQdef
  set L := lFactor F E with hLdef
  -- `1 ≤ β ≤ 2^ω q^{n/2}`
  have hβ1 : 0 ≤ (T - 1) * s := mul_nonneg (by linarith) (by linarith)
  have hβ2 : 0 ≤ T * s - (1 + (T - 1) * s) := by linarith
  have h1 : 0 ≤ θ * δ * ((T - 1) * s) := mul_nonneg (mul_nonneg hθ hδ0) hβ1
  have h2 : 0 ≤ θ * (T * s - (1 + (T - 1) * s)) * L := mul_nonneg (mul_nonneg hθ hβ2) hL0
  have h3 : 0 ≤ θ * δ := mul_nonneg hθ hδ0
  obtain ⟨k1, k2⟩ := abs_le.mp key
  rw [abs_le]
  constructor <;> linarith

/-- **Corollary 8.9 (a)**, second inequality:
`θ 2^ω q^{n/2} L ≤ 2^{ω + M + c(W) S} q^{-n/2} θ CN_q(n)` with `W = W(q)`. As in the paper, from
`L ≤ 2^M (1 - 1/q)^{M_1}` (Theorem 4.2) and `(1 - 1/q)^{M_1} ≤ 2^{c(W) S} δ_n` (Theorems 7.8 and 8.1 (a)). -/
theorem pcn_error_le_star :
    thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
        Real.sqrt (Fintype.card E) * lFactor F E ≤
      (2 : ℝ) ^ (((Fintype.card E - 1).primeFactors.card : ℝ) + (Model.numM q n : ℝ) +
          cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) / Real.sqrt (Fintype.card E) *
        thetaFrac (Fintype.card E - 1) * cnCount F E := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  obtain ⟨hW0, hW1⟩ := Wq_pos_lt_one q
  have hW0' : (0 : ℝ) < Wq q := by exact_mod_cast hW0
  have hW1' : (Wq q : ℝ) < 1 := by exact_mod_cast hW1
  have hδ := delta_ge_deltaStar (F := F) (E := E) (Wq q) hW0' hW1'
    (fun K hK hK2 => by exact_mod_cast weight_le_Wq _ _ hq hK hK2)
  have hL := lFactor_le (F := F) (E := E)
  have hQpos : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hs0 : 0 < Real.sqrt (Fintype.card E) := Real.sqrt_pos.2 hQpos
  have hθ := thetaFrac_pos E
  have hT0 : 0 ≤ twoPowOmega (Fintype.card E - 1) := by unfold twoPowOmega; positivity
  have hW' : 0 < 1 - (Wq q : ℝ) := by linarith
  -- `(1 - W)^{S/W} = 2^{-c(W) S}`
  have hW2 : (1 - (Wq q : ℝ)) ^ ((Model.sumS q n : ℝ) / Wq q) =
      (2 : ℝ) ^ (-(cW (Wq q : ℝ) * (Model.sumS q n : ℝ))) := by
    rw [show -(cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) =
        Real.logb 2 (1 - (Wq q : ℝ)) * ((Model.sumS q n : ℝ) / Wq q) by
          unfold cW; rw [one_div, Real.logb_inv]; ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hW']
  have h2 : (2 : ℝ) ^ (-(cW (Wq q : ℝ) * (Model.sumS q n : ℝ))) *
      (2 : ℝ) ^ (cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  -- `(1 - 1/q)^{M_1} ≤ 2^{c(W) S} δ_n`
  have haM : (1 - 1 / (q : ℝ)) ^ ((Model.essConds q n).filter fun C => Model.codim q n C = 1).card ≤
      (2 : ℝ) ^ (cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) * ((cnCount F E : ℝ) / Fintype.card E) := by
    have h := mul_le_mul_of_nonneg_right hδ
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (cW (Wq q : ℝ) * (Model.sumS q n : ℝ))).le
    rw [hW2, mul_assoc, h2, mul_one] at h
    linarith
  have hexp : (2 : ℝ) ^ (((Fintype.card E - 1).primeFactors.card : ℝ) + (Model.numM q n : ℝ) +
      cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) =
      twoPowOmega (Fintype.card E - 1) * 2 ^ Model.numM q n *
        (2 : ℝ) ^ (cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_natCast, Real.rpow_natCast]
    rfl
  have hCN : (cnCount F E : ℝ) = Real.sqrt (Fintype.card E) * Real.sqrt (Fintype.card E) *
      ((cnCount F E : ℝ) / Fintype.card E) := by
    rw [Real.mul_self_sqrt hQpos.le, mul_div_cancel₀ _ hQpos.ne']
  rw [hexp, hCN]
  have hA : 0 ≤ thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
      Real.sqrt (Fintype.card E) := mul_nonneg (mul_nonneg hθ.le hT0) hs0.le
  calc thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
        Real.sqrt (Fintype.card E) * lFactor F E
      ≤ thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
          Real.sqrt (Fintype.card E) * (2 ^ Model.numM q n *
            (1 - 1 / (q : ℝ)) ^ ((Model.essConds q n).filter fun C => Model.codim q n C = 1).card) :=
        mul_le_mul_of_nonneg_left hL hA
    _ ≤ thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
          Real.sqrt (Fintype.card E) * (2 ^ Model.numM q n *
            ((2 : ℝ) ^ (cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) *
              ((cnCount F E : ℝ) / Fintype.card E))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left haM (by positivity)) hA
    _ = twoPowOmega (Fintype.card E - 1) * 2 ^ Model.numM q n *
          (2 : ℝ) ^ (cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) / Real.sqrt (Fintype.card E) *
          thetaFrac (Fintype.card E - 1) * (Real.sqrt (Fintype.card E) *
            Real.sqrt (Fintype.card E) * ((cnCount F E : ℝ) / Fintype.card E)) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hs0.ne']
        ring

/-- **Corollary 8.9 (a)**: `|PCN_q(n) - θ CN_q(n)| ≤ θ 2^ω q^{n/2} L ≤ 2^{ω + M + c(W) S} q^{-n/2} θ CN_q(n)`,
`W = W(q)`. -/
theorem pcn_theta_cn :
    |(pcnCount F E : ℝ) - thetaFrac (Fintype.card E - 1) * cnCount F E| ≤
        thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
          Real.sqrt (Fintype.card E) * lFactor F E ∧
      thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
          Real.sqrt (Fintype.card E) * lFactor F E ≤
        (2 : ℝ) ^ (((Fintype.card E - 1).primeFactors.card : ℝ) + (Model.numM q n : ℝ) +
            cW (Wq q : ℝ) * (Model.sumS q n : ℝ)) / Real.sqrt (Fintype.card E) *
          thetaFrac (Fintype.card E - 1) * cnCount F E :=
  ⟨pcn_sub_theta_cn_abs_le, pcn_error_le_star⟩

/-- The large-`n` step of the proof of Corollary 8.9 (b): for `n ≥ 131200` the relative error
`|PCN_q(n)/(θ CN_q(n)) - 1|` is less than `2^{-h(n)}`, for every `q`. -/
theorem relErr_lt_large (hn : 131200 ≤ n) :
    |(pcnCount F E : ℝ) / (thetaFrac (Fintype.card E - 1) * cnCount F E) - 1| <
      (2 : ℝ) ^ (-hPCN n) := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hq2 : 2 ≤ q := hq.two_le
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hqpos : (0 : ℝ) < q := by linarith
  have hn1 : 1 ≤ n := by omega
  have hA : 0 < thetaFrac (Fintype.card E - 1) * (cnCount F E : ℝ) :=
    mul_pos (thetaFrac_pos E) cnCount_pos
  -- (a): the relative error is at most `2^{ω + M + c(W) S} q^{-n/2}`
  have hrel := abs_div_sub_one_le hA
    ((pcn_sub_theta_cn_abs_le (F := F) (E := E)).trans (pcn_error_le_star (F := F) (E := E)))
  -- `c(W) S ≤ (8/3) g_2(log₂ n)`
  obtain ⟨hW0, -⟩ := Wq_pos_lt_one q
  have hW0' : (0 : ℝ) < Wq q := by exact_mod_cast hW0
  have hc : cW (Wq q : ℝ) ≤ 8 / 3 := by
    rw [← cW_three_quarters]
    exact cW_le_cW hW0' (Wq_le_three_quarters q) (by norm_num)
  have hS0 : (0 : ℝ) ≤ Model.sumS q n := sumS_nonneg q n
  have hS : (Model.sumS q n : ℝ) ≤ gq 2 (Real.logb 2 n) := by
    obtain ⟨h1, h2⟩ := sumS_le_gq q n hq
    exact (h1.trans h2).trans (gq_logb_le q n hq2 hn1)
  have hcS : cW (Wq q : ℝ) * Model.sumS q n ≤ 8 / 3 * gq 2 (Real.logb 2 n) :=
    mul_le_mul hc hS hS0 (by norm_num)
  -- `M ≤ λ n`, `(1/2 - 1/16) log₂ q - λ ≥ 1/100`
  obtain ⟨μ, hμ1, hμ2⟩ := exists_lambda hq hn
  have hnμ : (n : ℝ) * (1 / 100) ≤ n * ((1 / 2 - 1 / 16) * Real.logb 2 q - μ) :=
    mul_le_mul_of_nonneg_left hμ2 (by positivity)
  -- `ω ≤ log₂ C₁₆ + (n/16) log₂ q`
  have hE : Fintype.card E = q ^ n := Module.card_eq_pow_finrank
  have hω : ((Fintype.card E - 1).primeFactors.card : ℝ) ≤
      Real.logb 2 (Ck 16) + n / 16 * Real.logb 2 q := by
    rw [hE]
    have h := omega_le_logb q n 16 hq2 hn1 (by norm_num)
    rw [show ((16 : ℕ) : ℝ) = 16 by norm_num] at h
    exact h
  have hexp : ((Fintype.card E - 1).primeFactors.card : ℝ) + (Model.numM q n : ℝ) +
      cW (Wq q : ℝ) * (Model.sumS q n : ℝ) - (n : ℝ) / 2 * Real.logb 2 q ≤ -hPCN n - 1 := by
    unfold hPCN
    linarith
  -- `q^{n/2} = 2^{(n/2) log₂ q}`
  have hsq : Real.sqrt (Fintype.card E : ℝ) = (2 : ℝ) ^ ((n : ℝ) / 2 * Real.logb 2 q) := by
    rw [hE]
    push_cast
    rw [show (n : ℝ) / 2 * Real.logb 2 q = Real.logb 2 q * ((n : ℝ) / 2) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hqpos,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
    congr 1
    ring
  rw [hsq, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)] at hrel
  calc _ ≤ _ := hrel
    _ ≤ (2 : ℝ) ^ (-hPCN n - 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ < (2 : ℝ) ^ (-hPCN n) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)

/-- The bounded-`n` step of the proof of Corollary 8.9 (b): the relative error is at most
`C₄ 4^n q^{-n/4}`, by the first inequality of (a), `L ≤ 2^M ≤ 2^n` (Theorem 4.2, Corollary 6.4),
`CN_q(n) ≥ q^n (1 - 1/q)^{n'} ≥ q^n 2^{-n}` (Corollary 8.8) and `2^ω ≤ C₄ q^{n/4}` (Lemma 8.2 (a)). -/
theorem relErr_le_bounded :
    |(pcnCount F E : ℝ) / (thetaFrac (Fintype.card E - 1) * cnCount F E) - 1| ≤
      Ck 4 * 4 ^ n / (Fintype.card E : ℝ) ^ ((1 : ℝ) / 4) := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hθ := thetaFrac_pos E
  have hA : 0 < thetaFrac (Fintype.card E - 1) * (cnCount F E : ℝ) := mul_pos hθ cnCount_pos
  have hQ2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
  have hQpos : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (Fintype.card E : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hQpos _
  have hs4 : s ^ 4 = Fintype.card E := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hQpos.le]
    norm_num
  have hsq : Real.sqrt (Fintype.card E) = s ^ 2 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hQpos.le, Real.sqrt_eq_rpow]
    norm_num
  -- `2^ω ≤ C₄ (q^n)^{1/4}` (Lemma 8.2 (a) with `k = 4`)
  have hT : twoPowOmega (Fintype.card E - 1) ≤ Ck 4 * s := by
    have h := two_pow_omega_le (Fintype.card E - 1) 4 (by omega) (by norm_num)
    rw [show ((4 : ℕ) : ℝ) = 4 by norm_num] at h
    have hle : ((Fintype.card E - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ s := by
      rw [hs]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.sub_le _ 1) (by norm_num)
    exact h.trans (mul_le_mul_of_nonneg_left hle (Ck_pos 4).le)
  -- `L ≤ 2^M ≤ 2^n`
  have hL : lFactor F E ≤ 2 ^ n := by
    have ha0 : 0 ≤ 1 - 1 / (q : ℝ) := by
      have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have ha1 : 1 - 1 / (q : ℝ) ≤ 1 := by
      have : 0 ≤ 1 / (q : ℝ) := by positivity
      linarith
    calc lFactor F E ≤ 2 ^ Model.numM q n *
          (1 - 1 / (q : ℝ)) ^ ((Model.essConds q n).filter fun C => Model.codim q n C = 1).card :=
          lFactor_le
      _ ≤ 2 ^ Model.numM q n * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ ha0 ha1) (by positivity)
      _ ≤ 2 ^ n := by rw [mul_one]; exact pow_le_pow_right₀ (by norm_num) (Model.numM_le_n hq)
  -- `CN_q(n) ≥ q^n (1 - 1/q)^{n'} ≥ q^n 2^{-n}` (Corollary 8.8)
  have hCNge : (Fintype.card E : ℝ) * (1 / 2) ^ n ≤ cnCount F E := by
    have h := delta_ge_hachenberger (F := F) (E := E)
    rw [le_div_iff₀ hQpos] at h
    have hhalf : (1 / 2 : ℝ) ≤ 1 - 1 / (q : ℝ) := by
      have : 1 / (q : ℝ) ≤ 1 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq2'
      linarith
    have h2 : (1 / 2 : ℝ) ^ n ≤ (1 - 1 / (q : ℝ)) ^ Model.nfree q n :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (nfree_le q n)).trans
        (pow_le_pow_left₀ (by norm_num) hhalf _)
    linarith [mul_le_mul_of_nonneg_left h2 hQpos.le]
  -- combine with the first inequality of (a)
  rw [← hs]
  apply abs_div_sub_one_le hA
  have h42 : (4 : ℝ) ^ n * (1 / 2) ^ n = 2 ^ n := by rw [← mul_pow]; norm_num
  have hB0 : 0 ≤ Ck 4 * 4 ^ n / s * thetaFrac (Fintype.card E - 1) :=
    mul_nonneg (div_nonneg (mul_nonneg (Ck_pos 4).le (by positivity)) hs0.le) hθ.le
  calc |(pcnCount F E : ℝ) - thetaFrac (Fintype.card E - 1) * cnCount F E|
      ≤ thetaFrac (Fintype.card E - 1) * twoPowOmega (Fintype.card E - 1) *
          Real.sqrt (Fintype.card E) * lFactor F E := pcn_sub_theta_cn_abs_le
    _ ≤ thetaFrac (Fintype.card E - 1) * (Ck 4 * s) * s ^ 2 * 2 ^ n := by
        rw [hsq]
        have e1 := mul_le_mul_of_nonneg_left hT hθ.le
        have e2 := mul_le_mul_of_nonneg_right e1 (by positivity : (0 : ℝ) ≤ s ^ 2)
        exact mul_le_mul e2 hL lFactor_nonneg
          (mul_nonneg (mul_nonneg hθ.le (mul_nonneg (Ck_pos 4).le hs0.le)) (by positivity))
    _ = Ck 4 * 4 ^ n / s * thetaFrac (Fintype.card E - 1) *
          ((Fintype.card E : ℝ) * (1 / 2) ^ n) := by
        rw [← hs4, div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hs0.ne',
          show Ck 4 * 4 ^ n * thetaFrac (Fintype.card E - 1) * (s ^ 4 * (1 / 2) ^ n) =
            Ck 4 * thetaFrac (Fintype.card E - 1) * s ^ 4 * ((4 : ℝ) ^ n * (1 / 2) ^ n) by ring,
          h42]
        ring
    _ ≤ Ck 4 * 4 ^ n / s * thetaFrac (Fintype.card E - 1) * cnCount F E :=
        mul_le_mul_of_nonneg_left hCNge hB0

end Setting

/-- **Corollary 8.9 (b)**:
`PCN_q(n) / (θ CN_q(n)) → 1` as `q^n → ∞`, i.e. for every `ε > 0` there is an `X` such that
`|PCN_q(n) / (θ CN_q(n)) - 1| < ε` for all finite field extensions `E/F` with `|E| = q^n ≥ X`. -/
theorem pcn_ratio_tendsto_one :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ (F : Type u) (E : Type v) [Field F] [Fintype F] [Field E]
      [Fintype E] [Algebra F E], X ≤ Fintype.card E →
        |(pcnCount F E : ℝ) / (thetaFrac (Fintype.card E - 1) * cnCount F E) - 1| < ε := by
  intro ε hε
  -- large `n`: `h(n) ≥ log₂(1/ε)` for `n ≥ N`
  obtain ⟨N₁, hN₁⟩ := exists_hPCN_ge (Real.logb 2 (1 / ε))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max N₁ 131200 := ⟨_, rfl⟩
  -- bounded `n`: `C₄ 4^N q^{-1/4} < ε` for `q ≥ Q₀`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Ck 4 * 4 ^ N / ε := ⟨_, rfl⟩
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : ℕ, B ^ (4 : ℕ) < Q₀ :=
    ⟨⌊B ^ (4 : ℕ)⌋₊ + 1, by exact_mod_cast Nat.lt_floor_add_one (B ^ (4 : ℕ))⟩
  refine ⟨Q₀ ^ N, fun F E _ _ _ _ _ hX => ?_⟩
  have hE : Fintype.card E = Fintype.card F ^ finrank F E := Module.card_eq_pow_finrank
  have hn1 : 1 ≤ finrank F E := Module.finrank_pos
  have hF1 : 1 ≤ Fintype.card F := Fintype.card_pos
  by_cases hn : N ≤ finrank F E
  · -- large `n`
    have h131 : 131200 ≤ finrank F E := le_trans (by rw [hN]; exact le_max_right _ _) hn
    have hh : Real.logb 2 (1 / ε) ≤ hPCN (finrank F E) :=
      hN₁ _ (le_trans (by rw [hN]; exact le_max_left _ _) hn)
    calc _ < (2 : ℝ) ^ (-hPCN (finrank F E)) := relErr_lt_large h131
      _ ≤ (2 : ℝ) ^ (-Real.logb 2 (1 / ε)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = ε := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (one_div_pos.mpr hε),
            one_div, inv_inv]
  · -- bounded `n`: then `q ≥ Q₀`, since `q^n ≥ Q₀^N`
    have hnN : finrank F E < N := not_le.mp hn
    have hqQ : Q₀ ≤ Fintype.card F := by
      by_contra hlt
      have hlt' : Fintype.card F < Q₀ := not_le.mp hlt
      have h1 : Fintype.card F ^ finrank F E < Q₀ ^ finrank F E :=
        pow_lt_pow_left₀ hlt' (Nat.zero_le _) (by omega)
      have h2 : Q₀ ^ finrank F E ≤ Q₀ ^ N := pow_le_pow_right₀ (by omega) hnN.le
      rw [hE] at hX
      exact absurd hX (not_le.mpr (h1.trans_le h2))
    have hbd := relErr_le_bounded (F := F) (E := E)
    have hQpos : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (Fintype.card E : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
    rw [← hs] at hbd
    have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hQpos _
    have hs4 : s ^ 4 = Fintype.card E := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hQpos.le]
      norm_num
    -- `s = q^{n/4} ≥ q^{1/4} ≥ Q₀^{1/4} > B`
    have hqE : Fintype.card F ≤ Fintype.card E := by
      rw [hE]
      calc Fintype.card F = Fintype.card F ^ 1 := (pow_one _).symm
        _ ≤ Fintype.card F ^ finrank F E := pow_le_pow_right₀ hF1 hn1
    have hBs : B < s := by
      by_contra h
      have h' : s ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hs0.le (not_lt.mp h) 4
      have : (Q₀ : ℝ) ≤ Fintype.card E := by exact_mod_cast hqQ.trans hqE
      linarith
    calc _ ≤ Ck 4 * 4 ^ finrank F E / s := hbd
      _ ≤ Ck 4 * 4 ^ N / s :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by norm_num) hnN.le) (Ck_pos 4).le) hs0.le
      _ < ε := by
          rw [div_lt_iff₀ hs0]
          have h : ε * B = Ck 4 * 4 ^ N := by rw [hB, mul_div_cancel₀ _ hε.ne']
          linarith [mul_lt_mul_of_pos_left hBs hε]

end MorganMullen
