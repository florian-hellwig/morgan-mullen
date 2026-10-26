import MorganMullen.Sec8Main

/-!
# Section 8: Hachenberger's lower bound (Corollary 8.8)

**Corollary 8.8** (paper): for every prime power `q`
and every `n ≥ 1`, with `n = p^a n'`, `p ∤ n'`,
`CN_q(n) ≥ (q - 1)^{n'} q^{(p^a - 1) n'}`, i.e. `δ_n ≥ (1 - 1/q)^{n'}`,
with equality if and only if `n' ∣ q - 1`.

The two forms agree since `(q - 1)^{n'} q^{(p^a - 1) n'} = q^n (1 - 1/q)^{n'}`
(`hachenberger_value_eq`). Outline of the proof (`a = 1 - 1/q`):

1. Put `W = 3/4` for `q = 2` and `W = 4/9` for `q ≥ 3` (`Model.Wb`); by Theorem 7.8
   (`weight_le_Wq`) every component without a condition of codimension `1` has weight `≤ W`, and by
   the proof of Theorem 8.1 (a) (`deltaStar_le_prod`), `∏_K (1 - w_K) ≥ a^{M_1} (1 - W)^{S/W} ≥
   a^{g'} (1 - W)^{S/W}`, where `g' ≥ M_1` is the number of `η ∈ μ_{n'}` with `o(η) = 1`
   (`Model.prod_one_sub_weight_ge`).
2. `S = ∑_η s(η)` (Lemma 6.1, second identity, `Model.sumS_eq_sum_sEta` in
   `Sec6NumberOfConditions.lean`), `s(η) = ∑_{d valid at η, o_d(η) ≥ 2} p^c q^{-o_d(η)} / o_d(η)`
   (`Model.sEta`).
3. `(†)`: `(1 - W)^{s(η)/W} ≥ a` whenever `o(η) ≥ 2` (`Model.dagger`), and `s(η) = 0` if `o(η) = 1`;
   hence `a^{n'} ≤ a^{g'} (1 - W)^{S/W} ≤ ∏_K (1 - w_K) ≤ δ_n` (`Model.pow_le_prod`).
4. Equality: if `n' ∣ q - 1`, all `n'` essential conditions are codimension-one singletons and
   `δ_n = a^{n'}` (`delta_eq_of_dvd`). Otherwise `o(ζ) ≥ 2` and `(†)` is strict for `η = ζ`
   (`Model.pow_lt_prod`), except for `q = 2`, `o(ζ) = 2`, `2 ∣ n`; there the level-one and the
   level-two condition through `ζ` lie in one component, so the union bound is strict
   (`prob_goodSet_gt`). In all cases `δ_n > a^{n'}`.

Main results: `hachenberger_lower_bound` and `hachenberger_eq_iff`.
-/

set_option linter.unusedSectionVars false

namespace MorganMullen

open Module Finset

namespace Model

/-! ### Definitions -/

section Defs

variable (q n : ℕ) [NeZero n]

/-- The weight bound of Corollary 8.8: `W = 3/4` for `q = 2`, `W = 4/9` otherwise. -/
noncomputable def Wb : ℝ := if q = 2 then 3 / 4 else 4 / 9

/-- The factor of `η` in the product `a^{g'} (1 - W)^{S/W} = ∏_η φ(η)`. -/
noncomputable def phiEta (W : ℝ) (i : ZMod (nfree q n)) : ℝ :=
  (if tcodim q n i = 1 then 1 - 1 / (q : ℝ) else 1) * (1 - W) ^ ((sEta q n i : ℝ) / W)

end Defs

variable {q n : ℕ} [NeZero n]

/-! ### The local bounds `(†)` -/

/-- The facts about a level `d` valid at `η = ζ^i` used below: `d ∣ o_d(η)`, `o_d(η) ∣ o(η)`,
`p^c ≤ d`. -/
lemma level_facts (hq : IsPrimePow q) {i : ZMod (nfree q n)} {d : ℕ} (hdn : d ∈ n.divisors)
    (hv : ValidAt q n d i) :
    1 ≤ d ∧ d ∣ ordMod q (ed q n d i) ∧ ordMod q (ed q n d i) ∣ tcodim q n i ∧
      chr q ^ dval q d ≤ d ∧ 0 < ordMod q (ed q n d i) := by
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hdn).ne'
  refine ⟨Nat.pos_of_mem_divisors hdn, hv.2, ordMod_dvd_ordMod (addOrderOf_mul_dvd _ i), ?_, ?_⟩
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) (Dvd.intro _ (chr_pow_dval_mul_dfree d))
  · exact ordMod_pos (coprime_q_of_dvd_nfree hq (NeZero.ne n) (addOrderOf_dvd_nfree _))
      (addOrderOf_pos' _).ne'

/-- `e_d(η) = ord η` if `d' = 1`. -/
lemma ed_of_dfree_eq_one {d : ℕ} (h : dfree q d = 1) (i : ZMod (nfree q n)) :
    ed q n d i = addOrderOf i := by
  unfold ed; rw [h, Nat.cast_one, one_mul]

/-- Monotonicity of the terms `P q^{-O} / O`. -/
lemma term_le {q p c O P₀ O₀ : ℕ} (hq : 1 ≤ q) (hP : p ^ c ≤ P₀) (hO : O₀ ≤ O) (hO₀ : 0 < O₀) :
    (p : ℚ) ^ c / O * ((q : ℚ) ^ O)⁻¹ ≤ (P₀ : ℚ) / O₀ * ((q : ℚ) ^ O₀)⁻¹ := by
  have hO0 : (0 : ℚ) < O₀ := by exact_mod_cast hO₀
  have hOq : (O₀ : ℚ) ≤ O := by exact_mod_cast hO
  have hq' : (1 : ℚ) ≤ q := by exact_mod_cast hq
  have hP' : (p : ℚ) ^ c ≤ P₀ := by exact_mod_cast hP
  apply mul_le_mul
  · exact div_le_div₀ (by positivity) hP' hO0 hOq
  · exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hq' hO)
  · positivity
  · positivity

/-- `∑_{i ∈ [m, k)} x^i ≤ x^m / (1 - x)` for `0 ≤ x < 1` (the statement of Mathlib's
`geom_sum_Ico_le_of_lt_one`, whose file is not imported by the project). -/
lemma geom_sum_Ico_le {x : ℚ} (hx : 0 ≤ x) (h'x : x < 1) (m k : ℕ) :
    ∑ i ∈ Ico m k, x ^ i ≤ x ^ m / (1 - x) := by
  rcases le_or_gt m k with hmk | hmk
  · rw [geom_sum_Ico' h'x.ne hmk]
    apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact div_nonneg (pow_nonneg hx _) (by linarith)

lemma sum_le_sum_bound {T U : Finset ℕ} (hTU : T ⊆ U) {t b : ℕ → ℚ}
    (htb : ∀ d ∈ T, t d ≤ b d) (hb : ∀ d ∈ U, 0 ≤ b d) : ∑ d ∈ T, t d ≤ ∑ d ∈ U, b d :=
  (Finset.sum_le_sum htb).trans (Finset.sum_le_sum_of_subset_of_nonneg hTU fun d hd _ => hb d hd)

lemma sEta_nonneg (i : ZMod (nfree q n)) : 0 ≤ sEta q n i :=
  Finset.sum_nonneg fun d _ => by positivity

/-- `s(η) = 0` if `o(η) = 1`. -/
lemma sEta_eq_zero (hq : IsPrimePow q) {i : ZMod (nfree q n)} (hi : tcodim q n i = 1) :
    sEta q n i = 0 := by
  classical
  unfold sEta
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨hdn, hv, h2⟩ := Finset.mem_filter.mp hd
  obtain ⟨-, -, hoo, -, -⟩ := level_facts hq hdn hv
  rw [hi] at hoo
  have := Nat.le_of_dvd one_pos hoo
  omega

/-- `q ≥ 3`, `o(η) ≥ 2`: `s(η) ≤ q^{-2}/2 + ∑_{d ≥ 2} q^{-d} ≤ 2 q^{-2}`. -/
lemma sEta_le_of_three_le (hq : IsPrimePow q) (hq3 : 3 ≤ q) {i : ZMod (nfree q n)}
    (hi : 2 ≤ tcodim q n i) : sEta q n i ≤ 2 / (q : ℚ) ^ 2 := by
  classical
  have hq1 : 1 ≤ q := by omega
  have hqQ : (3 : ℚ) ≤ q := by exact_mod_cast hq3
  set b : ℕ → ℚ := fun d => if d = 1 then 1 / 2 * ((q : ℚ) ^ 2)⁻¹ else ((q : ℚ) ^ d)⁻¹ with hb
  have h1 : sEta q n i ≤ ∑ d ∈ Ico 1 (n + 2), b d := by
    unfold sEta
    refine sum_le_sum_bound ?_ ?_ ?_
    · intro d hd
      have hdn := (Finset.mem_filter.mp hd).1
      have h1 := Nat.divisor_le hdn
      have h2 := Nat.pos_of_mem_divisors hdn
      rw [Finset.mem_Ico]; omega
    · intro d hd
      obtain ⟨hdn, hv, h2⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd1, hdo, -, hpc, hopos⟩ := level_facts hq hdn hv
      by_cases hd : d = 1
      · subst hd
        have hc : chr q ^ dval q 1 ≤ 1 := by simp [dval]
        have he : ordMod q (ed q n 1 i) = tcodim q n i := by
          rw [ed_of_dfree_eq_one dfree_one]; rfl
        refine (term_le (P₀ := 1) (O₀ := 2) hq1 hc (by rw [he]; exact hi) (by norm_num)).trans
          (le_of_eq ?_)
        simp only [hb, ↓reduceIte]
        norm_num
      · have hdle : d ≤ ordMod q (ed q n d i) := Nat.le_of_dvd hopos hdo
        refine (term_le hq1 hpc hdle (by omega)).trans (le_of_eq ?_)
        have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
        simp only [hb, hd, ↓reduceIte]
        rw [div_self hd', one_mul]
    · intro d _
      simp only [hb]
      split_ifs <;> positivity
  have h2 : ∑ d ∈ Ico 1 (n + 2), b d ≤ 2 / (q : ℚ) ^ 2 := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < n + 2)]
    have hb1 : b 1 = 1 / 2 * ((q : ℚ) ^ 2)⁻¹ := by simp [hb]
    have hrest : ∑ d ∈ Ico (1 + 1) (n + 2), b d = ∑ d ∈ Ico 2 (n + 2), ((q : ℚ)⁻¹) ^ d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have : d ≠ 1 := by rw [Finset.mem_Ico] at hd; omega
      simp only [hb, this, ↓reduceIte, inv_pow]
    rw [hb1, hrest]
    set x : ℚ := (q : ℚ)⁻¹ with hx
    have hx0 : 0 ≤ x := by positivity
    have hx3 : x ≤ 1 / 3 := by
      rw [hx, one_div]; exact inv_anti₀ (by norm_num) hqQ
    have hgeom := geom_sum_Ico_le hx0 (by linarith) 2 (n + 2)
    have hg : x ^ 2 / (1 - x) ≤ 3 / 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℚ) ≤ 1 / 3 - x)]
    have e1 : ((q : ℚ) ^ 2)⁻¹ = x ^ 2 := by rw [hx, inv_pow]
    have e2 : 2 / (q : ℚ) ^ 2 = 2 * x ^ 2 := by rw [div_eq_mul_inv, e1]
    rw [e1, e2]
    linarith
  exact h1.trans h2

/-- `q = 2`, `o(η) = 2`: the valid levels are among `d = 1, 2`, so `s(η) ≤ 1/8 + 1/4 = 3/8`, and
`s(η) ≤ 1/8` if `2 ∤ n`. -/
lemma sEta_le_two_two (hq : q = 2) {i : ZMod (nfree q n)} (hi : tcodim q n i = 2) :
    sEta q n i ≤ 3 / 8 ∧ (¬ 2 ∣ n → sEta q n i ≤ 1 / 8) := by
  classical
  subst hq
  have hq' : IsPrimePow 2 := Nat.prime_two.isPrimePow
  have key : ∀ d ∈ n.divisors.filter (fun d => ValidAt 2 n d i ∧ 2 ≤ ordMod 2 (ed 2 n d i)),
      (1 ≤ d ∧ d ≤ 2 ∧ d ∣ n) ∧
        (chr 2 : ℚ) ^ dval 2 d / ordMod 2 (ed 2 n d i) * (((2 : ℕ) : ℚ) ^ ordMod 2 (ed 2 n d i))⁻¹
          ≤ (d : ℚ) / 8 := by
    intro d hd
    obtain ⟨hdn, hv, h2⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdo, hoo, hpc, hopos⟩ := level_facts hq' hdn hv
    rw [hi] at hoo
    have ho2 : ordMod 2 (ed 2 n d i) = 2 := le_antisymm (Nat.le_of_dvd (by norm_num) hoo) h2
    rw [ho2] at hdo
    have hd2 : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdo
    refine ⟨⟨hd1, hd2, Nat.dvd_of_mem_divisors hdn⟩, ?_⟩
    refine (term_le (q := 2) (O₀ := 2) (by norm_num) hpc ho2.ge (by norm_num)).trans (le_of_eq ?_)
    push_cast; ring
  constructor
  · unfold sEta
    refine (sum_le_sum_bound (U := {1, 2}) (b := fun d => (d : ℚ) / 8) ?_ (fun d hd => (key d hd).2)
      (fun d _ => div_nonneg (Nat.cast_nonneg d) (by norm_num))).trans (le_of_eq ?_)
    · intro d hd
      obtain ⟨⟨h1, h2, -⟩, -⟩ := key d hd
      rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl <;> simp
    · rw [Finset.sum_pair (by norm_num)]; norm_num
  · intro h2n
    unfold sEta
    refine (sum_le_sum_bound (U := {1}) (b := fun d => (d : ℚ) / 8) ?_ (fun d hd => (key d hd).2)
      (fun d _ => div_nonneg (Nat.cast_nonneg d) (by norm_num))).trans (le_of_eq ?_)
    · intro d hd
      obtain ⟨⟨h1, h2, hdn⟩, -⟩ := key d hd
      rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
      · simp
      · exact absurd hdn h2n
    · rw [Finset.sum_singleton]; norm_num

lemma chr_two : chr 2 = 2 := by decide

lemma dfree_two_two : dfree 2 2 = 1 := by
  unfold dfree; rw [chr_two]
  have := pfree_pow_mul Nat.prime_two 1 1
  simpa [pfree_one] using this

/-- `q = 2`, `o(η) ≥ 3`: then `o_d(η) ≥ 3` for every valid `d`, the terms of `d = 1, 2, 3, 4` are at
most `1/24, 1/32, 1/24, 1/16`, those of `d ≥ 5` at most `2^{-d}`, so `s(η) ≤ 23/96`. -/
lemma sEta_le_two_three (hq : q = 2) {i : ZMod (nfree q n)} (hi : 3 ≤ tcodim q n i) :
    sEta q n i ≤ 23 / 96 := by
  classical
  subst hq
  have hq' : IsPrimePow 2 := Nat.prime_two.isPrimePow
  set b : ℕ → ℚ := fun d => if d = 1 then 1 / 24 else if d = 2 then 1 / 32 else
    if d = 3 then 1 / 24 else if d = 4 then 1 / 16 else ((2 : ℚ) ^ d)⁻¹ with hb
  have h1 : sEta 2 n i ≤ ∑ d ∈ Ico 1 (n + 5), b d := by
    unfold sEta
    refine sum_le_sum_bound ?_ ?_ ?_
    · intro d hd
      have hdn := (Finset.mem_filter.mp hd).1
      have h1 := Nat.divisor_le hdn
      have h2 := Nat.pos_of_mem_divisors hdn
      rw [Finset.mem_Ico]; omega
    · intro d hd
      obtain ⟨hdn, hv, h2⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd1, hdo, -, hpc, hopos⟩ := level_facts hq' hdn hv
      -- `o_d(η) ≥ 3`
      have ho3 : 3 ≤ ordMod 2 (ed 2 n d i) := by
        by_contra hlt
        have ho2 : ordMod 2 (ed 2 n d i) = 2 := by omega
        have hdo' := hdo
        rw [ho2] at hdo'
        have hd2 : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdo'
        have hdf : dfree 2 d = 1 := by
          rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
          · exact dfree_one
          · exact dfree_two_two
        have : ordMod 2 (ed 2 n d i) = tcodim 2 n i := by
          rw [ed_of_dfree_eq_one hdf]; rfl
        omega
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ 5 ≤ d) with rfl | rfl | rfl | rfl | h5
      · have hc : chr 2 ^ dval 2 1 ≤ 1 := by simp [dval]
        refine (term_le (q := 2) (O₀ := 3) (by norm_num) hc ho3 (by norm_num)).trans (le_of_eq ?_)
        norm_num [hb]
      · have ho4 : 4 ≤ ordMod 2 (ed 2 n 2 i) := by obtain ⟨k, hk⟩ := hdo; omega
        refine (term_le (q := 2) (O₀ := 4) (by norm_num) hpc ho4 (by norm_num)).trans (le_of_eq ?_)
        norm_num [hb]
      · have hc : chr 2 ^ dval 2 3 ≤ 1 := by
          have : dval 2 3 = 0 := by
            unfold dval; rw [chr_two]; exact Nat.factorization_eq_zero_of_not_dvd (by norm_num)
          rw [this, pow_zero]
        refine (term_le (q := 2) (O₀ := 3) (by norm_num) hc ho3 (by norm_num)).trans (le_of_eq ?_)
        norm_num [hb]
      · have ho4 : 4 ≤ ordMod 2 (ed 2 n 4 i) := Nat.le_of_dvd hopos hdo
        refine (term_le (q := 2) (O₀ := 4) (by norm_num) hpc ho4 (by norm_num)).trans (le_of_eq ?_)
        norm_num [hb]
      · have hdle : d ≤ ordMod 2 (ed 2 n d i) := Nat.le_of_dvd hopos hdo
        refine (term_le (q := 2) (by norm_num) hpc hdle (by omega)).trans (le_of_eq ?_)
        have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
        simp only [hb, show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 3 by omega,
          show d ≠ 4 by omega, ↓reduceIte]
        rw [div_self hd', one_mul]
        norm_num
    · intro d _
      simp only [hb]
      split_ifs <;> positivity
  have h2 : ∑ d ∈ Ico 1 (n + 5), b d ≤ 23 / 96 := by
    rw [← Finset.sum_Ico_consecutive b (by omega : 1 ≤ 5) (by omega : 5 ≤ n + 5)]
    have hhead : ∑ d ∈ Ico 1 5, b d = 17 / 96 := by
      rw [Finset.sum_Ico_eq_sum_range]
      norm_num [Finset.sum_range_succ, hb]
    have htail : ∑ d ∈ Ico 5 (n + 5), b d ≤ 1 / 16 := by
      have hcongr : ∑ d ∈ Ico 5 (n + 5), b d = ∑ d ∈ Ico 5 (n + 5), ((1 : ℚ) / 2) ^ d := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Finset.mem_Ico] at hd
        simp only [hb, show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 3 by omega,
          show d ≠ 4 by omega, ↓reduceIte]
        rw [one_div, inv_pow]
      rw [hcongr]
      refine (geom_sum_Ico_le (x := (1 : ℚ) / 2) (by norm_num) (by norm_num) 5 (n + 5)).trans
        (le_of_eq ?_)
      norm_num
    linarith
  exact h1.trans h2

/-- `q ≥ 3`: if `0 ≤ s ≤ 2/q²` then `(5/9)^{s/(4/9)} > 1 - 1/q` (Bernoulli's inequality for
`(9/5)^x`, `x = 9s/4 ≤ 1/2`). -/
lemma lt_rpow_of_three_le {q : ℕ} (hq3 : 3 ≤ q) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 2 / (q : ℝ) ^ 2) :
    1 - 1 / (q : ℝ) < (1 - 4 / 9) ^ (s / (4 / 9)) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hqpos : (0 : ℝ) < q := by linarith
  set y : ℝ := 1 / (q : ℝ) with hy
  have hy0 : 0 < y := by positivity
  have hy3 : y ≤ 1 / 3 := by rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hqR
  have hs' : s ≤ 2 * y ^ 2 := by
    rw [hy, div_pow, one_pow, ← div_eq_mul_one_div]; exact hs
  set x : ℝ := s / (4 / 9) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxy : x ≤ 9 / 2 * y ^ 2 := by rw [hx, div_le_iff₀ (by norm_num)]; linarith
  have hy2 : y ^ 2 ≤ 1 / 9 := by nlinarith
  have hx1 : x ≤ 1 := by linarith
  have hB : (9 / 5 : ℝ) ^ x ≤ 1 + x * (4 / 5) := by
    have h := rpow_one_add_le_one_add_mul_self (s := (4 : ℝ) / 5) (by norm_num) hx0 hx1
    rwa [show (1 : ℝ) + 4 / 5 = 9 / 5 by norm_num] at h
  have hpos : 0 < (9 / 5 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have h59 : (1 - 4 / 9 : ℝ) ^ x = ((9 / 5 : ℝ) ^ x)⁻¹ := by
    rw [show (1 : ℝ) - 4 / 9 = (9 / 5)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
  rw [h59]
  have hlt : 1 - y < (1 + x * (4 / 5))⁻¹ := by
    rw [← one_div, lt_div_iff₀ (by positivity)]
    have k1 : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
    have k2 : 18 / 5 * y ^ 2 * (1 - y) < y := by
      have e : 18 / 5 * y ^ 2 * (1 - y) = y * (18 / 5 * (y * (1 - y))) := by ring
      rw [e]
      have : 18 / 5 * (y * (1 - y)) < 1 := by linarith
      calc y * (18 / 5 * (y * (1 - y))) < y * 1 := mul_lt_mul_of_pos_left this hy0
        _ = y := mul_one y
    have k3 : (1 - y) * (1 + x * (4 / 5)) ≤ (1 - y) * (1 + 18 / 5 * y ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have k4 : (1 - y) * (1 + 18 / 5 * y ^ 2) = 1 - y + 18 / 5 * y ^ 2 * (1 - y) := by ring
    linarith
  exact hlt.trans_le (inv_anti₀ hpos hB)

/-- `(1/4)^{1/2} = 1/2`. -/
lemma quarter_rpow_half : (1 - 3 / 4 : ℝ) ^ ((1 : ℝ) / 2) = 1 / 2 := by
  rw [show (1 : ℝ) - 3 / 4 = (1 / 2) ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
    ← Real.rpow_mul (by norm_num), show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]

/-- `q = 2`: `(1/4)^{s/(3/4)} ≥ 1/2` iff `s ≤ 3/8`. -/
lemma half_le_rpow {s : ℝ} (hs : s ≤ 3 / 8) :
    1 - 1 / ((2 : ℕ) : ℝ) ≤ (1 - 3 / 4) ^ (s / (3 / 4)) := by
  have e : 1 - 1 / ((2 : ℕ) : ℝ) = (1 - 3 / 4 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [quarter_rpow_half]; norm_num
  rw [e]
  exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
    (by rw [div_le_iff₀ (by norm_num)]; linarith)

lemma half_lt_rpow {s : ℝ} (hs : s < 3 / 8) :
    1 - 1 / ((2 : ℕ) : ℝ) < (1 - 3 / 4) ^ (s / (3 / 4)) := by
  have e : 1 - 1 / ((2 : ℕ) : ℝ) = (1 - 3 / 4 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [quarter_rpow_half]; norm_num
  rw [e]
  exact Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num)
    (by rw [div_lt_iff₀ (by norm_num)]; linarith)

lemma Wb_pos_lt_one (q : ℕ) : 0 < Wb q ∧ Wb q < 1 := by
  unfold Wb; split_ifs <;> norm_num

lemma Wq_le_Wb (q : ℕ) : (Wq q : ℝ) ≤ Wb q := by
  by_cases h2 : q = 2
  · subst h2; norm_num [Wq, Wb]
  · have h : Wq q ≤ 4 / 9 := by
      unfold Wq
      split <;> first | (exfalso; exact h2 rfl) | norm_num
    rw [show Wb q = 4 / 9 by simp [Wb, h2]]
    have h' := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at h'
    exact h'

/-- **`(†)`**: for `o(η) ≥ 2`, `(1 - W)^{s(η)/W} ≥ 1 - 1/q`, strictly unless `q = 2`, `o(η) = 2` and
`2 ∣ n`. -/
lemma dagger (hq : IsPrimePow q) {i : ZMod (nfree q n)} (hi : 2 ≤ tcodim q n i) :
    1 - 1 / (q : ℝ) ≤ (1 - Wb q) ^ ((sEta q n i : ℝ) / Wb q) ∧
      (¬ (q = 2 ∧ tcodim q n i = 2 ∧ 2 ∣ n) →
        1 - 1 / (q : ℝ) < (1 - Wb q) ^ ((sEta q n i : ℝ) / Wb q)) := by
  by_cases hq2 : q = 2
  · subst hq2
    have hW : Wb 2 = 3 / 4 := by simp [Wb]
    rw [hW]
    rcases (by omega : tcodim 2 n i = 2 ∨ 3 ≤ tcodim 2 n i) with h2 | h3
    · obtain ⟨hs, hs'⟩ := sEta_le_two_two rfl h2
      have hsR := (Rat.cast_le (K := ℝ)).mpr hs
      push_cast at hsR
      refine ⟨half_le_rpow hsR, fun hne => ?_⟩
      have h2n : ¬ 2 ∣ n := fun h => hne ⟨rfl, h2, h⟩
      have h18 := (Rat.cast_le (K := ℝ)).mpr (hs' h2n)
      push_cast at h18
      exact half_lt_rpow (by linarith)
    · have hs := sEta_le_two_three rfl h3
      have h23 := (Rat.cast_le (K := ℝ)).mpr hs
      push_cast at h23
      have hsR : (sEta 2 n i : ℝ) < 3 / 8 := by linarith
      exact ⟨(half_lt_rpow hsR).le, fun _ => half_lt_rpow hsR⟩
  · have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have hW : Wb q = 4 / 9 := by simp [Wb, hq2]
    rw [hW]
    have hs := sEta_le_of_three_le hq hq3 hi
    have hsR := (Rat.cast_le (K := ℝ)).mpr hs
    push_cast at hsR
    have h0 : (0 : ℝ) ≤ sEta q n i := Rat.cast_nonneg.mpr (sEta_nonneg i)
    have h := lt_rpow_of_three_le hq3 h0 hsR
    exact ⟨h.le, fun _ => h⟩

/-! ### The product `∏_η φ(η)` -/

lemma one_sub_inv_pos (hq : IsPrimePow q) : 0 < 1 - 1 / (q : ℝ) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

lemma le_phiEta (hq : IsPrimePow q) (i : ZMod (nfree q n)) :
    1 - 1 / (q : ℝ) ≤ phiEta q n (Wb q) i := by
  unfold phiEta
  by_cases h1 : tcodim q n i = 1
  · rw [ite_eq_left h1, sEta_eq_zero hq h1]; simp
  · rw [ite_eq_right h1, one_mul]
    have := one_le_tcodim hq i
    exact (dagger hq (by omega)).1

lemma lt_phiEta (hq : IsPrimePow q) {i : ZMod (nfree q n)} (hi : 2 ≤ tcodim q n i)
    (hexc : ¬ (q = 2 ∧ tcodim q n i = 2 ∧ 2 ∣ n)) :
    1 - 1 / (q : ℝ) < phiEta q n (Wb q) i := by
  unfold phiEta
  rw [ite_eq_right (show tcodim q n i ≠ 1 by omega), one_mul]
  exact (dagger hq hi).2 hexc

/-- `∏_η φ(η) = a^{g'} (1 - W)^{S/W}`. -/
lemma prod_phiEta (hq : IsPrimePow q) (W : ℝ) (hW : 0 < 1 - W) :
    ∏ i, phiEta q n W i =
      (1 - 1 / (q : ℝ)) ^ (univ.filter fun i : ZMod (nfree q n) => tcodim q n i = 1).card *
        (1 - W) ^ ((sumS q n : ℝ) / W) := by
  classical
  unfold phiEta
  rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const,
    ← Real.rpow_sum_of_pos hW, ← Finset.sum_div, sumS_eq_sum_sEta hq]
  push_cast
  rfl

/-! ### The lower bound `δ_* ≤ ∏_K (1 - w_K)` -/

/-- The number of essential conditions of codimension `1` is at most the number `g'` of
`η ∈ μ_{n'}` with `o(η) = 1` (Lemma 3.3 (c): they are the conditions `(1, {η})`). -/
lemma card_codim_one_le (hq : IsPrimePow q) :
    ((essConds q n).filter fun C => codim q n C = 1).card ≤
      (univ.filter fun i : ZMod (nfree q n) => tcodim q n i = 1).card := by
  classical
  refine (Finset.card_le_card ?_).trans (Finset.card_image_le
    (s := univ.filter fun i : ZMod (nfree q n) => tcodim q n i = 1)
    (f := fun x => ((1, {x}) : Cond q n)))
  intro C hC
  obtain ⟨hCe, h1⟩ := Finset.mem_filter.mp hC
  obtain ⟨x, rfl, hx⟩ := codim_one_struct hq hCe h1
  exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

/-- The `δ_*` bound of the proof of Theorem 8.1 (a) (`deltaStar_le_prod`), with `g' ≥ M_1` in place of
`M_1`: `a^{g'} (1 - W)^{S/W} ≤ ∏_K (1 - w_K)`. -/
theorem prod_one_sub_weight_ge (hq : IsPrimePow q) {W : ℝ} (hW0 : 0 < W) (hW1 : W < 1)
    (hcomp : ∀ K ∈ components q n (essConds q n),
      (∀ C ∈ K, 2 ≤ codim q n C) → (weight q n K : ℝ) ≤ W) :
    (1 - 1 / (q : ℝ)) ^ (univ.filter fun i : ZMod (nfree q n) => tcodim q n i = 1).card *
        (1 - W) ^ ((sumS q n : ℝ) / W) ≤
      ∏ K ∈ components q n (essConds q n), (1 - (weight q n K : ℝ)) := by
  have ha0 : 0 < 1 - 1 / (q : ℝ) := one_sub_inv_pos hq
  have ha1 : 1 - 1 / (q : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (q : ℝ) := by positivity
    linarith
  refine le_trans ?_ (deltaStar_le_prod hq hW0 hW1 hcomp)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ha0.le ha1 (card_codim_one_le hq))
    (Real.rpow_pos_of_pos (by linarith) _).le

/-- Theorem 7.8 with `W(q) ≤ W`. -/
lemma weight_le_Wb (hq : IsPrimePow q) :
    ∀ K ∈ components q n (essConds q n), (∀ C ∈ K, 2 ≤ codim q n C) →
      (weight q n K : ℝ) ≤ Wb q := fun K hK hK2 => by
  have h := weight_le_Wq q n hq hK hK2
  have h' : (weight q n K : ℝ) ≤ (Wq q : ℝ) := by exact_mod_cast h
  exact h'.trans (Wq_le_Wb q)

/-- `(1 - 1/q)^{n'} ≤ ∏_K (1 - w_K)`. -/
theorem pow_le_prod (hq : IsPrimePow q) :
    (1 - 1 / (q : ℝ)) ^ nfree q n ≤
      ∏ K ∈ components q n (essConds q n), (1 - (weight q n K : ℝ)) := by
  obtain ⟨hW0, hW1⟩ := Wb_pos_lt_one q
  calc (1 - 1 / (q : ℝ)) ^ nfree q n = ∏ _i : ZMod (nfree q n), (1 - 1 / (q : ℝ)) := by
        rw [Finset.prod_const, Finset.card_univ, ZMod.card]
    _ ≤ ∏ i, phiEta q n (Wb q) i :=
        Finset.prod_le_prod₀ (fun _ _ => (one_sub_inv_pos hq).le) fun i _ => le_phiEta hq i
    _ = _ := prod_phiEta hq _ (by linarith)
    _ ≤ _ := prod_one_sub_weight_ge hq hW0 hW1 (weight_le_Wb hq)

/-- `(1 - 1/q)^{n'} < ∏_K (1 - w_K)` if `(†)` is strict for some `η`. -/
theorem pow_lt_prod (hq : IsPrimePow q) {i : ZMod (nfree q n)} (hi : 2 ≤ tcodim q n i)
    (hexc : ¬ (q = 2 ∧ tcodim q n i = 2 ∧ 2 ∣ n)) :
    (1 - 1 / (q : ℝ)) ^ nfree q n <
      ∏ K ∈ components q n (essConds q n), (1 - (weight q n K : ℝ)) := by
  obtain ⟨hW0, hW1⟩ := Wb_pos_lt_one q
  calc (1 - 1 / (q : ℝ)) ^ nfree q n = ∏ _i : ZMod (nfree q n), (1 - 1 / (q : ℝ)) := by
        rw [Finset.prod_const, Finset.card_univ, ZMod.card]
    _ < ∏ i, phiEta q n (Wb q) i :=
        Finset.prod_lt_prod₀ (fun _ _ => one_sub_inv_pos hq) (fun i _ => le_phiEta hq i)
          ⟨i, Finset.mem_univ _, lt_phiEta hq hi hexc⟩
    _ = _ := prod_phiEta hq _ (by linarith)
    _ ≤ _ := prod_one_sub_weight_ge hq hW0 hW1 (weight_le_Wb hq)

/-! ### The case of equality -/

/-- `o(ζ) = 1`, i.e. `ord_{n'}(q) = 1`, iff `n' ∣ q - 1`; so `o(ζ) ≥ 2` if `n' ∤ q - 1`. -/
lemma two_le_tcodim_one (hq : IsPrimePow q) (h : ¬ nfree q n ∣ q - 1) :
    2 ≤ tcodim q n (1 : ZMod (nfree q n)) := by
  have h1 := one_le_tcodim hq (1 : ZMod (nfree q n))
  by_contra hlt
  have he : tcodim q n (1 : ZMod (nfree q n)) = 1 := by omega
  apply h
  unfold tcodim at he
  rw [ZMod.addOrderOf_one] at he
  have hm := (ordMod_dvd_iff_modEq (q := q) (e := nfree q n) (k := 1)).mp (dvd_of_eq he)
  rw [pow_one] at hm
  exact (Nat.modEq_iff_dvd' hq.one_lt.le).mp hm.symm

/-- If `n' ∣ q - 1`, then `o(η) = 1` for every `η ∈ μ_{n'}`. -/
lemma tcodim_eq_one_of_dvd (hq : IsPrimePow q) (h : nfree q n ∣ q - 1) (x : ZMod (nfree q n)) :
    tcodim q n x = 1 := by
  unfold tcodim
  apply Nat.dvd_one.mp
  rw [ordMod_dvd_iff_modEq, pow_one]
  exact ((Nat.modEq_iff_dvd' hq.one_lt.le).mpr ((addOrderOf_dvd_nfree x).trans h)).symm

/-- If `n' ∣ q - 1`, the essential conditions are the `n'` codimension-one singletons `(1, {η})`. -/
lemma card_components_of_dvd (hq : IsPrimePow q) (h : nfree q n ∣ q - 1) :
    (components q n (essConds q n)).card = nfree q n := by
  classical
  have hall := tcodim_eq_one_of_dvd hq h
  have hcod : ∀ C ∈ essConds q n, codim q n C = 1 := by
    intro C hC
    obtain ⟨d, -, x, -, -, rfl⟩ := (mem_essConds_iff hq).mp hC
    rw [codim_orbit hq]; exact hall x
  have hess : essConds q n = univ.image fun x : ZMod (nfree q n) => ((1, {x}) : Cond q n) := by
    ext C
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hC
      obtain ⟨x, rfl, -⟩ := codim_one_struct hq hC (hcod C hC)
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      have hx := hall x
      unfold tcodim at hx
      have : lev1 x = ((1, {x}) : Cond q n) := by
        unfold lev1; rw [orbit_eq_singleton (d := 1) (x := x) hq (by simp [hx])]
      rw [← this]; exact lev1_mem_essConds x
  have hinj : Function.Injective fun x : ZMod (nfree q n) => ((1, {x}) : Cond q n) := by
    intro x y hxy
    simpa using congrArg Prod.snd hxy
  have hcomp : components q n (essConds q n) = (essConds q n).image fun C => {C} := by
    unfold components
    refine Finset.image_congr fun C hC => ?_
    exact (codim_one_singleton hq (Finset.mem_coe.mp hC) (hcod C (Finset.mem_coe.mp hC))).2
  rw [hcomp, Finset.card_image_of_injective _ Finset.singleton_injective, hess,
    Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

/-- If `q = 2`, `2 ∣ n` and `2 ∣ o(ζ)`, the level-one condition through `ζ` and the level-two
condition with target `ζ` are two different essential conditions in one component. -/
lemma exists_comp_two_conds (hq : q = 2) (h2n : 2 ∣ n)
    (h1 : 2 ∣ tcodim q n (1 : ZMod (nfree q n))) :
    ∃ K ∈ components q n (essConds q n), ∃ C₁ ∈ K, ∃ C₂ ∈ K, C₁ ≠ C₂ := by
  classical
  subst hq
  have hq' : IsPrimePow 2 := Nat.prime_two.isPrimePow
  have hL := lev1_mem_essConds (q := 2) (n := n) 1
  have hC₂ : ((2, orbit 2 n 2 1) : Cond 2 n) ∈ essConds 2 n := by
    refine (mem_essConds_iff hq').mpr ⟨2, Nat.mem_divisors.mpr ⟨h2n, NeZero.ne n⟩, 1, ?_, h1, rfl⟩
    have : bigN 2 n 2 = nfree 2 n := by unfold bigN; rw [dfree_two_two, Nat.div_one]
    rw [mul_one, this, ZMod.natCast_self]
  have hadj : Adj 2 n (lev1 1) ((2, orbit 2 n 2 1) : Cond 2 n) := by
    refine adj_of_mem_fibre (i := 1) ?_ ?_
    · simpa using mem_fibre_lev1 hq' (1 : ZMod (nfree 2 n)) 0
    · rw [mem_fibre]
      simp only [dfree_two_two, Nat.cast_one, one_mul]
      exact mem_orbit_self 2 1
  refine ⟨component 2 n (essConds 2 n) (lev1 1), component_mem_components hL, lev1 1,
    mem_component_self hL, (2, orbit 2 n 2 1),
    Finset.mem_filter.mpr ⟨hC₂, Relation.EqvGen.rel _ _ ⟨hL, hC₂, hadj⟩⟩, ?_⟩
  intro h
  have := congrArg Prod.fst h
  simp [lev1] at this

end Model

/-- `(q - 1)^{n'} q^{(p^a - 1) n'} = q^n (1 - 1/q)^{n'}`. -/
lemma hachenberger_value_eq (q n : ℕ) (hq : 1 ≤ q) :
    (((q - 1) ^ Model.nfree q n * q ^ ((Model.pa q n - 1) * Model.nfree q n) : ℕ) : ℝ) =
      (q : ℝ) ^ n * (1 - 1 / (q : ℝ)) ^ Model.nfree q n := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hpa1 : 1 ≤ Model.pa q n := Nat.pos_of_ne_zero (NeZero.ne _)
  have hpa : (Model.pa q n - 1) * Model.nfree q n + Model.nfree q n = n := by
    have h := Model.pa_mul_nfree q n
    obtain ⟨k, hk⟩ : ∃ k, Model.pa q n = k + 1 := ⟨_, (Nat.sub_add_cancel hpa1).symm⟩
    rw [hk] at h ⊢
    rw [Nat.add_sub_cancel]
    calc k * Model.nfree q n + Model.nfree q n = (k + 1) * Model.nfree q n := by ring
      _ = n := h
  have hq0 : (q : ℝ) ≠ 0 := hqpos.ne'
  push_cast [Nat.cast_sub hq]
  have e : (q : ℝ) - 1 = q * (1 - 1 / q) := by rw [mul_sub, mul_one, mul_one_div_cancel hq0]
  have hqn : (q : ℝ) ^ n = (q : ℝ) ^ ((Model.pa q n - 1) * Model.nfree q n) * (q : ℝ) ^ Model.nfree q n := by
    rw [← pow_add, hpa]
  rw [e, mul_pow, hqn]
  ring

section Setting

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
variable {Ω : Type*} [Field Ω] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]

local notation "q" => Fintype.card F
local notation "n" => Module.finrank F E

open Classical in
/-- The union bound inside a component is strict if the component has two different conditions:
all kernels contain `0`. -/
theorem prob_goodSet_gt {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n))
    {K : Finset (Model.Cond q n)} (hK : K ⊆ Model.essConds q n) {C₁ C₂ : Model.Cond q n}
    (h₁ : C₁ ∈ K) (h₂ : C₂ ∈ K) (hne : C₁ ≠ C₂) :
    1 - Model.weight q n K < ((goodSet (F := F) (E := E) ζ K).card : ℚ) / Fintype.card E := by
  set V : Model.Cond q n → Finset E := fun C => univ.filter (· ∈ condKer (F := F) ζ C)
  have hV : ∀ C ∈ K, (V C).card = q ^ (n - Model.codim q n C) ∧ Model.codim q n C ≤ n := by
    intro C hC
    have h := card_condKer hζ (hK hC)
    refine ⟨?_, h.2⟩
    rw [← h.1, Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun w => by simp [V])
  have h0 : ∀ C, (0 : E) ∈ V C := fun C => by simp [V]
  have hU : K.biUnion V = V C₁ ∪ (K.erase C₁).biUnion V := by
    rw [← Finset.biUnion_insert, Finset.insert_erase h₁]
  have hinter : 1 ≤ (V C₁ ∩ (K.erase C₁).biUnion V).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_inter.mpr ⟨h0 C₁, Finset.mem_biUnion.mpr
      ⟨C₂, Finset.mem_erase.mpr ⟨hne.symm, h₂⟩, h0 C₂⟩⟩⟩
  have hunion : (K.biUnion V).card + 1 ≤ ∑ C ∈ K, (V C).card := by
    have h1 := Finset.card_union_add_card_inter (V C₁) ((K.erase C₁).biUnion V)
    have h2 : ((K.erase C₁).biUnion V).card ≤ ∑ C ∈ K.erase C₁, (V C).card :=
      Finset.card_biUnion_le
    have h3 : (V C₁).card + ∑ C ∈ K.erase C₁, (V C).card = ∑ C ∈ K, (V C).card :=
      Finset.add_sum_erase K (fun C => (V C).card) h₁
    rw [hU]; omega
  have hsplit : Fintype.card E + 1 ≤
      (goodSet (F := F) (E := E) ζ K).card + ∑ C ∈ K, (V C).card := by
    have h1 : (univ : Finset E) ⊆ goodSet (F := F) ζ K ∪ K.biUnion V := by
      intro w _
      by_cases hw : w ∈ goodSet (F := F) ζ K
      · exact Finset.mem_union_left _ hw
      · apply Finset.mem_union_right
        simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
          not_not] at hw
        obtain ⟨C, hC, hwC⟩ := hw
        exact Finset.mem_biUnion.2 ⟨C, hC, by simp [V, hwC]⟩
    have h2 : Fintype.card E ≤ (goodSet (F := F) (E := E) ζ K).card + (K.biUnion V).card :=
      calc Fintype.card E = (univ : Finset E).card := rfl
        _ ≤ (goodSet (F := F) ζ K ∪ K.biUnion V).card := Finset.card_le_card h1
        _ ≤ _ := Finset.card_union_le _ _
    omega
  have hE : Fintype.card E = q ^ n := Module.card_eq_pow_finrank
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw : Model.weight q n K = (∑ C ∈ K, ((V C).card : ℚ)) / Fintype.card E := by
    unfold Model.weight
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun C hC => ?_
    rw [(hV C hC).1, hE]
    push_cast
    rw [eq_div_iff (pow_ne_zero _ hq0)]
    have e : (q : ℚ) ^ n = (q : ℚ) ^ Model.codim q n C * (q : ℚ) ^ (n - Model.codim q n C) := by
      rw [← pow_add, Nat.add_sub_cancel' (hV C hC).2]
    rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]
  rw [hw, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ (by exact_mod_cast Fintype.card_pos), one_mul]
  have hlt : Fintype.card E < (goodSet (F := F) (E := E) ζ K).card + ∑ C ∈ K, (V C).card := by
    omega
  exact_mod_cast hlt

open Classical in
/-- A codimension-one singleton component has probability exactly `1 - 1/q`. -/
lemma prob_goodSet_singleton {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n))
    {C : Model.Cond q n} (hC : C ∈ Model.essConds q n) (h1 : Model.codim q n C = 1) :
    ((goodSet (F := F) (E := E) ζ {C}).card : ℚ) / Fintype.card E = 1 - 1 / (q : ℚ) := by
  set V : Finset E := univ.filter (· ∈ condKer (F := F) ζ C) with hV
  have hVc : V.card = q ^ (n - 1) := by
    have h := card_condKer hζ hC
    rw [h1] at h
    rw [← h.1, Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun w => by simp [V])
  have hG : goodSet (F := F) (E := E) ζ {C} = univ.filter fun w => w ∉ condKer (F := F) ζ C := by
    ext w; simp [goodSet]
  have hsum : (goodSet (F := F) (E := E) ζ {C}).card + V.card = Fintype.card E := by
    rw [hG, hV, add_comm, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hE : Fintype.card E = q ^ n := Module.card_eq_pow_finrank
  have hn : 1 ≤ n := Module.finrank_pos
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hEq : (q : ℚ) ^ n = q * q ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
  have hgood : ((goodSet (F := F) (E := E) ζ {C}).card : ℚ) = (q : ℚ) ^ n - (q : ℚ) ^ (n - 1) := by
    have h : ((goodSet (F := F) (E := E) ζ {C}).card : ℚ) + (V.card : ℚ) = (Fintype.card E : ℚ) := by
      exact_mod_cast hsum
    rw [hVc, hE] at h; push_cast at h; linarith
  rw [hgood, hE]; push_cast
  rw [hEq]; field_simp

/-- `δ_n ≥ (1 - 1/q)^{n'}`. -/
theorem delta_ge_hachenberger :
    (1 - 1 / (q : ℝ)) ^ Model.nfree q n ≤ (cnCount F E : ℝ) / Fintype.card E := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hpos : ∀ K ∈ Model.components q n (Model.essConds q n), 0 < 1 - Model.weight q n K :=
    one_sub_weight_pos hq (Model.Wb_pos_lt_one q).2 (Model.weight_le_Wb hq)
  have h2 := (Rat.cast_le (K := ℝ)).mpr (delta_ge_prod (F := F) (E := E) hpos)
  push_cast at h2
  exact (Model.pow_le_prod hq).trans h2

/-- `δ_n > (1 - 1/q)^{n'}` if `n' ∤ q - 1`. -/
theorem delta_gt_hachenberger (h : ¬ Model.nfree q n ∣ q - 1) :
    (1 - 1 / (q : ℝ)) ^ Model.nfree q n < (cnCount F E : ℝ) / Fintype.card E := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have hpos : ∀ K ∈ Model.components q n (Model.essConds q n), 0 < 1 - Model.weight q n K :=
    one_sub_weight_pos hq (Model.Wb_pos_lt_one q).2 (Model.weight_le_Wb hq)
  have h21 := Model.two_le_tcodim_one hq h
  by_cases hexc : q = 2 ∧ Model.tcodim q n 1 = 2 ∧ 2 ∣ n
  · -- `q = 2`, `o(ζ) = 2`, `2 ∣ n`: the strict union bound
    obtain ⟨hq2, ht, h2n⟩ := hexc
    obtain ⟨K₀, hK₀, C₁, h₁, C₂, h₂, hne⟩ :=
      Model.exists_comp_two_conds hq2 h2n (dvd_of_eq ht.symm)
    obtain ⟨ζ, hζ⟩ := exists_zeta (F := F) (E := E)
    have hlt : ∏ K ∈ Model.components q n (Model.essConds q n), (1 - Model.weight q n K) <
        (cnCount F E : ℚ) / Fintype.card E := by
      rw [delta_eq_prod hζ]
      exact Finset.prod_lt_prod₀ hpos
        (fun K hK => prob_goodSet_ge hζ ((Model.components_partition _).1 K hK))
        ⟨K₀, hK₀, prob_goodSet_gt hζ ((Model.components_partition _).1 K₀ hK₀) h₁ h₂ hne⟩
    have hR := (Rat.cast_lt (K := ℝ)).mpr hlt
    push_cast at hR
    exact (Model.pow_le_prod hq).trans_lt hR
  · have h2 := (Rat.cast_le (K := ℝ)).mpr (delta_ge_prod (F := F) (E := E) hpos)
    push_cast at h2
    exact (Model.pow_lt_prod hq h21 hexc).trans_le h2

/-- `δ_n = (1 - 1/q)^{n'}` if `n' ∣ q - 1`. -/
theorem delta_eq_of_dvd (h : Model.nfree q n ∣ q - 1) :
    (cnCount F E : ℚ) / Fintype.card E = (1 - 1 / (q : ℚ)) ^ Model.nfree q n := by
  classical
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  obtain ⟨ζ, hζ⟩ := exists_zeta (F := F) (E := E)
  have hall := Model.tcodim_eq_one_of_dvd hq h
  have hcod : ∀ C ∈ Model.essConds q n, Model.codim q n C = 1 := by
    intro C hC
    obtain ⟨d, -, x, -, -, rfl⟩ := (Model.mem_essConds_iff hq).mp hC
    rw [Model.codim_orbit hq]; exact hall x
  have hprob : ∀ K ∈ Model.components q n (Model.essConds q n),
      ((goodSet (F := F) (E := E) ζ K).card : ℚ) / Fintype.card E = 1 - 1 / (q : ℚ) := by
    intro K hK
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hK
    rw [(Model.codim_one_singleton hq hC (hcod C hC)).2]
    exact prob_goodSet_singleton hζ hC (hcod C hC)
  rw [delta_eq_prod hζ, Finset.prod_congr rfl hprob, Finset.prod_const,
    Model.card_components_of_dvd hq h]

/-- **Corollary 8.8** (Hachenberger's lower bound):
`CN_q(n) ≥ (q - 1)^{n'} q^{(p^a - 1) n'}`. -/
theorem hachenberger_lower_bound :
    (q - 1) ^ Model.nfree q n * q ^ ((Model.pa q n - 1) * Model.nfree q n) ≤ cnCount F E := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have h := delta_ge_hachenberger (F := F) (E := E)
  have hE : (Fintype.card E : ℝ) = (q : ℝ) ^ n := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E), Nat.cast_pow]
  have hEpos : (0 : ℝ) < (q : ℝ) ^ n := by
    have : (0 : ℝ) < q := by exact_mod_cast hq.pos
    positivity
  rw [hE, le_div_iff₀ hEpos] at h
  have h' : (((q - 1) ^ Model.nfree q n * q ^ ((Model.pa q n - 1) * Model.nfree q n) : ℕ) : ℝ) ≤
      cnCount F E := by
    rw [hachenberger_value_eq _ _ hq.one_lt.le, mul_comm]; exact h
  exact_mod_cast h'

/-- The lower bound is strict if `n' ∤ q - 1`. -/
theorem hachenberger_lt (h : ¬ Model.nfree q n ∣ q - 1) :
    (q - 1) ^ Model.nfree q n * q ^ ((Model.pa q n - 1) * Model.nfree q n) < cnCount F E := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have h1 := delta_gt_hachenberger (F := F) (E := E) h
  have hE : (Fintype.card E : ℝ) = (q : ℝ) ^ n := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E)]; push_cast; rfl
  have hEpos : (0 : ℝ) < (q : ℝ) ^ n := by
    have : (0 : ℝ) < q := by exact_mod_cast hq.pos
    positivity
  rw [hE, lt_div_iff₀ hEpos] at h1
  have h' : (((q - 1) ^ Model.nfree q n * q ^ ((Model.pa q n - 1) * Model.nfree q n) : ℕ) : ℝ) <
      cnCount F E := by
    rw [hachenberger_value_eq _ _ hq.one_lt.le, mul_comm]; exact h1
  exact_mod_cast h'

/-- **Corollary 8.8**, the case of equality: `CN_q(n) = (q - 1)^{n'} q^{(p^a - 1) n'}` if and only if
`n' ∣ q - 1`. -/
theorem hachenberger_eq_iff :
    cnCount F E = (q - 1) ^ Model.nfree q n * q ^ ((Model.pa q n - 1) * Model.nfree q n) ↔
      Model.nfree q n ∣ q - 1 := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  constructor
  · intro heq
    by_contra h
    exact (hachenberger_lt (F := F) (E := E) h).ne' heq
  · intro h
    have hδ := delta_eq_of_dvd (F := F) (E := E) h
    have hδR := congrArg (fun x : ℚ => (x : ℝ)) hδ
    push_cast at hδR
    have hE : (Fintype.card E : ℝ) = (q : ℝ) ^ n := by
      rw [Module.card_eq_pow_finrank (K := F) (V := E)]; push_cast; rfl
    have hEpos : (0 : ℝ) < (q : ℝ) ^ n := by
      have : (0 : ℝ) < q := by exact_mod_cast hq.pos
      positivity
    rw [hE, div_eq_iff hEpos.ne'] at hδR
    have h' : (cnCount F E : ℝ) =
        (((q - 1) ^ Model.nfree q n * q ^ ((Model.pa q n - 1) * Model.nfree q n) : ℕ) : ℝ) := by
      rw [hachenberger_value_eq _ _ hq.one_lt.le, hδR]; ring
    exact_mod_cast h'

end Setting

end MorganMullen
