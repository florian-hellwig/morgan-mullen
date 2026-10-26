import MorganMullen.Sec7W28Defs
import MorganMullen.Axioms

/-!
# Theorem 7.8: soundness of the checkers

* `remP_eq`, `powMod_eq`: the computable `p`-free part and modular exponentiation;
* `sum_divisors_le`: splitting `∑_{o ∣ O, o ≥ o₀}` at a cut-off `m` with the crude tail
  `∑_{o ≥ m} o² B Q^{-o} ≤ 3 m² B Q^{-m}` (`Q ≥ 2`, `m ≥ 7`);
* `Wsum_mono`: monotonicity of `Wsum` in `O` and `D` (for divisibility);
* `chkW_sound`, `certOK_sound`, `chkU_sound`: soundness of the checkers;
* `lcmUpTo_mul_le`: `lcm(1, …, m) ≤ 2.83^m` (from Rosser–Schoenfeld `ψ(x) < 1.03883 x`);
* `Wcr_le_rs`: `W_cr(q, o₀) ≤ 3 o₀³ 2.83^{o₀} q^{-o₀}` for `o₀ ≥ 7`;
* `Wcl_two_large`: `W_cl(2, o₀) ≤ 4/125 = 0.032` for `o₀ ≥ 4096` (the proof gives `3/128`; from Lemma 7.5,
  `closure_bound`).
-/

namespace MorganMullen.W28

open MorganMullen Finset

/-! ### Computable helpers -/

lemma remP_eq {p : ℕ} (hp : p.Prime) (n : ℕ) : remP p n = pfree p n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [remP]
  split_ifs with h
  · have hd : p ∣ n := Nat.dvd_of_mod_eq_zero h.2.2
    rw [ih _ (Nat.div_lt_self h.2.1 h.1)]
    conv_rhs => rw [← Nat.mul_div_cancel' hd]
    rw [show p * (n / p) = p ^ 1 * (n / p) by rw [pow_one], pfree_pow_mul hp]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pfree_zero]
    · exact (pfree_eq_self hp fun hd => h ⟨hp.one_lt, hn, Nat.mod_eq_zero_of_dvd hd⟩).symm

lemma remP_fun_eq {p : ℕ} (hp : p.Prime) : remP p = pfree p := funext (remP_eq hp)

lemma powMod_eq (b m : ℕ) : ∀ e, powMod b m e = b ^ e % m := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  rcases e with _ | e
  · rw [powMod, pow_zero]
  · rw [powMod]
    have hlt : (e + 1) / 2 < e + 1 := by omega
    rw [ih _ hlt]
    split_ifs with h
    · have : e + 1 = (e + 1) / 2 + (e + 1) / 2 := by omega
      rw [← Nat.mul_mod, ← pow_add, ← this]
    · have : e + 1 = (e + 1) / 2 + (e + 1) / 2 + 1 := by omega
      rw [← Nat.mul_mod, Nat.mod_mul_mod, ← pow_add, ← pow_succ, ← this]

lemma powMod_modEq {b m e : ℕ} (h : powMod b m e = 1 % m) : b ^ e ≡ 1 [MOD m] := by
  rw [powMod_eq] at h; exact h

lemma minFac_prime_of_two_le {q : ℕ} (hq : 2 ≤ q) : q.minFac.Prime := Nat.minFac_prime (by omega)

/-! ### The tail `∑_{o ≥ m} o² Q^{-o} ≤ 3 m² Q^{-m}` -/

lemma tail_step {Q : ℚ} (hQ : 2 ≤ Q) {o : ℕ} (ho : 7 ≤ o) :
    3 * (((o + 1 : ℕ) : ℚ) ^ 2 / Q ^ (o + 1)) ≤ 2 * ((o : ℚ) ^ 2 / Q ^ o) := by
  have hQ0 : 0 < Q := by linarith
  have hQo : 0 < Q ^ o := pow_pos hQ0 o
  have ho' : (7 : ℚ) ≤ o := by exact_mod_cast ho
  rw [pow_succ Q o, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) hQo]
  push_cast
  have h1 : 3 * ((o : ℚ) + 1) ^ 2 ≤ 2 * (o : ℚ) ^ 2 * Q := by nlinarith
  calc 3 * ((o : ℚ) + 1) ^ 2 * Q ^ o ≤ 2 * (o : ℚ) ^ 2 * Q * Q ^ o :=
        mul_le_mul_of_nonneg_right h1 hQo.le
    _ = 2 * (o : ℚ) ^ 2 * (Q ^ o * Q) := by ring

lemma tail_geom {Q : ℚ} (hQ : 2 ≤ Q) {m : ℕ} (hm : 7 ≤ m) (N : ℕ) :
    ∑ k ∈ range N, ((m + k : ℕ) : ℚ) ^ 2 / Q ^ (m + k) ≤ 3 * ((m : ℚ) ^ 2 / Q ^ m) := by
  have hQ0 : 0 < Q := by linarith
  have key : ∀ N, ∑ k ∈ range N, ((m + k : ℕ) : ℚ) ^ 2 / Q ^ (m + k) +
      3 * (((m + N : ℕ) : ℚ) ^ 2 / Q ^ (m + N)) ≤ 3 * ((m : ℚ) ^ 2 / Q ^ m) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have := tail_step hQ (o := m + N) (by omega)
      have e : m + (N + 1) = m + N + 1 := by omega
      rw [e]
      linarith
  have hpos : 0 ≤ 3 * (((m + N : ℕ) : ℚ) ^ 2 / Q ^ (m + N)) := by positivity
  linarith [key N]

/-! ### Splitting the sum over the divisors -/

/-- `∑_{o ∣ O, o ≥ o₀} f(o) ≤ ∑_{o₀ ≤ o < m, o ∣ O} f(o) + 3 m² B Q^{-m}` if
`0 ≤ f(o) ≤ o² B Q^{-o}` (the tail vanishes if `O < m`). -/
lemma sum_divisors_le (f : ℕ → ℚ) (hf0 : ∀ o, 0 ≤ f o) {B Q : ℚ} (hB : 0 ≤ B) (hQ : 2 ≤ Q)
    (hf : ∀ o, f o ≤ (o : ℚ) ^ 2 * B / Q ^ o) (O o₀ m : ℕ) (hm : 7 ≤ m) :
    ∑ o ∈ O.divisors.filter (o₀ ≤ ·), f o ≤
      ∑ o ∈ (Ico o₀ m).filter (· ∣ O), f o +
        (if O < m then 0 else 3 * (m : ℚ) ^ 2 * B / Q ^ m) := by
  have hQ0 : 0 < Q := by linarith
  have htail0 : 0 ≤ (if O < m then 0 else 3 * (m : ℚ) ^ 2 * B / Q ^ m) := by
    split_ifs <;> positivity
  rcases Nat.eq_zero_or_pos O with rfl | hO
  · simp only [Nat.divisors_zero, filter_empty, sum_empty]
    have : 0 ≤ ∑ o ∈ (Ico o₀ m).filter (· ∣ 0), f o := sum_nonneg fun o _ => hf0 o
    linarith
  rw [← sum_filter_add_sum_filter_not (O.divisors.filter (o₀ ≤ ·)) (· < m)]
  have h1 : (O.divisors.filter (o₀ ≤ ·)).filter (· < m) = (Ico o₀ m).filter (· ∣ O) := by
    ext o
    simp only [mem_filter, Nat.mem_divisors, mem_Ico]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h2⟩, h3⟩; exact ⟨⟨h2, h3⟩, h1⟩
    · rintro ⟨⟨h2, h3⟩, h1⟩; exact ⟨⟨⟨h1, hO.ne'⟩, h2⟩, h3⟩
  rw [h1]
  refine add_le_add le_rfl ?_
  split_ifs with hOm
  · apply le_of_eq
    apply sum_eq_zero
    intro o ho
    simp only [mem_filter, Nat.mem_divisors] at ho
    exact absurd (lt_of_le_of_lt (Nat.le_of_dvd hO ho.1.1.1) hOm) ho.2
  · -- the tail
    calc ∑ o ∈ (O.divisors.filter (o₀ ≤ ·)).filter (fun o => ¬ o < m), f o
        ≤ ∑ o ∈ Ico m (O + 1), f o := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro o ho
            simp only [mem_filter, Nat.mem_divisors] at ho
            simp only [mem_Ico]
            exact ⟨by omega, Nat.lt_succ_of_le (Nat.le_of_dvd hO ho.1.1.1)⟩
          · intro o _ _; exact hf0 o
      _ ≤ ∑ o ∈ Ico m (O + 1), (o : ℚ) ^ 2 * B / Q ^ o := sum_le_sum fun o _ => hf o
      _ = B * ∑ k ∈ range (O + 1 - m), ((m + k : ℕ) : ℚ) ^ 2 / Q ^ (m + k) := by
          rw [sum_Ico_eq_sum_range, mul_sum]
          apply sum_congr rfl; intro k _; ring
      _ ≤ B * (3 * ((m : ℚ) ^ 2 / Q ^ m)) := mul_le_mul_of_nonneg_left (tail_geom hQ hm _) hB
      _ = 3 * (m : ℚ) ^ 2 * B / Q ^ m := by ring

/-! ### The summands of `Wsum` -/

/-- The inner sum of `Wsum` (in `ℚ`). -/
noncomputable def innerQ (q D o : ℕ) : ℚ :=
  ∑ d ∈ o.divisors.filter (fun d => pfree (charOf q) d ∣ D),
    (d : ℚ) * (Nat.gcd (q ^ o - 1) (D / pfree (charOf q) d) : ℚ)

lemma Wsum_eq (q o₀ O D : ℕ) :
    Wsum q o₀ O D = ∑ o ∈ O.divisors.filter (o₀ ≤ ·), ((q : ℚ) ^ o)⁻¹ * innerQ q D o := rfl

lemma innerQ_nonneg (q D o : ℕ) : 0 ≤ innerQ q D o := sum_nonneg fun _ _ => by positivity

lemma sigmaN_le (o : ℕ) : sigmaN o ≤ o * o := by
  unfold sigmaN
  calc ∑ d ∈ o.divisors, d ≤ o.divisors.card • o := sum_le_card_nsmul _ _ _ fun d hd => Nat.divisor_le hd
    _ ≤ o * o := by rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ (Nat.card_divisors_le_self o)

lemma innerQ_le_sigma (q : ℕ) {D : ℕ} (hD : 0 < D) (o : ℕ) :
    innerQ q D o ≤ (sigmaN o : ℚ) * D := by
  unfold innerQ sigmaN
  rw [Nat.cast_sum, sum_mul]
  calc ∑ d ∈ o.divisors.filter (fun d => pfree (charOf q) d ∣ D),
        (d : ℚ) * (Nat.gcd (q ^ o - 1) (D / pfree (charOf q) d) : ℚ)
      ≤ ∑ d ∈ o.divisors.filter (fun d => pfree (charOf q) d ∣ D), (d : ℚ) * D := by
        apply sum_le_sum
        intro d hd
        have hd' := (mem_filter.mp hd).2
        have hd0 : 0 < d := Nat.pos_of_mem_divisors (mem_filter.mp hd).1
        have hdp : 0 < pfree (charOf q) d := pfree_pos _ hd0.ne'
        have hpos : 0 < D / pfree (charOf q) d :=
          Nat.div_pos (Nat.le_of_dvd hD hd') hdp
        have : Nat.gcd (q ^ o - 1) (D / pfree (charOf q) d) ≤ D :=
          (Nat.gcd_le_right _ hpos).trans (Nat.div_le_self _ _)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
    _ ≤ ∑ d ∈ o.divisors, (d : ℚ) * D :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity

lemma innerQ_le_sq (q : ℕ) {D : ℕ} (hD : 0 < D) (o : ℕ) :
    innerQ q D o ≤ (o : ℚ) ^ 2 * D := by
  refine (innerQ_le_sigma q hD o).trans ?_
  have : (sigmaN o : ℚ) ≤ (o : ℚ) ^ 2 := by rw [sq]; exact_mod_cast sigmaN_le o
  exact mul_le_mul_of_nonneg_right this (by positivity)

lemma innerN_eq {q : ℕ} (hq : 2 ≤ q) (o D : ℕ) : (innerN q q.minFac o D : ℚ) = innerQ q D o := by
  unfold innerN innerQ
  rw [remP_fun_eq (minFac_prime_of_two_le hq)]
  push_cast
  rfl

/-- **Monotonicity** of `Wsum` in `O` and `D` (for divisibility). -/
lemma innerQ_mono (q o : ℕ) {D D' : ℕ} (hD : D ∣ D') (hD' : 0 < D') :
    innerQ q D o ≤ innerQ q D' o := by
  unfold innerQ
  calc ∑ d ∈ o.divisors.filter (fun d => pfree (charOf q) d ∣ D),
        (d : ℚ) * (Nat.gcd (q ^ o - 1) (D / pfree (charOf q) d) : ℚ)
      ≤ ∑ d ∈ o.divisors.filter (fun d => pfree (charOf q) d ∣ D),
        (d : ℚ) * (Nat.gcd (q ^ o - 1) (D' / pfree (charOf q) d) : ℚ) := by
        apply sum_le_sum
        intro d hd
        have hd' := (mem_filter.mp hd).2
        have hdD' : pfree (charOf q) d ∣ D' := hd'.trans hD
        have hpos : 0 < D' / pfree (charOf q) d :=
          Nat.div_pos (Nat.le_of_dvd hD' hdD')
            (pfree_pos _ (Nat.pos_of_mem_divisors (mem_filter.mp hd).1).ne')
        have : Nat.gcd (q ^ o - 1) (D / pfree (charOf q) d) ≤
            Nat.gcd (q ^ o - 1) (D' / pfree (charOf q) d) :=
          Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ hpos)
            (Nat.gcd_dvd_gcd_of_dvd_right _ ((Nat.div_dvd_div_iff_right hd' hdD').mpr hD))
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
    _ ≤ ∑ d ∈ o.divisors.filter (fun d => pfree (charOf q) d ∣ D'),
        (d : ℚ) * (Nat.gcd (q ^ o - 1) (D' / pfree (charOf q) d) : ℚ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          simp only [mem_filter] at hd ⊢
          exact ⟨hd.1, hd.2.trans hD⟩
        · intro _ _ _; positivity

lemma Wsum_mono (q o₀ : ℕ) {O O' D D' : ℕ} (hO : O ∣ O') (hO' : O' ≠ 0) (hD : D ∣ D')
    (hD' : 0 < D') : Wsum q o₀ O D ≤ Wsum q o₀ O' D' := by
  rw [Wsum_eq, Wsum_eq]
  calc ∑ o ∈ O.divisors.filter (o₀ ≤ ·), ((q : ℚ) ^ o)⁻¹ * innerQ q D o
      ≤ ∑ o ∈ O.divisors.filter (o₀ ≤ ·), ((q : ℚ) ^ o)⁻¹ * innerQ q D' o :=
        sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (innerQ_mono q o hD hD') (by positivity)
    _ ≤ ∑ o ∈ O'.divisors.filter (o₀ ≤ ·), ((q : ℚ) ^ o)⁻¹ * innerQ q D' o := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact filter_subset_filter _ (Nat.divisors_subset_of_dvd hO' hO)
        · intro o _ _; exact mul_nonneg (by positivity) (innerQ_nonneg _ _ _)

/-- The general bound: `Wsum q o₀ O D ≤ ∑_{o₀ ≤ o < m, o ∣ O} q^{-o} inner(o) + 3 m² D q^{-m}`. -/
lemma Wsum_le_split {q : ℕ} (hq : 2 ≤ q) (o₀ O : ℕ) {D : ℕ} (hD : 0 < D) {m : ℕ} (hm : 7 ≤ m) :
    Wsum q o₀ O D ≤ ∑ o ∈ (Ico o₀ m).filter (· ∣ O), ((q : ℚ) ^ o)⁻¹ * innerQ q D o +
      (if O < m then 0 else 3 * (m : ℚ) ^ 2 * D / (q : ℚ) ^ m) := by
  rw [Wsum_eq]
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  refine sum_divisors_le _ (fun o => mul_nonneg (by positivity) (innerQ_nonneg _ _ _))
    (by positivity) hq' (fun o => ?_) O o₀ m hm
  rw [mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (innerQ_le_sq q hD o) (by positivity)

/-- **Soundness of `chkW`.** -/
theorem chkW_sound {q o₀ O D m : ℕ} {W : ℚ} (hq : 2 ≤ q) (h : chkW q o₀ O D m W = true) :
    Wsum q o₀ O D ≤ W := by
  simp only [chkW, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hm, hom⟩, hO⟩, hD⟩, hW⟩ := h
  have hq0 : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqm : (0 : ℚ) < (q : ℚ) ^ m := pow_pos hq0 m
  refine (Wsum_le_split hq o₀ O hD hm).trans ?_
  have e1 : ∑ o ∈ (Ico o₀ m).filter (· ∣ O), ((q : ℚ) ^ o)⁻¹ * innerQ q D o =
      (exactS q q.minFac o₀ O D m : ℚ) / (q : ℚ) ^ m := by
    unfold exactS
    rw [Nat.cast_sum, sum_div]
    apply sum_congr rfl
    intro o ho
    have hom' : o ≤ m := (mem_Ico.mp (mem_filter.mp ho).1).2.le
    rw [Nat.cast_mul, innerN_eq hq, Nat.cast_pow]
    have : (q : ℚ) ^ m = (q : ℚ) ^ (m - o) * (q : ℚ) ^ o := by
      rw [← pow_add, Nat.sub_add_cancel hom']
    rw [this]
    field_simp
  have e2 : (if O < m then 0 else 3 * (m : ℚ) ^ 2 * D / (q : ℚ) ^ m) =
      (tailS O D m : ℚ) / (q : ℚ) ^ m := by
    unfold tailS
    split_ifs <;> push_cast <;> ring
  rw [e1, e2, ← add_div, div_le_iff₀ hqm]
  push_cast at hW ⊢
  exact hW

/-! ### Closure certificates and the crude choice -/

lemma K0c_eq {q : ℕ} (hq : 2 ≤ q) (o₀ : ℕ) : K0c q o₀ = Kzero q o₀ := by
  unfold K0c Kzero; rw [remP_eq (minFac_prime_of_two_le hq)]; rfl

lemma LamC_eq {q : ℕ} (hq : 2 ≤ q) (o₀ : ℕ) : LamC q o₀ = Lambda q o₀ := by
  unfold LamC Lambda; rw [remP_eq (minFac_prime_of_two_le hq)]; rfl

/-- **Soundness of `certOK`** (via `closure_cert`). -/
theorem certOK_sound {q o₀ O D M : ℕ} (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀)
    (h : certOK q o₀ O D M = true) :
    0 < O ∧ 0 < D ∧ Dinf q o₀ ∣ D ∧ Oinf q o₀ ∣ O ∧
      Nstarstar q o₀ ∣ Nat.lcm (Nat.lcm (K0c q o₀) D) O := by
  have hq2 := hq.two_le
  have hp := minFac_prime_of_two_le hq2
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hO, hD⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [remP_eq hp] at h3 h5
  rw [K0c_eq hq2] at h2 ⊢
  have hc := closure_cert q o₀ O D M hq ho₀ (Nat.dvd_of_mod_eq_zero h1) (powMod_modEq h2)
    (Nat.dvd_of_mod_eq_zero h3) (powMod_modEq h4) (Nat.dvd_of_mod_eq_zero h5)
    (Nat.dvd_of_mod_eq_zero h6)
  exact ⟨hO, hD, hc.2.1, hc.2.2.1, hc.2.2.2⟩

lemma Wcl_le_of_certOK {q o₀ O D M : ℕ} (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀)
    (h : certOK q o₀ O D M = true) : Wcl q o₀ ≤ Wsum q o₀ O D := by
  obtain ⟨hO, hD, hDd, hOd, -⟩ := certOK_sound hq ho₀ h
  exact Wsum_mono q o₀ hOd hO.ne' hDd hD

/-- **Soundness of `clOK`**: `W_cl(q, o₀) ≤ W`. -/
theorem clOK_sound {q : ℕ} {W : ℚ} {data : Array (ℕ × ℕ × ℕ)} {o₀ : ℕ} (hq : IsPrimePow q)
    (ho₀ : 1 ≤ o₀) (h : clOK q W data o₀ = true) : Wcl q o₀ ≤ W := by
  simp only [clOK, Bool.and_eq_true] at h
  exact (Wcl_le_of_certOK hq ho₀ h.1).trans (chkW_sound hq.two_le h.2)

/-- **Soundness of `crOK`**: `W_cr(q, o₀) ≤ W`. -/
theorem crOK_sound {q : ℕ} {W : ℚ} {o₀ : ℕ} (hq : 2 ≤ q) (h : crOK q W o₀ = true) :
    Wcr q o₀ ≤ W := by
  unfold crOK at h
  have := chkW_sound hq h
  rw [LamC_eq hq, remP_eq (minFac_prime_of_two_le hq)] at this
  exact this

/-! ### `q ≥ 32`: the uniform bound -/

lemma Lambda_dvd_LamF (q o₀ : ℕ) : Lambda q o₀ ∣ LamF o₀ :=
  Nat.mul_dvd_mul_right (pfree_dvd _ _) _

lemma LamF_pos {o₀ : ℕ} (ho₀ : 1 ≤ o₀) : 0 < LamF o₀ :=
  Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (lcmUpTo_ne_zero o₀))

/-- **Soundness of `chkU`**: `W_cr(q, o₀) ≤ 0.0118` for every prime power `q ≥ 32`. -/
theorem chkU_sound {q o₀ m : ℕ} (h32 : 32 ≤ q) (h : chkU o₀ m = true) : Wcr q o₀ ≤ 0.0118 := by
  simp only [chkU, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hm, hom⟩, hLf⟩, hW⟩ := h
  set L := Lambda q o₀ with hLdef
  set Lf := LamF o₀ with hLfdef
  have hL : 0 < L := Nat.pos_of_ne_zero fun h0 => by
    have := Lambda_dvd_LamF q o₀; rw [← hLdef, h0, zero_dvd_iff] at this; omega
  have hD : 0 < pfree (charOf q) L := pfree_pos _ hL.ne'
  have hDLf : pfree (charOf q) L ≤ Lf :=
    (Nat.le_of_dvd hL (pfree_dvd _ _)).trans (Nat.le_of_dvd hLf (Lambda_dvd_LamF q o₀))
  set U : ℕ → ℚ := fun o => (sigmaN o : ℚ) * Lf / (32 : ℚ) ^ o with hU
  have hq32 : (32 : ℚ) ≤ q := by exact_mod_cast h32
  have hterm : ∀ o, ((q : ℚ) ^ o)⁻¹ * innerQ q (pfree (charOf q) L) o ≤ U o := by
    intro o
    have h1 := innerQ_le_sigma q hD o
    have h2 : (sigmaN o : ℚ) * (pfree (charOf q) L : ℚ) ≤ (sigmaN o : ℚ) * Lf :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hDLf) (by positivity)
    have h3 : ((q : ℚ) ^ o)⁻¹ ≤ ((32 : ℚ) ^ o)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hq32 o)
    calc ((q : ℚ) ^ o)⁻¹ * innerQ q (pfree (charOf q) L) o
        ≤ ((32 : ℚ) ^ o)⁻¹ * ((sigmaN o : ℚ) * Lf) :=
          mul_le_mul h3 (h1.trans h2) (innerQ_nonneg _ _ _) (by positivity)
      _ = U o := by rw [hU]; ring
  have hU0 : ∀ o, 0 ≤ U o := fun o => by rw [hU]; positivity
  have step1 : Wcr q o₀ ≤ ∑ o ∈ Lf.divisors.filter (o₀ ≤ ·), U o := by
    show Wsum q o₀ L (pfree (charOf q) L) ≤ _
    rw [Wsum_eq]
    calc ∑ o ∈ L.divisors.filter (o₀ ≤ ·), ((q : ℚ) ^ o)⁻¹ * innerQ q (pfree (charOf q) L) o
        ≤ ∑ o ∈ L.divisors.filter (o₀ ≤ ·), U o := sum_le_sum fun o _ => hterm o
      _ ≤ ∑ o ∈ Lf.divisors.filter (o₀ ≤ ·), U o :=
          sum_le_sum_of_subset_of_nonneg
            (filter_subset_filter _ (Nat.divisors_subset_of_dvd hLf.ne' (Lambda_dvd_LamF q o₀)))
            fun o _ _ => hU0 o
  have hUle : ∀ o, U o ≤ (o : ℚ) ^ 2 * (Lf : ℚ) / (32 : ℚ) ^ o := by
    intro o
    rw [hU]
    have : (sigmaN o : ℚ) ≤ (o : ℚ) ^ 2 := by rw [sq]; exact_mod_cast sigmaN_le o
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity))
      (by positivity)
  have step2 := sum_divisors_le U hU0 (by positivity) (by norm_num) hUle Lf o₀ m hm
  have e1 : ∑ o ∈ (Ico o₀ m).filter (· ∣ Lf), U o =
      ((∑ o ∈ (Ico o₀ m).filter (· ∣ Lf), sigmaN o * Lf * 32 ^ (m - o) : ℕ) : ℚ) /
        (32 : ℚ) ^ m := by
    rw [Nat.cast_sum, sum_div]
    apply sum_congr rfl
    intro o ho
    have hom' : o ≤ m := (mem_Ico.mp (mem_filter.mp ho).1).2.le
    rw [hU]
    push_cast
    have : (32 : ℚ) ^ m = (32 : ℚ) ^ (m - o) * (32 : ℚ) ^ o := by
      rw [← pow_add, Nat.sub_add_cancel hom']
    rw [this]
    field_simp
  have e2 : (if Lf < m then 0 else 3 * (m : ℚ) ^ 2 * Lf / (32 : ℚ) ^ m) =
      (tailS Lf Lf m : ℚ) / (32 : ℚ) ^ m := by
    unfold tailS
    split_ifs <;> push_cast <;> ring
  rw [e1, e2, ← add_div] at step2
  refine step1.trans (step2.trans ?_)
  rw [div_le_iff₀ (by positivity)]
  push_cast at hW ⊢
  exact hW

/-! ### The Rosser–Schoenfeld tail -/

lemma exp_le_283 : Real.exp 1.03883 ≤ 2.83 := by
  have h1 : Real.exp 1.03883 = Real.exp (103883 / 200000) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_bound' (x := 0.519415) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  rw [h1]
  calc Real.exp (103883 / 200000) ^ 2 ≤
        (464775690368124463693136376659636383 / 276480000000000000000000000000000000) ^ 2 := by
        gcongr
    _ ≤ 2.83 := by norm_num

/-- `lcm(1, …, m) ≤ 2.83^m` (from `ψ(m) < 1.03883 m`, Rosser–Schoenfeld). -/
lemma lcmUpTo_le_real (m : ℕ) : (lcmUpTo m : ℝ) ≤ (2.83 : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [lcmUpTo]
  have hpsi := rosser_schoenfeld_psi (m : ℝ) (by exact_mod_cast hm)
  rw [Chebyshev.psi_eq_log_lcmUpto] at hpsi
  have hpos : (0 : ℝ) < (Nat.lcmUpto m : ℝ) := by exact_mod_cast Nat.lcmUpto_pos m
  have e : (lcmUpTo m : ℝ) = (Nat.lcmUpto m : ℝ) := rfl
  rw [e, ← Real.exp_log hpos]
  calc Real.exp (Real.log (Nat.lcmUpto m)) ≤ Real.exp (m * 1.03883) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp 1.03883 ^ m := Real.exp_nat_mul _ _
    _ ≤ 2.83 ^ m := pow_le_pow_left₀ (Real.exp_pos _).le exp_le_283 m

lemma lcmUpTo_mul_le (m : ℕ) : lcmUpTo m * 100 ^ m ≤ 283 ^ m := by
  have h := lcmUpTo_le_real m
  have e : (2.83 : ℝ) ^ m * 100 ^ m = 283 ^ m := by rw [← mul_pow]; norm_num
  have h2 : (lcmUpTo m : ℝ) * 100 ^ m ≤ 283 ^ m := by
    rw [← e]; exact mul_le_mul_of_nonneg_right h (by positivity)
  exact_mod_cast h2

/-- `W_cr(q, o₀) ≤ 3 o₀³ 283^{o₀} / (100 q)^{o₀}` for `o₀ ≥ 7`. -/
theorem Wcr_le_rs {q : ℕ} (hq : 2 ≤ q) {o₀ : ℕ} (h7 : 7 ≤ o₀) :
    Wcr q o₀ ≤ ((3 * o₀ ^ 3 * 283 ^ o₀ : ℕ) : ℚ) / ((100 * q) ^ o₀ : ℕ) := by
  set L := Lambda q o₀ with hLdef
  have hL : 0 < L := Nat.mul_pos (pfree_pos _ (by omega)) (Nat.pos_of_ne_zero (lcmUpTo_ne_zero o₀))
  have hD : 0 < pfree (charOf q) L := pfree_pos _ hL.ne'
  have h := Wsum_le_split hq o₀ L hD h7
  rw [Ico_self, filter_empty, sum_empty, zero_add] at h
  have h' : Wcr q o₀ ≤ 3 * (o₀ : ℚ) ^ 2 * (pfree (charOf q) L : ℚ) / (q : ℚ) ^ o₀ := by
    refine h.trans ?_
    split_ifs
    · positivity
    · exact le_rfl
  refine h'.trans ?_
  -- `D 100^{o₀} ≤ o₀ 283^{o₀}`
  have hDL : pfree (charOf q) L * 100 ^ o₀ ≤ o₀ * 283 ^ o₀ := by
    have h1 : pfree (charOf q) L ≤ o₀ * lcmUpTo o₀ :=
      (Nat.le_of_dvd hL (pfree_dvd _ _)).trans
        (Nat.le_of_dvd (LamF_pos (by omega)) (Lambda_dvd_LamF q o₀))
    calc pfree (charOf q) L * 100 ^ o₀ ≤ o₀ * lcmUpTo o₀ * 100 ^ o₀ := Nat.mul_le_mul_right _ h1
      _ = o₀ * (lcmUpTo o₀ * 100 ^ o₀) := by ring
      _ ≤ o₀ * 283 ^ o₀ := Nat.mul_le_mul_left _ (lcmUpTo_mul_le o₀)
  have hDL' : (pfree (charOf q) L : ℚ) * 100 ^ o₀ ≤ (o₀ : ℚ) * 283 ^ o₀ := by exact_mod_cast hDL
  have hq0 : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  calc 3 * (o₀ : ℚ) ^ 2 * (pfree (charOf q) L : ℚ) * (100 * (q : ℚ)) ^ o₀
      = 3 * (o₀ : ℚ) ^ 2 * ((pfree (charOf q) L : ℚ) * 100 ^ o₀) * (q : ℚ) ^ o₀ := by
        rw [mul_pow]; ring
    _ ≤ 3 * (o₀ : ℚ) ^ 2 * ((o₀ : ℚ) * 283 ^ o₀) * (q : ℚ) ^ o₀ := by gcongr
    _ = 3 * (o₀ : ℚ) ^ 3 * 283 ^ o₀ * (q : ℚ) ^ o₀ := by ring

lemma ratio_mono {a b o₁ o : ℕ} (h1 : 0 < o₁) (h : (o₁ + 1) ^ 3 * a ≤ o₁ ^ 3 * b)
    (ho : o₁ ≤ o) : (o + 1) ^ 3 * a ≤ o ^ 3 * b := by
  have h2 : (o + 1) * o₁ ≤ (o₁ + 1) * o := by nlinarith
  have h3 : ((o + 1) * o₁) ^ 3 ≤ ((o₁ + 1) * o) ^ 3 := Nat.pow_le_pow_left h2 3
  have h4 : 0 < o₁ ^ 3 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ h4
  calc (o + 1) ^ 3 * a * o₁ ^ 3 = ((o + 1) * o₁) ^ 3 * a := by ring
    _ ≤ ((o₁ + 1) * o) ^ 3 * a := Nat.mul_le_mul_right _ h3
    _ = (o₁ + 1) ^ 3 * a * o ^ 3 := by ring
    _ ≤ o₁ ^ 3 * b * o ^ 3 := Nat.mul_le_mul_right _ h
    _ = o ^ 3 * b * o₁ ^ 3 := by ring

lemma rs_ind {Q o₁ : ℕ} {W : ℚ} (hW : 0 ≤ W) (h1 : 0 < o₁)
    (hb : ((3 * o₁ ^ 3 * 283 ^ o₁ : ℕ) : ℚ) ≤ W * ((Q ^ o₁ : ℕ) : ℚ))
    (hm : (o₁ + 1) ^ 3 * 283 ≤ o₁ ^ 3 * Q) :
    ∀ o, o₁ ≤ o → ((3 * o ^ 3 * 283 ^ o : ℕ) : ℚ) ≤ W * ((Q ^ o : ℕ) : ℚ) := by
  intro o ho
  induction o, ho using Nat.le_induction with
  | base => exact hb
  | succ o ho ih =>
    have hmo : (o + 1) ^ 3 * 283 ≤ o ^ 3 * Q := ratio_mono h1 hm ho
    have hmo' : ((o : ℚ) + 1) ^ 3 * 283 ≤ (o : ℚ) ^ 3 * Q := by exact_mod_cast hmo
    have hpos : (0 : ℚ) < (o : ℚ) ^ 3 := by
      have : 0 < o := by omega
      positivity
    push_cast at ih ⊢
    refine le_of_mul_le_mul_right ?_ hpos
    calc 3 * ((o : ℚ) + 1) ^ 3 * 283 ^ (o + 1) * (o : ℚ) ^ 3
        = (3 * (o : ℚ) ^ 3 * 283 ^ o) * (((o : ℚ) + 1) ^ 3 * 283) := by ring
      _ ≤ (W * (Q : ℚ) ^ o) * (((o : ℚ) + 1) ^ 3 * 283) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ (W * (Q : ℚ) ^ o) * ((o : ℚ) ^ 3 * Q) :=
          mul_le_mul_of_nonneg_left hmo' (by positivity)
      _ = W * (Q : ℚ) ^ (o + 1) * (o : ℚ) ^ 3 := by ring

/-- **Soundness of `rsOK`**: for every `q ≥ q₀` and `o₀ ≥ o₁`, `W_cr(q, o₀) ≤ W`. -/
theorem rsOK_sound {q₀ o₁ : ℕ} {W : ℚ} (hW : 0 ≤ W) (h : rsOK q₀ o₁ W = true) {q : ℕ}
    (hq : 2 ≤ q) (hqq : q₀ ≤ q) {o₀ : ℕ} (ho : o₁ ≤ o₀) : Wcr q o₀ ≤ W := by
  simp only [rsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h7, hb⟩, hm⟩ := h
  have hrs := rs_ind (Q := 100 * q₀) hW (by omega) hb hm o₀ ho
  refine (Wcr_le_rs hq (h7.trans ho)).trans ?_
  have hden : (0 : ℚ) < (((100 * q) ^ o₀ : ℕ) : ℚ) := by
    have : 0 < 100 * q := by omega
    positivity
  rw [div_le_iff₀ hden]
  refine hrs.trans (mul_le_mul_of_nonneg_left ?_ hW)
  exact_mod_cast Nat.pow_le_pow_left (by omega) o₀

/-! ### `q = 2`, `o₀ ≥ 4096` (Lemma 7.5) -/

lemma pow_two_ge_poly : ∀ N, 12 ≤ N → 18 * (N + 1) ^ 2 + 2 * (N + 1) + 7 ≤ 2 ^ N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [pow_succ 2 N]
    nlinarith

lemma two_large_nat {x D₀ P : ℕ} (hx : 4096 ≤ x) (hD : D₀ ≤ x ^ 3) (hP : 2 ^ P ≤ D₀ ^ 2) :
    128 * x ^ 2 * D₀ ^ (P + 1) ≤ 2 ^ x := by
  rcases Nat.eq_zero_or_pos D₀ with rfl | hD0
  · simp
  set N := Nat.log 2 x with hNdef
  have hxlt : x < 2 ^ (N + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hxge : 2 ^ N ≤ x := Nat.pow_log_le_self 2 (by omega)
  have hN : 12 ≤ N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hD3 : D₀ < 2 ^ (3 * (N + 1)) := by
    calc D₀ ≤ x ^ 3 := hD
      _ < (2 ^ (N + 1)) ^ 3 := Nat.pow_lt_pow_left hxlt (by norm_num)
      _ = 2 ^ (3 * (N + 1)) := by rw [← pow_mul, mul_comm]
  have hP6 : P < 6 * (N + 1) := by
    have : 2 ^ P < 2 ^ (6 * (N + 1)) := by
      calc 2 ^ P ≤ D₀ ^ 2 := hP
        _ < (2 ^ (3 * (N + 1))) ^ 2 := Nat.pow_lt_pow_left hD3 (by norm_num)
        _ = 2 ^ (6 * (N + 1)) := by rw [← pow_mul]; ring_nf
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hDP : D₀ ^ (P + 1) ≤ 2 ^ (18 * (N + 1) ^ 2) := by
    calc D₀ ^ (P + 1) ≤ (2 ^ (3 * (N + 1))) ^ (P + 1) := Nat.pow_le_pow_left hD3.le _
      _ ≤ (2 ^ (3 * (N + 1))) ^ (6 * (N + 1)) :=
          Nat.pow_le_pow_right (Nat.one_le_two_pow) (by omega)
      _ = 2 ^ (18 * (N + 1) ^ 2) := by rw [← pow_mul]; ring_nf
  have hx2 : x ^ 2 ≤ 2 ^ (2 * (N + 1)) := by
    calc x ^ 2 ≤ (2 ^ (N + 1)) ^ 2 := Nat.pow_le_pow_left hxlt.le 2
      _ = 2 ^ (2 * (N + 1)) := by rw [← pow_mul, mul_comm]
  calc 128 * x ^ 2 * D₀ ^ (P + 1) ≤ 2 ^ 7 * 2 ^ (2 * (N + 1)) * 2 ^ (18 * (N + 1) ^ 2) := by
        gcongr; norm_num
    _ = 2 ^ (18 * (N + 1) ^ 2 + 2 * (N + 1) + 7) := by rw [← pow_add, ← pow_add]; ring_nf
    _ ≤ 2 ^ (2 ^ N) := Nat.pow_le_pow_right (by norm_num) (pow_two_ge_poly N hN)
    _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hxge

/-- `W_cl(2, o₀) ≤ 3 o₀² D_∞ 2^{-o₀} ≤ 3/128`, stated as `≤ 4/125 = 0.032`, for `o₀ ≥ 4096` (Lemma 7.5). -/
theorem Wcl_two_large {o₀ : ℕ} (h : 4096 ≤ o₀) : Wcl 2 o₀ ≤ 4 / 125 := by
  have hq : IsPrimePow 2 := Nat.prime_two.isPrimePow
  obtain ⟨hD0, P, hP, hDi⟩ := closure_bound 2 o₀ hq (by omega)
  have hDinf : Dinf 2 o₀ ≤ Dseq 2 o₀ 0 ^ (P + 1) := hDi _
  have hDpos : 0 < Dinf 2 o₀ := Nat.pos_of_ne_zero (Dseq_coprime 2 o₀ hq (by omega) _).1
  have hs := Wsum_le_split (q := 2) le_rfl o₀ (Oinf 2 o₀) hDpos (m := o₀) (by omega)
  rw [Ico_self, filter_empty, sum_empty, zero_add] at hs
  have hs' : Wcl 2 o₀ ≤ 3 * (o₀ : ℚ) ^ 2 * (Dinf 2 o₀ : ℚ) / (2 : ℚ) ^ o₀ := by
    refine hs.trans ?_
    split_ifs
    · positivity
    · push_cast; exact le_rfl
  refine hs'.trans ?_
  have key : 128 * o₀ ^ 2 * Dinf 2 o₀ ≤ 2 ^ o₀ :=
    (Nat.mul_le_mul_left _ hDinf).trans (two_large_nat h hD0 hP)
  have key' : 128 * (o₀ : ℚ) ^ 2 * (Dinf 2 o₀ : ℚ) ≤ (2 : ℚ) ^ o₀ := by exact_mod_cast key
  have h2pos : (0 : ℚ) ≤ (2 : ℚ) ^ o₀ := by positivity
  rw [div_le_iff₀ (by positivity)]
  linarith

end MorganMullen.W28
