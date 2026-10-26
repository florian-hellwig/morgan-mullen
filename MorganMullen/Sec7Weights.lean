import MorganMullen.Sec7Structure
import MorganMullen.Sec7Exact
import MorganMullen.Axioms
import MorganMullen.Sec7W28Sound
import MorganMullen.Sec7W28Runs
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Section 7 (continued): Theorem 7.8 (the weight bounds `W(q)`)

Proof of Theorem 7.8 (`weight_le_Wq`). Let `o₀ ≥ 2` be the minimal codimension of the component.

* `(q, o₀) ∈ {(2,3), (2,6), (3,2), (3,4)}`: Proposition 7.7 (`finite_reduction_weight`), the closure
  certificates `N** ∣ 42, 378, 16, 320` (`W28.Nss_exc`) and the checked labelling of step (i)
  (`exact_max_bound`: weight `≤ 3/4` resp. `≤ 4/9` for all `n₀ ∣ N**`; the exact maxima are not formalised);
* `q = 2`: `W_cl(2, o₀) ≤ 3/4`, and `≤ 0.032` for `o₀ ≥ 9` (certificates for `o₀ ≤ 4095`,
  Lemma 7.5 beyond; `W28.Wcl_two`, `W28.Wcl_two_small`);
* `q = 3`: `W_cl(3, o₀) ≤ 4/9`, and `≤ 0.051` for `o₀ ≥ 7`, for `o₀ ≤ 374` (certificates);
  `W_cr(3, o₀) ≤ 0.051` beyond (Rosser–Schoenfeld); `W28.Wcl_Wcr_three`, `W28.Wcl_Wcr_three_small`;
* `4 ≤ q ≤ 31`: `W_cr(q, o₀) ≤ W(q)` (exact sums for small `o₀`, Rosser–Schoenfeld beyond,
  `W28.Wcr_fixed`);
* `q ≥ 32`: `W_cr(q, o₀) ≤ 0.0118` uniformly in `q` (`W28.Wcr_big`).

The computations are in `Sec7W28Defs.lean` / `Sec7W28Runs.lean`, their soundness in
`Sec7W28Sound.lean`.
-/

namespace MorganMullen

open Finset

/-- The weight bounds `W(q)` of Theorem 7.8 (for `q ≥ 32` the uniform bound `0.0118`). -/
def Wq : ℕ → ℚ
  | 2 => 3 / 4
  | 3 => 4 / 9
  | 4 => 0.2946
  | 5 => 0.3392
  | 7 => 0.1683
  | 8 => 0.0469
  | 9 => 0.1006
  | 11 => 0.0670
  | 13 => 0.0478
  | 16 => 0.0118
  | 17 => 0.0279
  | 19 => 0.0223
  | 23 => 0.0152
  | 25 => 0.0129
  | 27 => 0.0110
  | 29 => 0.0096
  | 31 => 0.0084
  | _ => 0.0118

theorem Wq_pos_lt_one (q : ℕ) : 0 < Wq q ∧ Wq q < 1 := by
  unfold Wq
  split <;> norm_num

namespace W28

/-- `q = 2`: `W_cl(2, o₀) ≤ 3/4` for `o₀ ≥ 2`, `o₀ ∉ {3, 6}`, and `W_cl(2, o₀) ≤ 0.032` for
`o₀ ≥ 9`. -/
theorem Wcl_two_tgt {o₀ : ℕ} (h2 : 2 ≤ o₀) (h3 : o₀ ≠ 3) (h6 : o₀ ≠ 6) : Wcl 2 o₀ ≤ tgt2 o₀ := by
  rcases Nat.lt_or_ge o₀ 4096 with h | h
  · have hr := run2_ok
    unfold run2 at hr
    rw [List.all_eq_true] at hr
    have hc := hr o₀ (List.mem_range'_1.mpr ⟨h2, by omega⟩)
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with (hc | hc) | hc
    · exact absurd hc h3
    · exact absurd hc h6
    · exact clOK_sound Nat.prime_two.isPrimePow (by omega) hc
  · have : tgt2 o₀ = 4 / 125 := by unfold tgt2; simp only [show ¬ o₀ ≤ 8 by omega, ↓reduceIte]
    rw [this]; exact Wcl_two_large h

theorem Wcl_two {o₀ : ℕ} (h2 : 2 ≤ o₀) (h3 : o₀ ≠ 3) (h6 : o₀ ≠ 6) : Wcl 2 o₀ ≤ 3 / 4 := by
  refine (Wcl_two_tgt h2 h3 h6).trans ?_
  unfold tgt2; split_ifs <;> norm_num

/-- `q = 2`, `o₀ ≥ 9`: `W_cl(2, o₀) ≤ 0.032` (the bounds of Theorem 7.8 apart from the exact
maxima). -/
theorem Wcl_two_small {o₀ : ℕ} (h9 : 9 ≤ o₀) : Wcl 2 o₀ ≤ 4 / 125 := by
  have := Wcl_two_tgt (o₀ := o₀) (by omega) (by omega) (by omega)
  unfold tgt2 at this; simpa only [show ¬ o₀ ≤ 8 by omega, ↓reduceIte] using this

/-- `q = 3`: `W_cl(3, o₀) ≤ tgt3 o₀` (`4/9` for `o₀ ≤ 6`, `0.051` beyond) or
`W_cr(3, o₀) ≤ 0.051`, for `o₀ ≥ 3`, `o₀ ≠ 4`. -/
theorem Wcl_Wcr_three_tgt {o₀ : ℕ} (h3 : 3 ≤ o₀) (h4 : o₀ ≠ 4) :
    Wcl 3 o₀ ≤ tgt3 o₀ ∨ Wcr 3 o₀ ≤ 51 / 1000 := by
  rcases Nat.lt_or_ge o₀ 375 with h | h
  · left
    have hr := run3_ok
    unfold run3 at hr
    rw [List.all_eq_true] at hr
    have hc := hr o₀ (List.mem_range'_1.mpr ⟨h3, by omega⟩)
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with hc | hc
    · exact absurd hc h4
    · exact clOK_sound Nat.prime_three.isPrimePow (by omega) hc
  · right
    have hr := runBig_ok
    simp only [runBig, Bool.and_eq_true] at hr
    exact rsOK_sound (by norm_num) hr.2 (q := 3) (by norm_num) le_rfl h

/-- `q = 3`: `W_cl(3, o₀) ≤ 4/9` or `W_cr(3, o₀) ≤ 4/9` for `o₀ ≥ 3`, `o₀ ≠ 4`. -/
theorem Wcl_Wcr_three {o₀ : ℕ} (h3 : 3 ≤ o₀) (h4 : o₀ ≠ 4) :
    Wcl 3 o₀ ≤ 4 / 9 ∨ Wcr 3 o₀ ≤ 4 / 9 := by
  rcases Wcl_Wcr_three_tgt h3 h4 with h | h
  · left; refine h.trans ?_; unfold tgt3; split_ifs <;> norm_num
  · right; exact h.trans (by norm_num)

/-- `q = 3`, `o₀ ≥ 7`: the bound is at most `0.051` (the bounds of Theorem 7.8 apart from the exact
maxima). -/
theorem Wcl_Wcr_three_small {o₀ : ℕ} (h7 : 7 ≤ o₀) :
    Wcl 3 o₀ ≤ 51 / 1000 ∨ Wcr 3 o₀ ≤ 51 / 1000 := by
  rcases Wcl_Wcr_three_tgt (o₀ := o₀) (by omega) (by omega) with h | h
  · left; unfold tgt3 at h; simpa only [show ¬ o₀ ≤ 6 by omega, ↓reduceIte] using h
  · right; exact h

/-- `q ≥ 32`: `W_cr(q, o₀) ≤ 0.0118` for `o₀ ≥ 2`. -/
theorem Wcr_big {q o₀ : ℕ} (h32 : 32 ≤ q) (ho₀ : 2 ≤ o₀) : Wcr q o₀ ≤ 0.0118 := by
  have hr := runBig_ok
  simp only [runBig, Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨hU, hrs⟩, -⟩ := hr
  rcases Nat.lt_or_ge o₀ 7 with h | h
  · exact chkU_sound h32 (hU o₀ (List.mem_range'_1.mpr ⟨ho₀, by omega⟩))
  · exact rsOK_sound (by norm_num) hrs (by omega) h32 h

/-- `4 ≤ q ≤ 31`: `W_cr(q, o₀) ≤ W` for the entries `(q, o₁, W)` of `qtab`. -/
theorem Wcr_fixed {q o₁ : ℕ} {W : ℚ} (hmem : (q, o₁, W) ∈ qtab) (hW : 0 ≤ W) (hq : 2 ≤ q)
    {o₀ : ℕ} (ho₀ : 2 ≤ o₀) : Wcr q o₀ ≤ W := by
  have hr := runFixed_ok
  unfold runFixed at hr
  rw [List.all_eq_true] at hr
  have hf := hr _ hmem
  simp only [fixedOK, Bool.and_eq_true, List.all_eq_true] at hf
  obtain ⟨hcr, hrs⟩ := hf
  rcases Nat.lt_or_ge o₀ o₁ with h | h
  · exact crOK_sound hq (hcr o₀ (List.mem_range'_1.mpr ⟨ho₀, by omega⟩))
  · exact rsOK_sound hW hrs hq le_rfl h

/-- The exceptional cases: `N** ∣ 42, 378, 16, 320` for `(q, o₀) = (2,3), (2,6), (3,2), (3,4)`. -/
theorem Nss_exc :
    Nstarstar 2 3 ∣ 42 ∧ Nstarstar 2 6 ∣ 378 ∧ Nstarstar 3 2 ∣ 16 ∧ Nstarstar 3 4 ∣ 320 := by
  have hr := runExc_ok
  simp only [runExc, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, d1⟩, h2⟩, d2⟩, h3⟩, d3⟩, h4⟩, d4⟩ := hr
  have hp2 : IsPrimePow 2 := Nat.prime_two.isPrimePow
  have hp3 : IsPrimePow 3 := Nat.prime_three.isPrimePow
  exact ⟨(certOK_sound hp2 (by norm_num) h1).2.2.2.2.trans d1,
    (certOK_sound hp2 (by norm_num) h2).2.2.2.2.trans d2,
    (certOK_sound hp3 (by norm_num) h3).2.2.2.2.trans d3,
    (certOK_sound hp3 (by norm_num) h4).2.2.2.2.trans d4⟩

end W28

lemma Wq_of_ge {q : ℕ} (h : 32 ≤ q) : Wq q = 0.0118 := by
  unfold Wq
  split <;> first | omega | rfl

/-- A prime power divisible by the prime `a` is a power of `a`; so `n` is not a prime power if
`a ∣ n` and no `a^k` (`k ≤ n`) equals `n`. -/
lemma not_isPrimePow_of_pow {n a : ℕ} (ha : a.Prime) (han : a ∣ n) (hno : ∀ k ≤ n, a ^ k ≠ n) :
    ¬ IsPrimePow n := by
  rintro ⟨p, k, hp, -, rfl⟩
  have hp' := Nat.prime_iff.mpr hp
  have hap : a = p := (Nat.prime_dvd_prime_iff_eq ha hp').mp (ha.dvd_of_dvd_pow han)
  subst hap
  have hk : k ≤ a ^ k := (Nat.lt_pow_self ha.one_lt).le
  exact hno k hk rfl

lemma Wcr_le_Wq_tab {q : ℕ} (hmem : ∃ o₁, (q, o₁, Wq q) ∈ W28.qtab) (hq : 2 ≤ q) {o₀ : ℕ}
    (ho₀ : 2 ≤ o₀) : Wcr q o₀ ≤ Wq q :=
  W28.Wcr_fixed hmem.choose_spec (Wq_pos_lt_one q).1.le hq ho₀

/-- **Theorem 7.8** (weights): every component without a condition of
codimension `1` has weight at most `W(q)`. -/
theorem weight_le_Wq (q n : ℕ) [NeZero n] (hq : IsPrimePow q)
    {K : Finset (Model.Cond q n)} (hK : K ∈ Model.components q n (Model.essConds q n))
    (hK2 : ∀ C ∈ K, 2 ≤ Model.codim q n C) :
    Model.weight q n K ≤ Wq q := by
  classical
  -- the minimal codimension `o₀ ≥ 2`
  have hne : K.Nonempty := by
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hK
    exact ⟨C, Finset.mem_filter.mpr ⟨hC, Relation.EqvGen.refl C⟩⟩
  obtain ⟨C₀, hC₀, hmin⟩ := Finset.exists_min_image K (Model.codim q n) hne
  obtain ⟨o₀, hmin'⟩ : ∃ o₀, Model.IsMinCodim q n K o₀ := ⟨_, ⟨C₀, hC₀, rfl⟩, hmin⟩
  have ho₀ : 2 ≤ o₀ := by obtain ⟨⟨C, hC, rfl⟩, -⟩ := hmin'; exact hK2 C hC
  have hW := Model.weight_le_Wcl_Wcr q n hq hK hK2 hmin'
  by_cases hex : (q = 2 ∧ (o₀ = 3 ∨ o₀ = 6)) ∨ (q = 3 ∧ (o₀ = 2 ∨ o₀ = 4))
  · -- the exceptional cases: finite reduction and the exact maxima
    obtain ⟨n₀, hn₀, hdvd, K₀, hK₀, hmin₀, hw⟩ := finite_reduction_weight q n hq ho₀ hK hmin'
    have hK₀2 : ∀ C ∈ K₀, 2 ≤ Model.codim q n₀ C := fun C hC => ho₀.trans (hmin₀.2 C hC)
    obtain ⟨e1, e2, e3, e4⟩ := W28.Nss_exc
    have hN : (q = 2 ∧ (n₀ ∣ 42 ∨ n₀ ∣ 378)) ∨ (q = 3 ∧ (n₀ ∣ 16 ∨ n₀ ∣ 320)) := by
      rcases hex with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ <;> rw [h] at hdvd
      · exact Or.inl ⟨rfl, Or.inl (hdvd.trans e1)⟩
      · exact Or.inl ⟨rfl, Or.inr (hdvd.trans e2)⟩
      · exact Or.inr ⟨rfl, Or.inl (hdvd.trans e3)⟩
      · exact Or.inr ⟨rfl, Or.inr (hdvd.trans e4)⟩
    have hb := exact_max_bound q n₀ hN hK₀ hK₀2
    rw [← hw]
    rcases hex with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simpa [Wq] using hb
    · simpa [Wq] using hb
  · have hq2 := hq.two_le
    rcases Nat.lt_or_ge q 4 with hq4 | hq4
    · interval_cases q
      · have h3 : o₀ ≠ 3 := fun h => hex (Or.inl ⟨rfl, Or.inl h⟩)
        have h6 : o₀ ≠ 6 := fun h => hex (Or.inl ⟨rfl, Or.inr h⟩)
        exact hW.1.trans (W28.Wcl_two ho₀ h3 h6)
      · have h2 : o₀ ≠ 2 := fun h => hex (Or.inr ⟨rfl, Or.inl h⟩)
        have h4 : o₀ ≠ 4 := fun h => hex (Or.inr ⟨rfl, Or.inr h⟩)
        rcases W28.Wcl_Wcr_three (by omega) h4 with h | h
        · exact hW.1.trans h
        · exact hW.2.trans h
    · rcases Nat.lt_or_ge q 32 with h32 | h32
      · refine hW.2.trans ?_
        interval_cases q <;>
          first
          | exact absurd hq (not_isPrimePow_of_pow Nat.prime_two (by decide) (by decide))
          | exact absurd hq (not_isPrimePow_of_pow Nat.prime_three (by decide) (by decide))
          | exact Wcr_le_Wq_tab (by simp [W28.qtab, Wq]) (by norm_num) ho₀
      · rw [Wq_of_ge h32]
        exact hW.2.trans (W28.Wcr_big h32 ho₀)

end MorganMullen
