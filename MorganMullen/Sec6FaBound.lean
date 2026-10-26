import MorganMullen.NT
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

/-!
# Proposition 6.5, analytic part: bounds for `f_a(o)`

`faX p a o` is the function `f_a(o)` of Section 6 with the characteristic `p` as a parameter
(`fa q a o = Msmall.faX (charOf q) a o` by definition). All declarations are in the namespace
`MorganMullen.Msmall` (the bounds for `M` for small `q`, Proposition 6.5).

* `faX_eq_SN`: `o p^a f_a(o) = ∑_{d ∣ o, v_p(d) ≤ a} p^{v_p(d)} min(d, o/d)` (an integer);
* `faX_succ`, `faX_anti`: for `a ≥ v_p(o)`, `f_{a+1}(o) = f_a(o)/p`, so `f_a(o)` decreases in `a`;
* `card_divisors_pow3_le`, `card_divisors_pow4_le_all`: `τ(m)^3 ≤ κ_3^3 m`, `τ(m)^4 ≤ κ_4^4 m` with
  `κ_3^3 = 1536/35`, `κ_4^4 = 127401984/25025` (the classical argument of the paper);
* `faX_le_of_kappa3`, `faX_le_of_kappa4` (the tail bound of Proposition 6.5):
  `f_a(o) ≤ τ(o)/√o ≤ κ_s o^{1/s - 1/2}` (each weight `p^{v_p(d) - a}` is `≤ 1` and each term
  `min(1/d, d/o)` is `≤ 1/√o`; the paper passes through `f(o)`, which gives the same bound).
-/

namespace MorganMullen.Msmall

open MorganMullen Finset

/-- `f_a(o)` with the characteristic `p` as a parameter. -/
noncomputable def faX (p a o : ℕ) : ℚ :=
  ∑ d ∈ o.divisors.filter (fun d => d.factorization p ≤ a),
    (p : ℚ) ^ d.factorization p / (p : ℚ) ^ a * min (1 / (d : ℚ)) ((d : ℚ) / o)

/-- The integer `o p^a f_a(o) = ∑_{d ∣ o, v_p(d) ≤ a} p^{v_p(d)} min(d, o/d)`. -/
def SN (p a o : ℕ) : ℕ :=
  ∑ d ∈ o.divisors, if d.factorization p ≤ a then p ^ d.factorization p * min d (o / d) else 0

lemma min_div_eq {o d : ℕ} (hd : d ∈ o.divisors) :
    min (1 / (d : ℚ)) ((d : ℚ) / o) = ((min d (o / d) : ℕ) : ℚ) / o := by
  have hdo := Nat.dvd_of_mem_divisors hd
  have hdpos : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have ho : o ≠ 0 := Nat.ne_of_gt (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
  obtain ⟨c, hc⟩ := hdo
  have hc' : o / d = c := by rw [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_mem_divisors hd)]
  rw [hc', Nat.cast_min]
  have hoq : (o : ℚ) = d * c := by exact_mod_cast hc
  have hcpos : (0 : ℚ) < c := by
    have : c ≠ 0 := by rintro rfl; simp at hc; exact ho hc
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [hoq, ← min_div_div_right (by positivity : (0 : ℚ) ≤ d * c)]
  have e1 : (d : ℚ) / (d * c) = 1 / c := by field_simp
  have e2 : (c : ℚ) / (d * c) = 1 / d := by field_simp
  rw [e1, e2, min_comm]

lemma faX_eq_SN {p : ℕ} (hp : 0 < p) (a : ℕ) {o : ℕ} (ho : 0 < o) :
    faX p a o = (SN p a o : ℚ) / ((o : ℚ) * (p : ℚ) ^ a) := by
  unfold faX SN
  rw [Finset.sum_filter, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have ho' : (0 : ℚ) < o := by exact_mod_cast ho
  split_ifs with h
  · rw [min_div_eq hd]
    push_cast
    field_simp
  · simp

/-! ### Monotonicity in `a` for `a ≥ v_p(o)` -/

lemma faX_succ {p : ℕ} (a : ℕ) {o : ℕ} (ho : o ≠ 0) (h : o.factorization p ≤ a) :
    faX p (a + 1) o = faX p a o / p := by
  have hall : ∀ b, a ≤ b → o.divisors.filter (fun d => d.factorization p ≤ b) = o.divisors := by
    intro b hb
    apply Finset.filter_true_of_mem
    intro d hd
    exact ((Nat.factorization_le_iff_dvd (Nat.pos_of_mem_divisors hd).ne' ho).mpr
      (Nat.dvd_of_mem_divisors hd) p).trans (h.trans hb)
  unfold faX
  rw [hall a le_rfl, hall (a + 1) (Nat.le_succ a), Finset.sum_div]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pow_succ]
  ring

lemma faX_nonneg (p a o : ℕ) : 0 ≤ faX p a o := by
  unfold faX
  refine Finset.sum_nonneg fun d hd => ?_
  have : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
  have : (0 : ℚ) ≤ o := by exact_mod_cast Nat.zero_le o
  positivity

lemma faX_anti {p : ℕ} (hp : 0 < p) {o : ℕ} (ho : o ≠ 0) {a' : ℕ}
    (h : o.factorization p ≤ a') : ∀ a, a' ≤ a → faX p a o ≤ faX p a' o := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => exact le_rfl
  | succ b hb ih =>
    rw [faX_succ b ho (h.trans hb)]
    have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
    calc faX p b o / p ≤ faX p b o := div_le_self (faX_nonneg p b o) hp1
      _ ≤ faX p a' o := ih

/-! ### `min(1/d, d/o) ≤ 1/√o` -/

/-- `min(1/d, d/o)^2 ≤ 1/o`. -/
lemma min_sq_le {o d : ℕ} (hd : d ∈ o.divisors) :
    min (1 / (d : ℚ)) ((d : ℚ) / o) ^ 2 ≤ 1 / o := by
  have hdpos : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have ho : (0 : ℚ) < o := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  have h1 : min (1 / (d : ℚ)) ((d : ℚ) / o) ≤ 1 / d := min_le_left _ _
  have h2 : min (1 / (d : ℚ)) ((d : ℚ) / o) ≤ d / o := min_le_right _ _
  have h0 : 0 ≤ min (1 / (d : ℚ)) ((d : ℚ) / o) := le_min (by positivity) (by positivity)
  calc min (1 / (d : ℚ)) ((d : ℚ) / o) ^ 2 = min (1 / (d : ℚ)) ((d : ℚ) / o) *
        min (1 / (d : ℚ)) ((d : ℚ) / o) := sq _
    _ ≤ (1 / d) * (d / o) := mul_le_mul h1 h2 h0 (by positivity)
    _ = 1 / o := by field_simp

/-! ### Bounds `τ(m)^s ≤ K m` -/

/-- `τ(m)^s ≤ (∏_{ℓ ∣ m} c ℓ) m` if `(α+1)^s ≤ c ℓ ℓ^α` for the prime powers `ℓ^α ∥ m`. -/
theorem card_divisors_pow_le (c : ℕ → ℚ) (s : ℕ) {m : ℕ} (hm : m ≠ 0)
    (_hc0 : ∀ ℓ ∈ m.primeFactors, 0 ≤ c ℓ)
    (hc : ∀ ℓ ∈ m.primeFactors,
      (((m.factorization ℓ + 1 : ℕ) : ℚ)) ^ s ≤ c ℓ * (ℓ : ℚ) ^ (m.factorization ℓ)) :
    ((m.divisors.card : ℕ) : ℚ) ^ s ≤ (∏ ℓ ∈ m.primeFactors, c ℓ) * m := by
  rw [Nat.card_divisors hm]
  have hmprod : (m : ℚ) = ∏ ℓ ∈ m.primeFactors, (ℓ : ℚ) ^ (m.factorization ℓ) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast; rfl
  rw [hmprod, ← Finset.prod_mul_distrib, Nat.cast_prod, ← Finset.prod_pow]
  apply Finset.prod_le_prod₀
  · intro ℓ _; positivity
  · exact hc

/-- the constants `max_α (α+1)^4/ℓ^α` for `ℓ < 16` (and `1` for `ℓ ≥ 16`). -/
def c4 (ℓ : ℕ) : ℚ :=
  if ℓ = 2 then 81 / 2 else if ℓ = 3 then 256 / 27 else if ℓ = 5 then 81 / 25 else
  if ℓ = 7 then 16 / 7 else if ℓ = 11 then 16 / 11 else if ℓ = 13 then 16 / 13 else 1

lemma pow4_step (α : ℕ) (h : 6 ≤ α) : (α + 2) ^ 4 ≤ 2 * (α + 1) ^ 4 := by
  have h1 : 7 * (α + 2) ≤ 8 * (α + 1) := by omega
  have h2 := Nat.pow_le_pow_left h1 4
  rw [mul_pow, mul_pow] at h2
  norm_num at h2
  omega

lemma pow4_bound (ℓ U D : ℕ) (hℓ : 2 ≤ ℓ) (h : ∀ α ≤ 6, D * (α + 1) ^ 4 ≤ U * ℓ ^ α) :
    ∀ α, D * (α + 1) ^ 4 ≤ U * ℓ ^ α := by
  intro α
  rcases le_or_gt α 6 with hα | hα
  · exact h α hα
  · induction α, (show 6 ≤ α by omega) using Nat.le_induction with
    | base => exact h 6 le_rfl
    | succ k hk ih =>
      have hstep := pow4_step k hk
      have ih' : D * (k + 1) ^ 4 ≤ U * ℓ ^ k := by
        rcases Nat.lt_or_ge 6 k with h6 | h6
        · exact ih h6
        · have : k = 6 := by omega
          subst this; exact h 6 le_rfl
      calc D * (k + 1 + 1) ^ 4 = D * (k + 2) ^ 4 := by ring_nf
        _ ≤ D * (2 * (k + 1) ^ 4) := Nat.mul_le_mul_left D hstep
        _ = 2 * (D * (k + 1) ^ 4) := by ring
        _ ≤ ℓ * (U * ℓ ^ k) := Nat.mul_le_mul hℓ ih'
        _ = U * ℓ ^ (k + 1) := by ring

lemma pow4_le_c4 {ℓ : ℕ} (hℓ : ℓ.Prime) (α : ℕ) :
    (((α + 1 : ℕ) : ℚ)) ^ 4 ≤ c4 ℓ * (ℓ : ℚ) ^ α := by
  have key : ∀ U D : ℕ, 0 < D → c4 ℓ = (U : ℚ) / D → (∀ α ≤ 6, D * (α + 1) ^ 4 ≤ U * ℓ ^ α) →
      (((α + 1 : ℕ) : ℚ)) ^ 4 ≤ c4 ℓ * (ℓ : ℚ) ^ α := by
    intro U D hD hc h
    have := pow4_bound ℓ U D hℓ.two_le h α
    have hD' : (0 : ℚ) < D := by exact_mod_cast hD
    rw [hc, div_mul_eq_mul_div, le_div_iff₀ hD']
    have : ((D * (α + 1) ^ 4 : ℕ) : ℚ) ≤ ((U * ℓ ^ α : ℕ) : ℚ) := by exact_mod_cast this
    push_cast at this ⊢
    linarith
  by_cases h2 : ℓ = 2
  · subst h2; exact key 81 2 (by norm_num) (by simp [c4]) (by decide)
  by_cases h3 : ℓ = 3
  · subst h3; exact key 256 27 (by norm_num) (by simp [c4]) (by decide)
  by_cases h5 : ℓ = 5
  · subst h5; exact key 81 25 (by norm_num) (by simp [c4]) (by decide)
  by_cases h7 : ℓ = 7
  · subst h7; exact key 16 7 (by norm_num) (by simp [c4]) (by decide)
  by_cases h11 : ℓ = 11
  · subst h11; exact key 16 11 (by norm_num) (by simp [c4]) (by decide)
  by_cases h13 : ℓ = 13
  · subst h13; exact key 16 13 (by norm_num) (by simp [c4]) (by decide)
  -- `ℓ ≥ 17`
  have hc : c4 ℓ = 1 := by simp [c4, h2, h3, h5, h7, h11, h13]
  have h16 : 16 ≤ ℓ := by
    by_contra hlt
    push Not at hlt
    interval_cases ℓ <;> first | omega | exact absurd hℓ (by decide)
  rw [hc, one_mul]
  have h1 : α + 1 ≤ 2 ^ α := Nat.lt_two_pow_self
  have : (α + 1) ^ 4 ≤ ℓ ^ α :=
    calc (α + 1) ^ 4 ≤ (2 ^ α) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = 16 ^ α := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ ℓ ^ α := Nat.pow_le_pow_left h16 α
  exact_mod_cast this

lemma one_le_c4 (ℓ : ℕ) : 1 ≤ c4 ℓ := by
  unfold c4; split_ifs <;> norm_num

/-- `τ(m)^4 ≤ (∏_{ℓ ∈ S} c4 ℓ) m` if every prime factor `ℓ` of `m` with `c4 ℓ ≠ 1` lies in `S`. -/
theorem card_divisors_pow4_le (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0)
    (hS : ∀ ℓ ∈ m.primeFactors, c4 ℓ ≠ 1 → ℓ ∈ S) :
    ((m.divisors.card : ℕ) : ℚ) ^ 4 ≤ (∏ ℓ ∈ S, c4 ℓ) * m := by
  have h := card_divisors_pow_le c4 4 hm (fun ℓ _ => (zero_le_one.trans (one_le_c4 ℓ)))
    (fun ℓ hℓ => pow4_le_c4 (Nat.prime_of_mem_primeFactors hℓ) _)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [← Finset.prod_filter_of_ne (p := fun ℓ => ℓ ∈ S) (fun ℓ hℓ hne => hS ℓ hℓ hne)]
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro ℓ hℓ; exact (Finset.mem_filter.mp hℓ).2
  · intro ℓ _; exact zero_le_one.trans (one_le_c4 ℓ)
  · intro ℓ _ _; exact one_le_c4 ℓ

/-! ### The tail bound of the paper: `f_a(o) ≤ f(o) ≤ τ(o)/√o ≤ κ_s o^{1/s - 1/2}` -/

/-- Each weight `p^{v_p(d) - a}` with `v_p(d) ≤ a` is at most `1`, so the weights sum to at most
`τ(o)`. -/
lemma sum_weights_le_card {p : ℕ} (hp : 0 < p) (a o : ℕ) :
    ∑ d ∈ o.divisors.filter (fun d => d.factorization p ≤ a), (p : ℚ) ^ d.factorization p / (p : ℚ) ^ a
      ≤ ((o.divisors.card : ℕ) : ℚ) := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
  calc ∑ d ∈ o.divisors.filter (fun d => d.factorization p ≤ a), (p : ℚ) ^ d.factorization p / (p : ℚ) ^ a
      ≤ ∑ _d ∈ o.divisors.filter (fun d => d.factorization p ≤ a), (1 : ℚ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [div_le_one (by positivity)]
        exact pow_le_pow_right₀ hp1 (Finset.mem_filter.mp hd).2
    _ = (((o.divisors.filter (fun d => d.factorization p ≤ a)).card : ℕ) : ℚ) := by simp
    _ ≤ ((o.divisors.card : ℕ) : ℚ) := by exact_mod_cast Finset.card_filter_le _ _

/-- `f_a(o)^2 o ≤ τ(o)^2`, i.e. `f_a(o) ≤ τ(o)/√o` (each term `min(1/d, d/o)` is at most `1/√o`). -/
lemma faX_sq_mul_le_card {p : ℕ} (hp : 0 < p) (a : ℕ) {o : ℕ} (ho : o ≠ 0) :
    faX p a o ^ 2 * o ≤ ((o.divisors.card : ℕ) : ℚ) ^ 2 := by
  set S := o.divisors.filter (fun d => d.factorization p ≤ a)
  set w : ℕ → ℚ := fun d => (p : ℚ) ^ d.factorization p / (p : ℚ) ^ a
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp
  have ho' : (0 : ℚ) < o := by exact_mod_cast Nat.pos_of_ne_zero ho
  have hw0 : ∀ d, 0 ≤ w d := fun d => by simp only [w]; positivity
  have hCS : faX p a o ^ 2 ≤ (∑ d ∈ S, w d) * ∑ d ∈ S, w d / o := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro d _; exact hw0 d
    · intro d _; have := hw0 d; positivity
    · intro d hd
      have hdo := (Finset.mem_filter.mp hd).1
      have := min_sq_le hdo
      have hwd := hw0 d
      calc (w d * min (1 / (d : ℚ)) ((d : ℚ) / o)) ^ 2
          = w d * w d * min (1 / (d : ℚ)) ((d : ℚ) / o) ^ 2 := by ring
        _ ≤ w d * w d * (1 / o) := mul_le_mul_of_nonneg_left this (mul_nonneg hwd hwd)
        _ = w d * (w d / o) := by ring
  have hW := sum_weights_le_card hp a o
  have hWnn : 0 ≤ ∑ d ∈ S, w d := Finset.sum_nonneg fun d _ => hw0 d
  rw [show ∑ d ∈ S, w d / o = (∑ d ∈ S, w d) / o from (Finset.sum_div _ _ _).symm] at hCS
  calc faX p a o ^ 2 * o ≤ (∑ d ∈ S, w d) * ((∑ d ∈ S, w d) / o) * o :=
        mul_le_mul_of_nonneg_right hCS ho'.le
    _ = (∑ d ∈ S, w d) ^ 2 := by field_simp
    _ ≤ _ := pow_le_pow_left₀ hWnn hW 2

/-- The constants `max_α (α+1)^3/ℓ^α` for the primes `ℓ < 8` (and `1` otherwise); their product is
`κ_3^3 = 8 · 3 · 8/5 · 8/7 = 1536/35` (`κ_3 = 3.5273…`). -/
def c3 (ℓ : ℕ) : ℚ :=
  if ℓ = 2 then 8 else if ℓ = 3 then 3 else if ℓ = 5 then 8 / 5 else if ℓ = 7 then 8 / 7 else 1

lemma pow3_step (α : ℕ) (h : 6 ≤ α) : (α + 2) ^ 3 ≤ 2 * (α + 1) ^ 3 := by
  have h1 : 7 * (α + 2) ≤ 8 * (α + 1) := by omega
  have h2 := Nat.pow_le_pow_left h1 3
  rw [mul_pow, mul_pow] at h2
  norm_num at h2
  omega

lemma pow3_bound (ℓ U D : ℕ) (hℓ : 2 ≤ ℓ) (h : ∀ α ≤ 6, D * (α + 1) ^ 3 ≤ U * ℓ ^ α) :
    ∀ α, D * (α + 1) ^ 3 ≤ U * ℓ ^ α := by
  intro α
  rcases le_or_gt α 6 with hα | hα
  · exact h α hα
  · induction α, (show 6 ≤ α by omega) using Nat.le_induction with
    | base => exact h 6 le_rfl
    | succ k hk ih =>
      have hstep := pow3_step k hk
      have ih' : D * (k + 1) ^ 3 ≤ U * ℓ ^ k := by
        rcases Nat.lt_or_ge 6 k with h6 | h6
        · exact ih h6
        · have : k = 6 := by omega
          subst this; exact h 6 le_rfl
      calc D * (k + 1 + 1) ^ 3 = D * (k + 2) ^ 3 := by ring_nf
        _ ≤ D * (2 * (k + 1) ^ 3) := Nat.mul_le_mul_left D hstep
        _ = 2 * (D * (k + 1) ^ 3) := by ring
        _ ≤ ℓ * (U * ℓ ^ k) := Nat.mul_le_mul hℓ ih'
        _ = U * ℓ ^ (k + 1) := by ring

lemma pow3_le_c3 {ℓ : ℕ} (hℓ : ℓ.Prime) (α : ℕ) :
    (((α + 1 : ℕ) : ℚ)) ^ 3 ≤ c3 ℓ * (ℓ : ℚ) ^ α := by
  have key : ∀ U D : ℕ, 0 < D → c3 ℓ = (U : ℚ) / D → (∀ α ≤ 6, D * (α + 1) ^ 3 ≤ U * ℓ ^ α) →
      (((α + 1 : ℕ) : ℚ)) ^ 3 ≤ c3 ℓ * (ℓ : ℚ) ^ α := by
    intro U D hD hc h
    have := pow3_bound ℓ U D hℓ.two_le h α
    have hD' : (0 : ℚ) < D := by exact_mod_cast hD
    rw [hc, div_mul_eq_mul_div, le_div_iff₀ hD']
    have : ((D * (α + 1) ^ 3 : ℕ) : ℚ) ≤ ((U * ℓ ^ α : ℕ) : ℚ) := by exact_mod_cast this
    push_cast at this ⊢
    linarith
  by_cases h2 : ℓ = 2
  · subst h2; exact key 8 1 (by norm_num) (by simp [c3]) (by decide)
  by_cases h3 : ℓ = 3
  · subst h3; exact key 3 1 (by norm_num) (by simp [c3]) (by decide)
  by_cases h5 : ℓ = 5
  · subst h5; exact key 8 5 (by norm_num) (by simp [c3]) (by decide)
  by_cases h7 : ℓ = 7
  · subst h7; exact key 8 7 (by norm_num) (by simp [c3]) (by decide)
  -- `ℓ ≥ 11`
  have hc : c3 ℓ = 1 := by simp [c3, h2, h3, h5, h7]
  have h8 : 8 ≤ ℓ := by
    by_contra hlt
    push Not at hlt
    interval_cases ℓ <;> first | omega | exact absurd hℓ (by decide)
  rw [hc, one_mul]
  have h1 : α + 1 ≤ 2 ^ α := Nat.lt_two_pow_self
  have : (α + 1) ^ 3 ≤ ℓ ^ α :=
    calc (α + 1) ^ 3 ≤ (2 ^ α) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = 8 ^ α := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ ℓ ^ α := Nat.pow_le_pow_left h8 α
  exact_mod_cast this

lemma one_le_c3 (ℓ : ℕ) : 1 ≤ c3 ℓ := by
  unfold c3; split_ifs <;> norm_num

/-- `τ(m)^3 ≤ κ_3^3 m` with `κ_3^3 = 1536/35`. -/
theorem card_divisors_pow3_le {m : ℕ} (hm : m ≠ 0) :
    ((m.divisors.card : ℕ) : ℚ) ^ 3 ≤ 1536 / 35 * m := by
  have h := card_divisors_pow_le c3 3 hm (fun ℓ _ => (zero_le_one.trans (one_le_c3 ℓ)))
    (fun ℓ hℓ => pow3_le_c3 (Nat.prime_of_mem_primeFactors hℓ) _)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hS : ∀ ℓ ∈ m.primeFactors, c3 ℓ ≠ 1 → ℓ ∈ ({2, 3, 5, 7} : Finset ℕ) := by
    intro ℓ _ hne
    simp only [Finset.mem_insert, Finset.mem_singleton]
    unfold c3 at hne
    split_ifs at hne <;> first | omega | exact absurd rfl hne
  rw [← Finset.prod_filter_of_ne (p := fun ℓ => ℓ ∈ ({2, 3, 5, 7} : Finset ℕ)) hS]
  have e : (∏ ℓ ∈ ({2, 3, 5, 7} : Finset ℕ), c3 ℓ) = 1536 / 35 := by simp [c3]; norm_num
  rw [← e]
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro ℓ hℓ; exact (Finset.mem_filter.mp hℓ).2
  · intro ℓ _; exact zero_le_one.trans (one_le_c3 ℓ)
  · intro ℓ _ _; exact one_le_c3 ℓ

/-- `τ(m)^4 ≤ κ_4^4 m` with `κ_4^4 = ∏_{ℓ < 16} max_α (α+1)^4/ℓ^α = 127401984/25025`
(`κ_4 = 8.4470…`). -/
theorem card_divisors_pow4_le_all {m : ℕ} (hm : m ≠ 0) :
    ((m.divisors.card : ℕ) : ℚ) ^ 4 ≤ 127401984 / 25025 * m := by
  have := card_divisors_pow4_le {2, 3, 5, 7, 11, 13} hm (by
    intro ℓ _ hne
    simp only [Finset.mem_insert, Finset.mem_singleton]
    unfold c4 at hne
    split_ifs at hne <;> first | omega | exact absurd rfl hne)
  have e : (∏ ℓ ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), c4 ℓ) = 127401984 / 25025 := by
    simp [c4]; norm_num
  rwa [e] at this

/-- **Tail bound of Proposition 6.5** (with `κ_3`): `f_a(o) ≤ τ(o)/√o ≤ κ_3 o^{-1/6}`; hence
`f_a(o) ≤ ϑ` for `o ≥ N` as soon as `κ_3^6 ≤ ϑ^6 N`. -/
theorem faX_le_of_kappa3 {p : ℕ} (hp : 0 < p) (a : ℕ) (ϑ : ℚ) (N : ℕ) (hϑ : 0 ≤ ϑ)
    (hN : (1536 / 35 : ℚ) ^ 2 ≤ ϑ ^ 6 * N) {o : ℕ} (ho : N ≤ o) (ho0 : o ≠ 0) :
    faX p a o ≤ ϑ := by
  set F := faX p a o
  set τ : ℚ := ((o.divisors.card : ℕ) : ℚ)
  have hF0 : 0 ≤ F := faX_nonneg p a o
  have ho' : (0 : ℚ) < o := by exact_mod_cast Nat.pos_of_ne_zero ho0
  have h1 : F ^ 2 * o ≤ τ ^ 2 := faX_sq_mul_le_card hp a ho0
  have h2 : τ ^ 3 ≤ 1536 / 35 * o := card_divisors_pow3_le ho0
  have hτ0 : 0 ≤ τ := by positivity
  have h3 : F ^ 6 * (o : ℚ) ^ 3 ≤ τ ^ 6 := by
    have := pow_le_pow_left₀ (by positivity) h1 3
    calc F ^ 6 * (o : ℚ) ^ 3 = (F ^ 2 * o) ^ 3 := by ring
      _ ≤ (τ ^ 2) ^ 3 := this
      _ = τ ^ 6 := by ring
  have h4 : τ ^ 6 ≤ (1536 / 35) ^ 2 * (o : ℚ) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    calc τ ^ 6 = (τ ^ 3) ^ 2 := by ring
      _ ≤ (1536 / 35 * (o : ℚ)) ^ 2 := this
      _ = (1536 / 35) ^ 2 * (o : ℚ) ^ 2 := by ring
  have h5 : F ^ 6 * o ≤ (1536 / 35) ^ 2 := by
    have h6 : (F ^ 6 * o) * (o : ℚ) ^ 2 ≤ (1536 / 35) ^ 2 * (o : ℚ) ^ 2 := by
      calc (F ^ 6 * o) * (o : ℚ) ^ 2 = F ^ 6 * (o : ℚ) ^ 3 := by ring
        _ ≤ _ := h3.trans h4
    exact le_of_mul_le_mul_right h6 (by positivity)
  have h7 : F ^ 6 * o ≤ ϑ ^ 6 * o :=
    h5.trans (hN.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast ho) (by positivity)))
  have h8 : F ^ 6 ≤ ϑ ^ 6 := le_of_mul_le_mul_right h7 ho'
  exact (pow_le_pow_iff_left₀ hF0 hϑ (by norm_num)).mp h8

/-- **Tail bound of Proposition 6.5** (with `κ_4`): `f_a(o) ≤ τ(o)/√o ≤ κ_4 o^{-1/4}`; hence
`f_a(o) ≤ ϑ` for `o ≥ N` as soon as `κ_4^4 ≤ ϑ^4 N`. -/
theorem faX_le_of_kappa4 {p : ℕ} (hp : 0 < p) (a : ℕ) (ϑ : ℚ) (N : ℕ) (hϑ : 0 ≤ ϑ)
    (hN : (127401984 / 25025 : ℚ) ≤ ϑ ^ 4 * N) {o : ℕ} (ho : N ≤ o) (ho0 : o ≠ 0) :
    faX p a o ≤ ϑ := by
  set F := faX p a o
  set τ : ℚ := ((o.divisors.card : ℕ) : ℚ)
  set K : ℚ := 127401984 / 25025
  have hF0 : 0 ≤ F := faX_nonneg p a o
  have ho' : (0 : ℚ) < o := by exact_mod_cast Nat.pos_of_ne_zero ho0
  have h1 : F ^ 2 * o ≤ τ ^ 2 := faX_sq_mul_le_card hp a ho0
  have h2 : τ ^ 4 ≤ K * o := card_divisors_pow4_le_all ho0
  have hτ0 : 0 ≤ τ := by positivity
  have h3 : (F ^ 4 * o) * (F ^ 4 * o) * (o : ℚ) ^ 2 ≤ (K * o) * (K * o) := by
    have h1' := pow_le_pow_left₀ (by positivity) h1 4
    have h2' := pow_le_pow_left₀ (by positivity) h2 2
    calc (F ^ 4 * o) * (F ^ 4 * o) * (o : ℚ) ^ 2 = (F ^ 2 * o) ^ 4 := by ring
      _ ≤ (τ ^ 2) ^ 4 := h1'
      _ = (τ ^ 4) ^ 2 := by ring
      _ ≤ (K * o) ^ 2 := h2'
      _ = (K * o) * (K * o) := by ring
  have h4 : (F ^ 4 * o) * (F ^ 4 * o) ≤ K * K := by
    have : (F ^ 4 * o) * (F ^ 4 * o) * (o : ℚ) ^ 2 ≤ (K * K) * (o : ℚ) ^ 2 := by
      calc _ ≤ (K * o) * (K * o) := h3
        _ = (K * K) * (o : ℚ) ^ 2 := by ring
    exact le_of_mul_le_mul_right this (by positivity)
  have hK0 : 0 ≤ K := by norm_num [K]
  have h5 : F ^ 4 * o ≤ K := by
    have hA : 0 ≤ F ^ 4 * o := by positivity
    nlinarith
  have h7 : F ^ 4 * o ≤ ϑ ^ 4 * o :=
    h5.trans (hN.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast ho) (by positivity)))
  have h8 : F ^ 4 ≤ ϑ ^ 4 := le_of_mul_le_mul_right h7 ho'
  exact (pow_le_pow_iff_left₀ hF0 hϑ (by norm_num)).mp h8

end MorganMullen.Msmall
