import MorganMullen.NT
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Nth

/-!
# Section 5: prime factors of `q^n - 1` and essential types

* Lemma 5.1, first bound: `ω(q^n - 1) ≤ ω(q - 1) + ∑_{k ∣ n, k > 1} t_k` via the numbers `t_k`
  (`omega_le_omegaBd`).
* Lemma 5.1, second bound: `t_k log₂(lcm(2,k) + 1) ≤ φ(k) log₂ q + c_q` with
  `c_q = -∑_{j ≥ 1} log₂(1 - q^{-j})` (`cq`, `summable_cq`, `tk_mul_logb_le`; product form
  `lcm_add_one_pow_tk_le`), from `Φ_k(q) = q^{φ(k)} ∏_{j ∣ k} (1 - q^{-j})^{μ(k/j)}
  ≤ q^{φ(k)} ∏_{j ≥ 1} (1 - q^{-j})^{-1} = q^{φ(k)} 2^{c_q}` (`cycloVal_le_pow_mul_two_rpow_cq`),
  proved in logarithmic form by Möbius inversion of `∏_{d ∣ n} Φ_d(q) = q^n - 1`
  (`log_cycloVal_eq`). A rational upper bound `c_q ≤ cqUpper q` (within `0.15 %` of
  `c_2 = 1.7919…`) and its integer version `S c_q ≤ cqCeil S q` (`cq_le_cqUpper`,
  `mul_cq_le_cqCeil`).
* A computable upper bound `tUpper q k ≥ t_k` used by the verified computations of Section 8:
  for small `φ(k)` the exact `t_k` (exact value of `Φ_k(q)`, candidates `≡ 1 (mod lcm(2,k))`
  sieved by trial division), otherwise the second bound of Lemma 5.1 evaluated with integer
  logarithms (`tk_le_tUpper`).
* Lemma 5.2 is in `Sec5Types.lean`.

Implementation notes.
* `cycloNat k q = Φ_k(q)` is computed by the recursion `Φ_{np}(x) = Φ_n(x^p)` (`p ∣ n`),
  `Φ_{np}(x) = Φ_n(x^p) / Φ_n(x)` (`p ∤ n`), from `Polynomial.cyclotomic_expand_eq_cyclotomic(_mul)`.
* The trial division of the sieve (`detComposite`) is done by two `gcd`s with the products of the
  primes below `2^8` and `2^14` (exact for candidates `< 2^28`, with a `minFac` fallback beyond);
  soundness only uses that a prime is never declared composite.
* The infinitude of the primes `≡ 1 (mod m)` (`exists_prime_gt_modEq_one'`) is Mathlib's
  `Nat.exists_prime_gt_modEq_one`, reproduced here with Mathlib's proof (via cyclotomic polynomials).
* `cqUpper` uses `-ln(1 - y) ≤ y + y²/2 + y³/3 + y⁴/4 + y⁵/(5(1 - y))` (from the logarithmic
  series) and `ln 2 > 10000/14427` (a partial sum of the series of `-ln(1 - 1/2)`).
-/

namespace MorganMullen

open Finset

/-- The `j`-th prime (from `j = 0`) that is `≡ 1 (mod m)`. -/
noncomputable def primeCong (m j : ℕ) : ℕ := Nat.nth (fun ℓ => ℓ.Prime ∧ ℓ % m = 1) j

/-- `Φ_k(q)` as an integer. -/
noncomputable def cycloVal (k q : ℕ) : ℤ := (Polynomial.cyclotomic k ℤ).eval (q : ℤ)

/-- `t_k`: the largest `t` such that the product of the `t` smallest primes `≡ 1 (mod lcm(2,k))` is at
most `Φ_k(q)`. -/
noncomputable def tk (q k : ℕ) : ℕ :=
  sSup {t | ((∏ j ∈ range t, primeCong (Nat.lcm 2 k) j : ℕ) : ℤ) ≤ cycloVal k q}

/-- The bound of Lemma 5.1 for `ω(q^n - 1)`: `ω(q - 1) + ∑_{k ∣ n, k > 1} t_k`. -/
noncomputable def omegaBd (q n : ℕ) : ℕ :=
  (q - 1).primeFactors.card + ∑ k ∈ n.divisors.filter (1 < ·), tk q k

/-! ### Primes `≡ 1 (mod m)` -/

section PrimesCongOne

open Polynomial Nat

/-- For `k ≠ 0` and every `n` there is a prime `p > n` with `p ≡ 1 (mod k)`: Mathlib's
`Nat.exists_prime_gt_modEq_one`, reproduced here with Mathlib's proof. -/
theorem exists_prime_gt_modEq_one' {k : ℕ} (n : ℕ) (hk0 : k ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≡ 1 [MOD k] := by
  rcases (one_le_iff_ne_zero.2 hk0).eq_or_lt with (rfl | hk1)
  · rcases exists_infinite_primes (n + 1) with ⟨p, hnp, hp⟩
    exact ⟨p, hp, hnp, modEq_one⟩
  let b := k * (n !)
  have hgt : 1 < (eval (↑b) (cyclotomic k ℤ)).natAbs := by
    rcases le_iff_exists_add'.1 hk1.le with ⟨k, rfl⟩
    have hb : 2 ≤ b := le_mul_of_le_of_one_le hk1 n.factorial_pos
    calc
      1 ≤ b - 1 := le_tsub_of_add_le_left hb
      _ < (eval (b : ℤ) (cyclotomic (k + 1) ℤ)).natAbs :=
        sub_one_lt_natAbs_cyclotomic_eval hk1 (succ_le_iff.1 hb).ne'
  let p := minFac (eval (↑b) (cyclotomic k ℤ)).natAbs
  have hprime : Fact p.Prime := ⟨minFac_prime (_root_.ne_of_lt hgt).symm⟩
  have hroot : IsRoot (cyclotomic k (ZMod p)) (castRingHom (ZMod p) b) := by
    have : ((b : ℤ) : ZMod p) = ↑(Int.castRingHom (ZMod p) b) := by simp
    rw [IsRoot.def, ← map_cyclotomic_int k (ZMod p), eval_map, coe_castRingHom,
      ← Int.cast_natCast, this, eval₂_hom, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply Int.dvd_natAbs.1
    exact mod_cast minFac_dvd (eval (↑b) (cyclotomic k ℤ)).natAbs
  have hpb : ¬p ∣ b :=
    hprime.1.coprime_iff_not_dvd.1 (coprime_of_root_cyclotomic hk0.bot_lt hroot).symm
  refine ⟨p, hprime.1, not_le.1 fun habs => ?_, ?_⟩
  · exact hpb (dvd_mul_of_dvd_right (dvd_factorial (minFac_pos _) habs) _)
  · have hdiv : orderOf (b : ZMod p) ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one (mt (CharP.cast_eq_zero_iff _ _ _).1 hpb)
    have : NeZero (k : ZMod p) :=
      NeZero.of_not_dvd (ZMod p) fun hpk => hpb (dvd_mul_of_dvd_left hpk _)
    have : k = orderOf (b : ZMod p) := (isRoot_cyclotomic_iff.mp hroot).eq_orderOf
    rw [← this] at hdiv
    exact ((modEq_iff_dvd' hprime.1.pos).2 hdiv).symm

end PrimesCongOne

lemma infinite_primeCongSet {m : ℕ} (hm : 2 ≤ m) :
    (Set.ofPred (fun ℓ : ℕ => ℓ.Prime ∧ ℓ % m = 1)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hp, hBp, hpm⟩ := exists_prime_gt_modEq_one' B (k := m) (by omega)
  have : p ≤ B := hB (show p.Prime ∧ p % m = 1 from ⟨hp, by
    rw [hpm, Nat.mod_eq_of_lt (by omega)]⟩)
  omega

lemma primeCong_spec {m : ℕ} (hm : 2 ≤ m) (j : ℕ) :
    (primeCong m j).Prime ∧ primeCong m j % m = 1 :=
  Nat.nth_mem_of_infinite (infinite_primeCongSet hm) j

lemma primeCong_strictMono {m : ℕ} (hm : 2 ≤ m) : StrictMono (primeCong m) :=
  Nat.nth_strictMono (infinite_primeCongSet hm)

/-- Two numbers `a < b` that are both `≡ 1 (mod m)` satisfy `a + m ≤ b`. -/
lemma add_le_of_lt_of_mod_eq_one {m a b : ℕ} (hab : a < b) (ha : a % m = 1) (hb : b % m = 1) :
    a + m ≤ b := by
  have h1 : m ∣ b - a := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (hb.trans ha.symm))
  have h2 : m ≤ b - a := Nat.le_of_dvd (by omega) h1
  omega

lemma succ_le_primeCong {m : ℕ} (hm : 2 ≤ m) (j : ℕ) : m + 1 ≤ primeCong m j := by
  have h := primeCong_spec hm j
  have := add_le_of_lt_of_mod_eq_one h.1.one_lt (Nat.mod_eq_of_lt (by omega)) h.2
  omega

lemma prod_primeCong_pos {m : ℕ} (hm : 2 ≤ m) (t : ℕ) : 0 < ∏ j ∈ range t, primeCong m j :=
  prod_pos fun j _ => (primeCong_spec hm j).1.pos

lemma pow_le_prod_primeCong {m : ℕ} (hm : 2 ≤ m) (t : ℕ) :
    (m + 1) ^ t ≤ ∏ j ∈ range t, primeCong m j := by
  calc (m + 1) ^ t = ∏ _j ∈ range t, (m + 1) := by rw [prod_const, card_range]
    _ ≤ _ := prod_le_prod fun j _ => succ_le_primeCong hm j

lemma prod_primeCong_le_of_le {m : ℕ} (hm : 2 ≤ m) {a b : ℕ} (hab : a ≤ b) :
    ∏ j ∈ range a, primeCong m j ≤ ∏ j ∈ range b, primeCong m j :=
  Nat.le_of_dvd (prod_primeCong_pos hm b) (prod_dvd_prod_of_subset _ _ _ (range_subset_range.2 hab))

/-- If `S` is a finite set of elements satisfying `p`, then the product of the `|S|` smallest
elements satisfying `p` is at most the product of the elements of `S`. -/
lemma prod_nth_le_prod (p : ℕ → Prop) [DecidablePred p] :
    ∀ (n : ℕ) (S : Finset ℕ), S.card = n → (∀ x ∈ S, p x) →
      ∏ j ∈ range n, Nat.nth p j ≤ ∏ x ∈ S, x := by
  intro n
  induction n with
  | zero => intro S hS _; simp [card_eq_zero.1 hS]
  | succ n ih =>
    intro S hS hp
    have hne : S.Nonempty := by rw [← card_pos, hS]; omega
    have ha : S.max' hne ∈ S := S.max'_mem hne
    have hcard : (S.erase (S.max' hne)).card = n := by rw [card_erase_of_mem ha, hS]; rfl
    have h1 := ih (S.erase (S.max' hne)) hcard (fun x hx => hp x (mem_of_mem_erase hx))
    have h2 : Nat.nth p n ≤ S.max' hne := by
      have : n < Nat.count p (S.max' hne + 1) := by
        rw [Nat.count_eq_card_filter_range]
        calc n < S.card := by omega
          _ ≤ _ := card_le_card fun x hx =>
            mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (S.le_max' x hx)), hp x hx⟩
      exact Nat.lt_succ_iff.1 (Nat.nth_lt_of_lt_count this)
    rw [prod_range_succ, ← mul_prod_erase S (fun x => x) ha, mul_comm]
    exact Nat.mul_le_mul h2 h1

/-! ### Properties of `t_k` -/

lemma two_le_lcm {k : ℕ} (hk : 1 ≤ k) : 2 ≤ Nat.lcm 2 k :=
  Nat.le_of_dvd (Nat.lcm_pos (by norm_num) hk) (Nat.dvd_lcm_left 2 k)

lemma cycloVal_pos {q : ℕ} (hq : 2 ≤ q) (k : ℕ) : 0 < cycloVal k q :=
  Polynomial.cyclotomic_pos' k (by exact_mod_cast hq)

lemma tk_bddAbove {q k : ℕ} (hk : 1 ≤ k) :
    BddAbove {t | ((∏ j ∈ range t, primeCong (Nat.lcm 2 k) j : ℕ) : ℤ) ≤ cycloVal k q} := by
  refine ⟨(cycloVal k q).toNat, fun t ht => ?_⟩
  have hm := two_le_lcm hk
  have h1 : t < 2 ^ t := Nat.lt_two_pow_self
  have h2 : 2 ^ t ≤ (Nat.lcm 2 k + 1) ^ t := Nat.pow_le_pow_left (by omega) t
  have h3 := pow_le_prod_primeCong hm t
  have h4 : ((t : ℕ) : ℤ) ≤ cycloVal k q := le_trans (by exact_mod_cast (by omega : t ≤ _)) ht
  omega

lemma le_tk {q k t : ℕ} (hk : 1 ≤ k)
    (ht : ((∏ j ∈ range t, primeCong (Nat.lcm 2 k) j : ℕ) : ℤ) ≤ cycloVal k q) : t ≤ tk q k :=
  le_csSup (tk_bddAbove hk) ht

lemma tk_mem {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    ((∏ j ∈ range (tk q k), primeCong (Nat.lcm 2 k) j : ℕ) : ℤ) ≤ cycloVal k q :=
  Nat.sSup_mem ⟨0, by
    show ((∏ j ∈ range 0, primeCong (Nat.lcm 2 k) j : ℕ) : ℤ) ≤ cycloVal k q
    have := cycloVal_pos hq k
    simp only [range_zero, prod_empty, Nat.cast_one]
    omega⟩ (tk_bddAbove hk)

/-! ### Lemma 5.1 -/

lemma zmod_two_eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

/-- A prime `ℓ` with `ord_ℓ(q) = k ≥ 2` divides `Φ_k(q)` and is `≡ 1 (mod lcm(2,k))`. -/
lemma prime_dvd_cycloVal {q k ℓ : ℕ} (hℓ : ℓ.Prime) (hk : 2 ≤ k)
    (hord : orderOf (q : ZMod ℓ) = k) :
    (ℓ : ℤ) ∣ cycloVal k q ∧ ℓ % Nat.lcm 2 k = 1 := by
  have := Fact.mk hℓ
  have hq0 : (q : ZMod ℓ) ≠ 0 := by
    intro h
    rw [h, orderOf_eq_zero_iff'.2 (fun n hn => by simp [zero_pow hn.ne'])] at hord
    omega
  have hdvd : k ∣ ℓ - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have : (q : ZMod 2) = 1 := zmod_two_eq_one_of_ne_zero _ hq0
    rw [this, orderOf_one] at hord
    omega
  have hodd : 2 ∣ ℓ - 1 := by
    rcases hℓ.eq_two_or_odd with h | h
    · exact absurd h hℓ2
    · omega
  have hm : Nat.lcm 2 k ∣ ℓ - 1 := Nat.lcm_dvd hodd hdvd
  have hm2 : 2 ≤ Nat.lcm 2 k := two_le_lcm (by omega)
  refine ⟨?_, ?_⟩
  · have hkℓ : ¬ ℓ ∣ k := fun h => by
      have := Nat.le_of_dvd (by omega) h
      have := Nat.le_of_dvd (by have := hℓ.one_lt; omega) hdvd
      omega
    have : NeZero (k : ZMod ℓ) := ⟨by rwa [Ne, ZMod.natCast_eq_zero_iff]⟩
    have hroot : (Polynomial.cyclotomic k (ZMod ℓ)).IsRoot (q : ZMod ℓ) :=
      Polynomial.isRoot_cyclotomic_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hord)
    have := Polynomial.cyclotomic.eval_apply (q : ℤ) k (Int.castRingHom (ZMod ℓ))
    simp only [eq_intCast, Int.cast_natCast] at this
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, cycloVal, ← this]
    exact hroot
  · have h1 : 1 ≡ ℓ [MOD Nat.lcm 2 k] := (Nat.modEq_iff_dvd' hℓ.pos).2 hm
    rw [← Nat.mod_eq_of_lt (show 1 < Nat.lcm 2 k by omega)]
    exact h1.symm

/-- The number of primes `ℓ` with `ord_ℓ(q) = k ≥ 2` in a finite set is at most `t_k`. -/
lemma card_le_tk {q k : ℕ} (hq : 2 ≤ q) (hk : 2 ≤ k) (S : Finset ℕ)
    (hS : ∀ ℓ ∈ S, ℓ.Prime ∧ orderOf (q : ZMod ℓ) = k) : S.card ≤ tk q k := by
  have h1 := fun ℓ (hℓ : ℓ ∈ S) => prime_dvd_cycloVal (hS ℓ hℓ).1 hk (hS ℓ hℓ).2
  have hVpos := cycloVal_pos hq k
  obtain ⟨V, hV⟩ : ∃ V : ℕ, cycloVal k q = V :=
    ⟨(cycloVal k q).toNat, (Int.toNat_of_nonneg hVpos.le).symm⟩
  have hprod : ∏ ℓ ∈ S, ℓ ∣ V := Finset.prod_primes_dvd V
    (fun ℓ hℓ => (hS ℓ hℓ).1.prime) (fun ℓ hℓ => by
      have := (h1 ℓ hℓ).1
      rw [hV] at this
      exact_mod_cast this)
  have hVpos' : 0 < V := by rw [hV] at hVpos; exact_mod_cast hVpos
  apply le_tk (by omega)
  rw [hV]
  have h2 : ∏ j ∈ range S.card, primeCong (Nat.lcm 2 k) j ≤ ∏ ℓ ∈ S, ℓ := by
    classical
    exact prod_nth_le_prod (fun ℓ => ℓ.Prime ∧ ℓ % Nat.lcm 2 k = 1) S.card S rfl
      (fun ℓ hℓ => ⟨(hS ℓ hℓ).1, (h1 ℓ hℓ).2⟩)
  exact_mod_cast h2.trans (Nat.le_of_dvd hVpos' hprod)

/-- **Lemma 5.1**: `ω(q^n - 1) ≤ ω(q - 1) + ∑_{k ∣ n, k > 1} t_k`. -/
theorem omega_le_omegaBd {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) :
    (q ^ n - 1).primeFactors.card ≤ omegaBd q n := by
  classical
  have hqn : 2 ≤ q ^ n := le_trans hq (Nat.le_self_pow (by omega) q)
  have hpow : ∀ ℓ ∈ (q ^ n - 1).primeFactors, (q : ZMod ℓ) ^ n = 1 := by
    intro ℓ hℓ
    have hd : ℓ ∣ q ^ n - 1 := Nat.dvd_of_mem_primeFactors hℓ
    have : ((q ^ n - 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at this
    exact this
  have hmaps : ∀ ℓ ∈ (q ^ n - 1).primeFactors,
      (fun ℓ : ℕ => orderOf (q : ZMod ℓ)) ℓ ∈ n.divisors := by
    intro ℓ hℓ
    exact Nat.mem_divisors.2 ⟨orderOf_dvd_of_pow_eq_one (hpow ℓ hℓ), by omega⟩
  rw [card_eq_sum_card_fiberwise hmaps, ← sum_filter_add_sum_filter_not n.divisors (1 < ·)]
  have hsplit : n.divisors.filter (fun d => ¬ 1 < d) = {1} := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_singleton]
    constructor
    · rintro ⟨⟨hd, hn0⟩, h1⟩
      have := Nat.pos_of_dvd_of_pos hd (by omega)
      omega
    · rintro rfl
      exact ⟨⟨one_dvd n, by omega⟩, by omega⟩
  rw [hsplit, sum_singleton, omegaBd, add_comm]
  apply add_le_add
  · apply card_le_card
    intro ℓ hℓ
    rw [mem_filter] at hℓ
    obtain ⟨hℓ, h1⟩ := hℓ
    have hp := Nat.prime_of_mem_primeFactors hℓ
    rw [orderOf_eq_one_iff] at h1
    refine Nat.mem_primeFactors.2 ⟨hp, ?_, by omega⟩
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega), h1, Nat.cast_one, sub_self]
  · apply sum_le_sum
    intro k hk
    rw [mem_filter] at hk
    exact card_le_tk hq hk.2 _ fun ℓ hℓ => by
      rw [mem_filter] at hℓ
      exact ⟨Nat.prime_of_mem_primeFactors hℓ.1, hℓ.2⟩

/-! ### Lemma 5.1, second bound -/

/-- `c_q = -∑_{j ≥ 1} log₂(1 - q^{-j})`, so that `2^{c_q} = ∏_{j ≥ 1} (1 - q^{-j})^{-1}`
(the series converges for `q ≥ 2`, `summable_cq`). -/
noncomputable def cq (q : ℕ) : ℝ := -∑' j : ℕ, Real.logb 2 (1 - (q : ℝ)⁻¹ ^ (j + 1))

/-- A rational upper bound for `c_q` (`cq_le_cqUpper`, for `q ≥ 2`):
`(14427/10000) (1/(q-1) + 1/(2(q²-1)) + 1/(3(q³-1)) + 1/(4(q⁴-1)) + q/(5(q-1)(q⁵-1)))`.
For `q = 2` it is `2225193/1240000 = 1.7945…`, against `c_2 = 1.7919…`. -/
def cqUpper (q : ℕ) : ℚ :=
  14427 / 10000 * (1 / (q - 1) + 1 / (2 * (q ^ 2 - 1)) + 1 / (3 * (q ^ 3 - 1)) +
    1 / (4 * (q ^ 4 - 1)) + q / (5 * (q - 1) * (q ^ 5 - 1)))

/-- `⌈a / b⌉` for natural numbers (`b > 0`). -/
def ceilDivNat (a b : ℕ) : ℕ := (a + b - 1) / b

/-- An integer upper bound for `S c_q` (`mul_cq_le_cqCeil`): the sum of the ceilings of the five
terms of `S · cqUpper q`. -/
def cqCeil (S q : ℕ) : ℕ :=
  ceilDivNat (14427 * S) (10000 * (q - 1)) + ceilDivNat (14427 * S) (20000 * (q ^ 2 - 1)) +
    ceilDivNat (14427 * S) (30000 * (q ^ 3 - 1)) + ceilDivNat (14427 * S) (40000 * (q ^ 4 - 1)) +
    ceilDivNat (14427 * S * q) (50000 * (q - 1) * (q ^ 5 - 1))

section SecondBound

open Real

/-- `-log(1 - y) ≤ y + y²/2 + y³/3 + y⁴/4 + y⁵/(5(1 - y))` for `0 ≤ y < 1`. -/
lemma neg_log_one_sub_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    -log (1 - y) ≤ y + y ^ 2 / 2 + y ^ 3 / 3 + y ^ 4 / 4 + y ^ 5 / (5 * (1 - y)) := by
  have hs := hasSum_pow_div_log_of_abs_lt_one (by rw [abs_of_nonneg h0]; exact h1)
  rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add 4]
  have hg : HasSum (fun i : ℕ => y ^ 5 / 5 * y ^ i) (y ^ 5 / 5 * (1 - y)⁻¹) :=
    (hasSum_geometric_of_lt_one h0 h1).mul_left _
  have hle : ∑' i : ℕ, y ^ (i + 4 + 1) / (((i + 4 : ℕ) : ℝ) + 1) ≤ y ^ 5 / (5 * (1 - y)) := by
    calc _ ≤ ∑' i : ℕ, y ^ 5 / 5 * y ^ i := by
          refine ((summable_nat_add_iff 4).2 hs.summable).tsum_le_tsum (fun i => ?_) hg.summable
          rw [show y ^ (i + 4 + 1) = y ^ 5 * y ^ i by ring,
            show y ^ 5 / 5 * y ^ i = y ^ 5 * y ^ i / 5 by ring]
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
          push_cast
          linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      _ = _ := by rw [hg.tsum_eq]; field_simp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast at hle ⊢
  norm_num at hle ⊢
  linarith

lemma neg_log_one_sub_nonneg {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : 0 ≤ -log (1 - y) := by
  have := Real.log_nonpos (by linarith) (by linarith : 1 - y ≤ 1)
  linarith

/-- `∑_{j ≥ 0} (x^{j+1})^i = x^i / (1 - x^i)`. -/
lemma hasSum_pow_succ_pow {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) {i : ℕ} (hi : i ≠ 0) :
    HasSum (fun j : ℕ => (x ^ (j + 1)) ^ i) (x ^ i / (1 - x ^ i)) := by
  have h := (hasSum_geometric_of_lt_one (pow_nonneg h0 i) (pow_lt_one₀ h0 h1 hi)).mul_left (x ^ i)
  convert h using 1
  · funext j; ring
  · rw [div_eq_mul_inv]

/-- The majorant series of `∑_{j ≥ 0} -log(1 - x^{j+1})` (termwise `neg_log_one_sub_le` with
`1 - x^{j+1} ≥ 1 - x`). -/
lemma hasSum_cq_majorant {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    HasSum (fun j : ℕ => x ^ (j + 1) + (x ^ (j + 1)) ^ 2 / 2 + (x ^ (j + 1)) ^ 3 / 3 +
        (x ^ (j + 1)) ^ 4 / 4 + (x ^ (j + 1)) ^ 5 / (5 * (1 - x)))
      (x / (1 - x) + x ^ 2 / (2 * (1 - x ^ 2)) + x ^ 3 / (3 * (1 - x ^ 3)) +
        x ^ 4 / (4 * (1 - x ^ 4)) + x ^ 5 / (5 * (1 - x) * (1 - x ^ 5))) := by
  have h1' := hasSum_pow_succ_pow h0 h1 (i := 1) one_ne_zero
  simp only [pow_one] at h1'
  have h2 := (hasSum_pow_succ_pow h0 h1 (i := 2) two_ne_zero).div_const 2
  have h3 := (hasSum_pow_succ_pow h0 h1 (i := 3) three_ne_zero).div_const 3
  have h4 := (hasSum_pow_succ_pow h0 h1 (i := 4) four_ne_zero).div_const 4
  have h5 := (hasSum_pow_succ_pow h0 h1 (i := 5) (by norm_num)).div_const (5 * (1 - x))
  convert (((h1'.add h2).add h3).add h4).add h5 using 1
  have : 1 - x ≠ 0 := by linarith
  have : 1 - x ^ 5 ≠ 0 := by have := pow_lt_one₀ h0 h1 (n := 5) (by norm_num); linarith
  have : 1 - x ^ 2 ≠ 0 := by have := pow_lt_one₀ h0 h1 (n := 2) (by norm_num); linarith
  have : 1 - x ^ 3 ≠ 0 := by have := pow_lt_one₀ h0 h1 (n := 3) (by norm_num); linarith
  have : 1 - x ^ 4 ≠ 0 := by have := pow_lt_one₀ h0 h1 (n := 4) (by norm_num); linarith
  field_simp

/-- `ln 2 > 10000/14427` (so `1/ln 2 < 1.4427`), from a partial sum of
`ln 2 = ∑_{n ≥ 1} 2^{-n}/n`. -/
lemma log_two_gt : (10000 / 14427 : ℝ) < log 2 := by
  have h := hasSum_pow_div_log_of_abs_lt_one (x := (1 / 2 : ℝ)) (by norm_num [abs_of_pos])
  have h2 : -log (1 - 1 / 2) = log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]
  rw [h2] at h
  have := sum_le_hasSum (range 16) (fun i _ => by positivity) h
  norm_num [Finset.sum_range_succ] at this
  linarith

lemma inv_cast_bounds {q : ℕ} (hq : 2 ≤ q) : 0 < (q : ℝ)⁻¹ ∧ (q : ℝ)⁻¹ ≤ 1 / 2 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨by positivity, ?_⟩
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hq'

lemma summable_neg_log_cq {q : ℕ} (hq : 2 ≤ q) :
    Summable (fun j : ℕ => -log (1 - (q : ℝ)⁻¹ ^ (j + 1))) := by
  obtain ⟨hx0, hx1⟩ := inv_cast_bounds hq
  set x := (q : ℝ)⁻¹
  refine Summable.of_nonneg_of_le (fun j => neg_log_one_sub_nonneg (by positivity)
    (pow_lt_one₀ hx0.le (by linarith) (Nat.succ_ne_zero j))) (fun j => ?_)
    (hasSum_cq_majorant hx0.le (by linarith)).summable
  have hy0 : 0 ≤ x ^ (j + 1) := by positivity
  have hyx : x ^ (j + 1) ≤ x := pow_le_of_le_one hx0.le (by linarith) (Nat.succ_ne_zero j)
  refine (neg_log_one_sub_le hy0 (by linarith)).trans ?_
  gcongr
  linarith

lemma tsum_neg_log_cq_le {q : ℕ} (hq : 2 ≤ q) :
    ∑' j : ℕ, -log (1 - (q : ℝ)⁻¹ ^ (j + 1)) ≤
      (q : ℝ)⁻¹ / (1 - (q : ℝ)⁻¹) + (q : ℝ)⁻¹ ^ 2 / (2 * (1 - (q : ℝ)⁻¹ ^ 2)) +
        (q : ℝ)⁻¹ ^ 3 / (3 * (1 - (q : ℝ)⁻¹ ^ 3)) + (q : ℝ)⁻¹ ^ 4 / (4 * (1 - (q : ℝ)⁻¹ ^ 4)) +
        (q : ℝ)⁻¹ ^ 5 / (5 * (1 - (q : ℝ)⁻¹) * (1 - (q : ℝ)⁻¹ ^ 5)) := by
  obtain ⟨hx0, hx1⟩ := inv_cast_bounds hq
  set x := (q : ℝ)⁻¹
  refine hasSum_le (fun j => ?_) (summable_neg_log_cq hq).hasSum
    (hasSum_cq_majorant hx0.le (by linarith))
  have hy0 : 0 ≤ x ^ (j + 1) := by positivity
  have hyx : x ^ (j + 1) ≤ x := pow_le_of_le_one hx0.le (by linarith) (Nat.succ_ne_zero j)
  refine (neg_log_one_sub_le hy0 (by linarith)).trans ?_
  gcongr
  linarith

/-- `c_q ln 2 = ∑_{j ≥ 1} -ln(1 - q^{-j})`. -/
lemma cq_mul_log_two (q : ℕ) :
    cq q * log 2 = ∑' j : ℕ, -log (1 - (q : ℝ)⁻¹ ^ (j + 1)) := by
  have : log 2 ≠ 0 := by positivity
  simp only [cq, Real.logb, tsum_div_const, tsum_neg]
  field_simp

/-- The series defining `c_q` converges. -/
theorem summable_cq {q : ℕ} (hq : 2 ≤ q) :
    Summable (fun j : ℕ => Real.logb 2 (1 - (q : ℝ)⁻¹ ^ (j + 1))) := by
  refine ((summable_neg_log_cq hq).neg.div_const (log 2)).congr fun j => ?_
  simp [Real.logb]

theorem cq_nonneg {q : ℕ} (hq : 2 ≤ q) : 0 ≤ cq q := by
  have h := cq_mul_log_two q
  have h2 : 0 ≤ ∑' j : ℕ, -log (1 - (q : ℝ)⁻¹ ^ (j + 1)) := by
    obtain ⟨hx0, hx1⟩ := inv_cast_bounds hq
    exact tsum_nonneg fun j => neg_log_one_sub_nonneg (by positivity)
      (pow_lt_one₀ hx0.le (by linarith) (Nat.succ_ne_zero j))
  have hl : 0 < log 2 := by positivity
  nlinarith

/-- The rational upper bound `c_q ≤ cqUpper q`. -/
theorem cq_le_cqUpper {q : ℕ} (hq : 2 ≤ q) : cq q ≤ cqUpper q := by
  have h1 := tsum_neg_log_cq_le hq
  rw [← cq_mul_log_two] at h1
  have hl := log_two_gt
  have hcq := cq_nonneg hq
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have e : (q : ℝ)⁻¹ / (1 - (q : ℝ)⁻¹) + (q : ℝ)⁻¹ ^ 2 / (2 * (1 - (q : ℝ)⁻¹ ^ 2)) +
        (q : ℝ)⁻¹ ^ 3 / (3 * (1 - (q : ℝ)⁻¹ ^ 3)) + (q : ℝ)⁻¹ ^ 4 / (4 * (1 - (q : ℝ)⁻¹ ^ 4)) +
        (q : ℝ)⁻¹ ^ 5 / (5 * (1 - (q : ℝ)⁻¹) * (1 - (q : ℝ)⁻¹ ^ 5)) =
      1 / ((q : ℝ) - 1) + 1 / (2 * ((q : ℝ) ^ 2 - 1)) + 1 / (3 * ((q : ℝ) ^ 3 - 1)) +
        1 / (4 * ((q : ℝ) ^ 4 - 1)) + q / (5 * ((q : ℝ) - 1) * ((q : ℝ) ^ 5 - 1)) := by
    have hp : ∀ i : ℕ, i ≠ 0 → (q : ℝ) ^ i - 1 ≠ 0 := fun i hi =>
      (sub_pos.2 (one_lt_pow₀ (by linarith) hi)).ne'
    have h0 : (q : ℝ) ≠ 0 := by positivity
    have : (q : ℝ) - 1 ≠ 0 := by linarith
    have := hp 2 (by norm_num)
    have := hp 3 (by norm_num)
    have := hp 4 (by norm_num)
    have := hp 5 (by norm_num)
    field_simp
  rw [e] at h1
  simp only [cqUpper]
  push_cast
  set G := 1 / ((q : ℝ) - 1) + 1 / (2 * ((q : ℝ) ^ 2 - 1)) + 1 / (3 * ((q : ℝ) ^ 3 - 1)) +
        1 / (4 * ((q : ℝ) ^ 4 - 1)) + q / (5 * ((q : ℝ) - 1) * ((q : ℝ) ^ 5 - 1))
  have : cq q * (10000 / 14427) ≤ G := le_trans (by nlinarith) h1
  linarith

lemma div_le_ceilDivNat (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ceilDivNat a b := by
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : a ≤ b * ceilDivNat a b := by unfold ceilDivNat; omega
  rw [div_le_iff₀ (by exact_mod_cast hb), mul_comm]
  exact_mod_cast h3

/-- The integer upper bound `S c_q ≤ cqCeil S q`. -/
theorem mul_cq_le_cqCeil {q : ℕ} (hq : 2 ≤ q) (S : ℕ) : S * cq q ≤ cqCeil S q := by
  have h := cq_le_cqUpper hq
  have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have p2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have p3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have p4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have p5 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ (by omega)
  have q2 : 2 ≤ q ^ 2 := le_trans hq (Nat.le_self_pow (by norm_num) q)
  have q3 : 2 ≤ q ^ 3 := le_trans hq (Nat.le_self_pow (by norm_num) q)
  have q4 : 2 ≤ q ^ 4 := le_trans hq (Nat.le_self_pow (by norm_num) q)
  have q5 : 2 ≤ q ^ 5 := le_trans hq (Nat.le_self_pow (by norm_num) q)
  have d1 := div_le_ceilDivNat (14427 * S) (10000 * (q - 1))
    (Nat.mul_pos (by norm_num) (by omega))
  have d2 := div_le_ceilDivNat (14427 * S) (20000 * (q ^ 2 - 1))
    (Nat.mul_pos (by norm_num) (by omega))
  have d3 := div_le_ceilDivNat (14427 * S) (30000 * (q ^ 3 - 1))
    (Nat.mul_pos (by norm_num) (by omega))
  have d4 := div_le_ceilDivNat (14427 * S) (40000 * (q ^ 4 - 1))
    (Nat.mul_pos (by norm_num) (by omega))
  have d5 := div_le_ceilDivNat (14427 * S * q) (50000 * (q - 1) * (q ^ 5 - 1))
    (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega))
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub p2,
    Nat.cast_sub p3, Nat.cast_sub p4, Nat.cast_sub p5, Nat.cast_pow, Nat.cast_one] at d1 d2 d3 d4 d5
  have e : (S : ℝ) * (cqUpper q : ℝ) = 14427 * S / (10000 * ((q : ℝ) - 1)) +
      14427 * S / (20000 * ((q : ℝ) ^ 2 - 1)) + 14427 * S / (30000 * ((q : ℝ) ^ 3 - 1)) +
      14427 * S / (40000 * ((q : ℝ) ^ 4 - 1)) +
      14427 * S * q / (50000 * ((q : ℝ) - 1) * ((q : ℝ) ^ 5 - 1)) := by
    simp only [cqUpper]
    push_cast
    have hp : ∀ i : ℕ, i ≠ 0 → (q : ℝ) ^ i - 1 ≠ 0 := fun i hi =>
      (sub_pos.2 (one_lt_pow₀ (by linarith) hi)).ne'
    have : (q : ℝ) - 1 ≠ 0 := by linarith
    have := hp 2 (by norm_num)
    have := hp 3 (by norm_num)
    have := hp 4 (by norm_num)
    have := hp 5 (by norm_num)
    field_simp
    ring
  calc (S : ℝ) * cq q ≤ S * (cqUpper q : ℝ) := mul_le_mul_of_nonneg_left h hS
    _ ≤ _ := by
      rw [e, cqCeil]
      push_cast
      linarith

open ArithmeticFunction in
/-- `log Φ_n(q) = φ(n) log q + ∑_{ab = n} μ(a) log(1 - q^{-b})`, i.e.
`Φ_n(q) = q^{φ(n)} ∏_{b ∣ n} (1 - q^{-b})^{μ(n/b)}` (Möbius inversion of
`∑_{d ∣ n} (log Φ_d(q) - φ(d) log q) = log(q^n - 1) - n log q`, from
`∏_{d ∣ n} Φ_d(q) = q^n - 1` and `∑_{d ∣ n} φ(d) = n`). -/
lemma log_cycloVal_eq {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : 0 < n) :
    log (cycloVal n q) = n.totient * log q +
      ∑ x ∈ n.divisorsAntidiagonal, (moebius x.1 : ℝ) * log (1 - (q : ℝ)⁻¹ ^ x.2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have key := (sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun d => log (cycloVal d q) - d.totient * log q)
    (g := fun n => log (1 - (q : ℝ)⁻¹ ^ n))).1 (fun n hn => ?_) n hn
  · linarith
  · have hprod : ∏ d ∈ n.divisors, (cycloVal d q : ℝ) = (q : ℝ) ^ n - 1 := by
      have := congrArg (Polynomial.eval (q : ℤ))
        (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
      rw [Polynomial.eval_prod] at this
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one] at this
      unfold cycloVal
      exact_mod_cast this
    have hpos : ∀ d ∈ n.divisors, (cycloVal d q : ℝ) ≠ 0 := fun d _ =>
      (Int.cast_pos.2 (cycloVal_pos hq d)).ne'
    have hqn : (1 : ℝ) < (q : ℝ) ^ n := one_lt_pow₀ (by exact_mod_cast hq) hn.ne'
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_totient,
      ← Real.log_prod hpos, hprod, ← Real.log_pow, ← Real.log_div (by linarith) (by positivity)]
    congr 1
    have : (q : ℝ) ^ n ≠ 0 := by positivity
    rw [inv_pow]
    field_simp

open ArithmeticFunction in
/-- `log Φ_n(q) ≤ φ(n) log q + c_q log 2`: in `log_cycloVal_eq` drop the terms with
`μ(a) = 1` (they are `≤ 0`), bound those with `μ(a) = -1` by `-log(1 - q^{-b}) ≥ 0`, and the
sum over `b ∣ n` by the sum over all `b ≥ 1`. -/
lemma log_cycloVal_le {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : 0 < n) :
    log (cycloVal n q) ≤ n.totient * log q + cq q * log 2 := by
  obtain ⟨hx0, hx1⟩ := inv_cast_bounds hq
  rw [log_cycloVal_eq hq hn, cq_mul_log_two]
  gcongr
  set x := (q : ℝ)⁻¹
  have hL : ∀ b : ℕ, b ≠ 0 → 0 ≤ -log (1 - x ^ b) := fun b hb =>
    neg_log_one_sub_nonneg (by positivity) (pow_lt_one₀ hx0.le (by linarith) hb)
  calc ∑ p ∈ n.divisorsAntidiagonal, (moebius p.1 : ℝ) * log (1 - x ^ p.2)
      ≤ ∑ p ∈ n.divisorsAntidiagonal, -log (1 - x ^ p.2) := by
        refine sum_le_sum fun p hp => ?_
        have hb : p.2 ≠ 0 := by
          rw [Nat.mem_divisorsAntidiagonal] at hp
          intro h
          rw [h, mul_zero] at hp
          omega
        have hμ : -1 ≤ (moebius p.1 : ℝ) := by
          have := (abs_le.1 (abs_moebius_le_one (n := p.1))).1
          exact_mod_cast this
        nlinarith [hL p.2 hb]
    _ = ∑ b ∈ n.divisors, -log (1 - x ^ b) :=
        Nat.sum_divisorsAntidiagonal' (fun _ b => -log (1 - x ^ b))
    _ ≤ ∑ b ∈ Finset.Ico 1 (n + 1), -log (1 - x ^ b) := by
        refine sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) (fun b hb _ => ?_)
        · rw [Nat.mem_divisors] at hb
          rw [Finset.mem_Ico]
          exact ⟨Nat.pos_of_dvd_of_pos hb.1 hn, Nat.lt_succ_of_le (Nat.le_of_dvd hn hb.1)⟩
        · rw [Finset.mem_Ico] at hb
          exact hL b (by omega)
    _ = ∑ j ∈ range n, -log (1 - x ^ (j + 1)) := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel, add_comm 1]
    _ ≤ ∑' j : ℕ, -log (1 - x ^ (j + 1)) :=
        (summable_neg_log_cq hq).sum_le_tsum _ fun j _ => hL _ (Nat.succ_ne_zero j)

/-- **Lemma 5.1**, second bound, key step:
`Φ_k(q) = q^{φ(k)} ∏_{j ∣ k} (1 - q^{-j})^{μ(k/j)} ≤ q^{φ(k)} ∏_{j ≥ 1} (1 - q^{-j})^{-1}
= q^{φ(k)} 2^{c_q}`. -/
theorem cycloVal_le_pow_mul_two_rpow_cq {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    (cycloVal k q : ℝ) ≤ (q : ℝ) ^ k.totient * 2 ^ cq q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpos : (0 : ℝ) < cycloVal k q := Int.cast_pos.2 (cycloVal_pos hq k)
  rw [← Real.log_le_log_iff hpos (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_rpow (by norm_num)]
  exact log_cycloVal_le hq hk

/-- **Lemma 5.1**, second bound, product form: `(lcm(2,k) + 1)^{t_k} ≤ q^{φ(k)} 2^{c_q}`
(the `t_k` primes `≡ 1 (mod lcm(2,k))` are each `≥ lcm(2,k) + 1`). -/
theorem lcm_add_one_pow_tk_le {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    (Nat.lcm 2 k + 1 : ℝ) ^ tk q k ≤ (q : ℝ) ^ k.totient * 2 ^ cq q := by
  have h1 := pow_le_prod_primeCong (two_le_lcm hk) (tk q k)
  have h2 := tk_mem hq hk
  have h3 : ((Nat.lcm 2 k + 1) ^ tk q k : ℕ) ≤ (cycloVal k q : ℝ) := by
    have : (((Nat.lcm 2 k + 1) ^ tk q k : ℕ) : ℤ) ≤ cycloVal k q :=
      le_trans (by exact_mod_cast h1) h2
    exact_mod_cast this
  push_cast at h3
  exact h3.trans (cycloVal_le_pow_mul_two_rpow_cq hq hk)

/-- **Lemma 5.1**, second bound: `t_k ≤ (φ(k) log₂ q + c_q) / log₂(lcm(2,k) + 1)`, i.e.
`t_k log₂(lcm(2,k) + 1) ≤ φ(k) log₂ q + c_q` with `c_q = -∑_{j ≥ 1} log₂(1 - q^{-j})`. -/
theorem tk_mul_logb_le {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    (tk q k : ℝ) * Real.logb 2 (Nat.lcm 2 k + 1) ≤ k.totient * Real.logb 2 q + cq q := by
  have h := lcm_add_one_pow_tk_le hq hk
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
  rwa [Real.logb_pow, Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_rpow (by norm_num) (by norm_num)] at this

end SecondBound

/-! ### A computable upper bound for `t_k` -/

/-- `cycloAux k x = Φ_k(x)` (for `k ≥ 1`, `x ≥ 2`), computed recursively via
`Φ_{np}(x) = Φ_n(x^p)` if `p ∣ n` and `Φ_{np}(x) = Φ_n(x^p) / Φ_n(x)` if `p ∤ n`
(`p` the least prime factor of `k = np`). -/
def cycloAux (k x : ℕ) : ℕ :=
  if h : k ≤ 1 then x - 1
  else
    if k.minFac ∣ k / k.minFac then cycloAux (k / k.minFac) (x ^ k.minFac)
    else cycloAux (k / k.minFac) (x ^ k.minFac) / cycloAux (k / k.minFac) x
termination_by k
decreasing_by all_goals exact Nat.div_lt_self (by omega) (Nat.minFac_prime (by omega)).one_lt

lemma cycloAux_eq : ∀ (k x : ℕ), 1 ≤ k → 2 ≤ x →
    (cycloAux k x : ℤ) = (Polynomial.cyclotomic k ℤ).eval (x : ℤ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x hk hx
  rw [cycloAux]
  split_ifs with h1 h2
  · obtain rfl : k = 1 := by omega
    simp [Polynomial.cyclotomic_one, Nat.cast_sub (by omega : 1 ≤ x)]
  · have hp := Nat.minFac_prime (show k ≠ 1 by omega)
    have hkp : k / k.minFac * k.minFac = k := Nat.div_mul_cancel (Nat.minFac_dvd k)
    have hlt : k / k.minFac < k := Nat.div_lt_self (by omega) hp.one_lt
    have hk1 : 1 ≤ k / k.minFac := Nat.div_pos (Nat.minFac_le (by omega)) hp.pos
    have hxp : 2 ≤ x ^ k.minFac := le_trans hx (Nat.le_self_pow hp.ne_zero x)
    rw [ih _ hlt _ hk1 hxp, Nat.cast_pow, ← Polynomial.expand_eval,
      Polynomial.cyclotomic_expand_eq_cyclotomic hp h2, hkp]
  · have hp := Nat.minFac_prime (show k ≠ 1 by omega)
    have hkp : k / k.minFac * k.minFac = k := Nat.div_mul_cancel (Nat.minFac_dvd k)
    have hlt : k / k.minFac < k := Nat.div_lt_self (by omega) hp.one_lt
    have hk1 : 1 ≤ k / k.minFac := Nat.div_pos (Nat.minFac_le (by omega)) hp.pos
    have hxp : 2 ≤ x ^ k.minFac := le_trans hx (Nat.le_self_pow hp.ne_zero x)
    have hB := ih _ hlt _ hk1 hx
    have hBpos : 0 < (Polynomial.cyclotomic (k / k.minFac) ℤ).eval (x : ℤ) :=
      Polynomial.cyclotomic_pos' _ (by exact_mod_cast hx)
    rw [Int.natCast_div, ih _ hlt _ hk1 hxp, hB, Nat.cast_pow, ← Polynomial.expand_eval,
      Polynomial.cyclotomic_expand_eq_cyclotomic_mul hp h2, Polynomial.eval_mul, hkp,
      Int.mul_ediv_cancel _ hBpos.ne']

/-- Computable `Φ_k(q)` (for `q ≥ 2`, `k ≥ 1`). -/
def cycloNat (k q : ℕ) : ℕ := cycloAux k q

theorem cycloNat_eq {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) : (cycloNat k q : ℤ) = cycloVal k q :=
  cycloAux_eq k q hk hq

/-- `φ(n)` computed from the prime factorisation of `n` (trial division). -/
def totientFast (n : ℕ) : ℕ := (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1)

lemma totientFast_eq (n : ℕ) : totientFast n = n.totient :=
  (Nat.totient_eq_div_primeFactors_mul n).symm

/-- The product of the primes below `2^8`. -/
def smallPrimeProd₁ : ℕ := ((List.range 256).filter (fun p => 2 ≤ p && p.minFac == p)).prod

/-- The product of the primes below `2^14`. -/
def smallPrimeProd₂ : ℕ := ((List.range 16384).filter (fun p => 2 ≤ p && p.minFac == p)).prod

lemma prime_lt_of_dvd_smallPrimeProd₁ {r : ℕ} (hr : r.Prime) (h : r ∣ smallPrimeProd₁) :
    r < 256 := by
  obtain ⟨a, ha, hra⟩ := (hr.prime.dvd_prod_iff).1 h
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) hra) ha.1

lemma prime_lt_of_dvd_smallPrimeProd₂ {r : ℕ} (hr : r.Prime) (h : r ∣ smallPrimeProd₂) :
    r < 16384 := by
  obtain ⟨a, ha, hra⟩ := (hr.prime.dvd_prod_iff).1 h
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) hra) ha.1

/-- A fast compositeness test (trial division by all primes below `2^14` via two `gcd`s): `c` is
declared composite if `g = gcd(c, P)` is `≠ 1` and either a proper divisor of `c` or equal to `c`
with `c ≥ 2^8` resp. `c ≥ 2^14` (then `c` is a product of primes `< c`), where `P` is the product
of the primes below `2^8`, resp. `2^14`; in the remaining rare cases the test falls back to
`minFac c < c`. It is exact for `c < 2^28`, and it never declares a prime composite
(`not_prime_of_detComposite`). -/
def detComposite (c : ℕ) : Bool :=
  let g₁ := Nat.gcd c smallPrimeProd₁
  if g₁ = 1 then
    let g₂ := Nat.gcd c smallPrimeProd₂
    if g₂ = 1 then decide (2 ^ 28 ≤ c) && decide (c.minFac < c)
    else decide (g₂ < c) || decide (16384 ≤ c) || decide (c.minFac < c)
  else decide (g₁ < c) || decide (256 ≤ c) || decide (c.minFac < c)

lemma not_prime_of_detComposite {c : ℕ} (h : detComposite c = true) : ¬ c.Prime := by
  intro hc
  have hmf := hc.minFac_eq
  unfold detComposite at h
  simp only at h
  split_ifs at h with hg₁ hg₂
  · simp [hmf] at h
  · rcases (Nat.dvd_prime hc).1 (Nat.gcd_dvd_left c smallPrimeProd₂) with h1 | h1
    · exact hg₂ h1
    · have := prime_lt_of_dvd_smallPrimeProd₂ hc (h1 ▸ Nat.gcd_dvd_right c smallPrimeProd₂)
      simp [h1, hmf] at h
      omega
  · rcases (Nat.dvd_prime hc).1 (Nat.gcd_dvd_left c smallPrimeProd₁) with h1 | h1
    · exact hg₁ h1
    · have := prime_lt_of_dvd_smallPrimeProd₁ hc (h1 ▸ Nat.gcd_dvd_right c smallPrimeProd₁)
      simp [h1, hmf] at h
      omega

/-- The sieve: scanning the candidates `c, c + m, c + 2m, …` (all `≡ 1 (mod m)`), skipping those
detected composite, multiplying the kept candidates into `prod` while `prod ≤ V`; returns the
number `cnt` of kept candidates multiplied in. -/
def sieveCount (m V c cnt prod : ℕ) : ℕ :=
  if _h : V < c ∨ m = 0 then cnt
  else if detComposite c then sieveCount m V (c + m) cnt prod
  else if prod * c ≤ V then sieveCount m V (c + m) (cnt + 1) (prod * c)
  else cnt
termination_by V + 1 - c
decreasing_by all_goals omega

/-- Soundness of the sieve: under the invariant (`c ≡ 1 (mod m)`, `c ≤ primeCong m cnt`,
`prod ≤ ∏_{j < cnt} primeCong m j`), every `t` with `∏_{j < t} primeCong m j ≤ V` is at most the
value of the sieve. -/
lemma sieveCount_sound {m V : ℕ} (hm : 2 ≤ m) (c cnt prod : ℕ) (hc : c % m = 1)
    (hcp : c ≤ primeCong m cnt) (hprod : prod ≤ ∏ j ∈ range cnt, primeCong m j)
    (t : ℕ) (ht : ∏ j ∈ range t, primeCong m j ≤ V) : t ≤ sieveCount m V c cnt prod := by
  induction c, cnt, prod using sieveCount.induct m V with
  | case1 c cnt prod h =>
    rw [sieveCount, dite_eq_left h]
    by_contra hlt
    have h1 := prod_primeCong_le_of_le hm (show cnt + 1 ≤ t by omega)
    rw [prod_range_succ] at h1
    have h2 := prod_primeCong_pos hm cnt
    have h3 : primeCong m cnt ≤ (∏ j ∈ range cnt, primeCong m j) * primeCong m cnt :=
      Nat.le_mul_of_pos_left _ h2
    omega
  | case2 c cnt prod h hmin ih =>
    rw [sieveCount, dite_eq_right h, ite_eq_left hmin]
    have hne : c ≠ primeCong m cnt := by
      intro heq
      exact not_prime_of_detComposite hmin (heq ▸ (primeCong_spec hm cnt).1)
    have hc' : (c + m) % m = 1 := by rw [Nat.add_mod_right]; exact hc
    exact ih hc' (add_le_of_lt_of_mod_eq_one (lt_of_le_of_ne hcp hne) hc
      (primeCong_spec hm cnt).2) hprod
  | case3 c cnt prod h hmin hle ih =>
    rw [sieveCount, dite_eq_right h, ite_eq_right hmin, ite_eq_left hle]
    have hc' : (c + m) % m = 1 := by rw [Nat.add_mod_right]; exact hc
    have hlt : c < primeCong m (cnt + 1) :=
      lt_of_le_of_lt hcp (primeCong_strictMono hm (Nat.lt_succ_self cnt))
    refine ih hc' (add_le_of_lt_of_mod_eq_one hlt hc (primeCong_spec hm _).2) ?_
    rw [prod_range_succ]
    exact Nat.mul_le_mul hprod hcp
  | case4 c cnt prod h hmin hle =>
    rw [sieveCount, dite_eq_right h, ite_eq_right hmin, ite_eq_right hle]
    by_contra hlt
    have h1 := prod_primeCong_le_of_le hm (show cnt + 1 ≤ t by omega)
    rw [prod_range_succ] at h1
    have := Nat.mul_le_mul hprod hcp
    omega

/-- Computable upper bound for `t_k` (`tk_le_tUpper`): with `m = lcm(2,k)`, if
`φ(k) · ⌊log₂ q⌋ ≤ 3000` the exact sieve `sieveCount` (the largest `t` such that the product of the
first `t` candidates `≡ 1 (mod m)` not detected composite is `≤ Φ_k(q)`), otherwise
`⌊(φ(k) ⌈1024 log₂ q⌉ + cqCeil 1024 q) / ⌊1024 log₂ (m+1)⌋⌋`, the second bound of Lemma 5.1
(`tk_mul_logb_le`, `mul_cq_le_cqCeil`) with `⌈1024 log₂ q⌉ = ⌊log₂ (q^1024 - 1)⌋ + 1` and
`⌊1024 log₂ (m+1)⌋ = ⌊log₂ (m+1)^1024⌋`. -/
def tUpper (q k : ℕ) : ℕ :=
  let m := Nat.lcm 2 k
  let φ := totientFast k
  if φ * Nat.log2 q ≤ 3000 then sieveCount m (cycloNat k q) (m + 1) 0 1
  else (φ * (Nat.log2 (q ^ 1024 - 1) + 1) + cqCeil 1024 q) / Nat.log2 ((m + 1) ^ 1024)

/-- `Φ_k(q) ≤ (q + 1)^{φ(k)}`. -/
lemma cycloVal_le {q : ℕ} (hq : 2 ≤ q) (k : ℕ) : cycloVal k q ≤ ((q + 1) ^ k.totient : ℕ) := by
  have h := Polynomial.cyclotomic_eval_le_add_one_pow_totient (q := (q : ℝ))
    (by exact_mod_cast hq) k
  have := Polynomial.cyclotomic.eval_apply (q : ℤ) k (Int.castRingHom ℝ)
  simp only [eq_intCast, Int.cast_natCast] at this
  rw [this] at h
  unfold cycloVal
  exact_mod_cast h

theorem tk_le_tUpper {q k : ℕ} (hq : 2 ≤ q) (hk : 2 ≤ k) : tk q k ≤ tUpper q k := by
  have hm := two_le_lcm (show 1 ≤ k by omega)
  have hmem := tk_mem hq (show 1 ≤ k by omega)
  have hlog := tk_mul_logb_le hq (show 1 ≤ k by omega)
  set t := tk q k
  set m := Nat.lcm 2 k
  dsimp only [tUpper]
  split_ifs with hsw
  · refine sieveCount_sound hm (m + 1) 0 1 ?_ (succ_le_primeCong hm 0) (by simp) t ?_
    · rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · rw [← cycloNat_eq hq (by omega)] at hmem
      exact_mod_cast hmem
  · rw [totientFast_eq]
    set φ := k.totient
    set A := Nat.log2 (q ^ 1024 - 1) + 1
    set C := cqCeil 1024 q
    set M := Nat.log2 ((m + 1) ^ 1024)
    have hne1 : (m + 1) ^ 1024 ≠ 0 := by positivity
    have hM : 0 < M := by
      have h2le : 2 ≤ (m + 1) ^ 1024 := by
        have := Nat.le_self_pow (n := 1024) (by norm_num) (m + 1)
        omega
      have : 1 ≤ M := (Nat.le_log2 hne1).2 (by rw [pow_one]; exact h2le)
      omega
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    -- `M ≤ 1024 log₂ (m + 1)`
    have h1 : (M : ℝ) ≤ 1024 * Real.logb 2 (m + 1) := by
      have h : ((2 ^ M : ℕ) : ℝ) ≤ ((m + 1) ^ 1024 : ℕ) := by
        exact_mod_cast Nat.log2_self_le hne1
      push_cast at h
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
      rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
    -- `1024 log₂ q ≤ A`
    have h2 : 1024 * Real.logb 2 q ≤ A := by
      have hA : q ^ 1024 ≤ 2 ^ A := Nat.le_of_pred_lt (Nat.lt_log2_self (n := q ^ 1024 - 1))
      have h : ((q ^ 1024 : ℕ) : ℝ) ≤ ((2 ^ A : ℕ) : ℝ) := by exact_mod_cast hA
      push_cast at h
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
      rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
    -- `1024 c_q ≤ C`
    have h3 : 1024 * cq q ≤ C := by exact_mod_cast mul_cq_le_cqCeil hq 1024
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have hφ : (0 : ℝ) ≤ φ := Nat.cast_nonneg _
    have h4 : ((M * t : ℕ) : ℝ) ≤ ((φ * A + C : ℕ) : ℝ) := by
      push_cast
      calc (M : ℝ) * t ≤ 1024 * Real.logb 2 (m + 1) * t := mul_le_mul_of_nonneg_right h1 ht
        _ = 1024 * (t * Real.logb 2 (m + 1)) := by ring
        _ ≤ 1024 * (φ * Real.logb 2 q + cq q) := by gcongr
        _ = φ * (1024 * Real.logb 2 q) + 1024 * cq q := by ring
        _ ≤ φ * A + C := by gcongr
    rw [Nat.le_div_iff_mul_le hM, mul_comm]
    exact_mod_cast h4

end MorganMullen
