import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.ZMod.Units

/-!
# Elementary number-theoretic notation

* `pfree p j = j'`, the `p`-free part of `j`;
* `ordMod q e = ord_e(q)`;
* `charOf q = p = minFac q`, the characteristic of the prime power `q`.
-/

namespace MorganMullen

/-- `pfree p j = j'`, the `p`-free part of `j` (`j = p^{v_p(j)} j'`). -/
def pfree (p j : ℕ) : ℕ := j / p ^ j.factorization p

/-- `ordMod q e = ord_e(q)`, the multiplicative order of `q` modulo `e`
(it is `1` for `e = 1`, and `0` if `q` is not a unit modulo `e`). -/
noncomputable def ordMod (q e : ℕ) : ℕ := orderOf (q : ZMod e)

/-- The characteristic `p` of the prime power `q` (`p = minFac q`). -/
def charOf (q : ℕ) : ℕ := q.minFac

open Nat

lemma pfree_def (p j : ℕ) : pfree p j = ordCompl[p] j := rfl

lemma pfree_dvd (p j : ℕ) : pfree p j ∣ j := Nat.ordCompl_dvd j p

lemma pfree_pos (p : ℕ) {j : ℕ} (hj : j ≠ 0) : 0 < pfree p j := Nat.ordCompl_pos p hj

lemma pfree_ne_zero (p : ℕ) {j : ℕ} (hj : j ≠ 0) : pfree p j ≠ 0 := (pfree_pos p hj).ne'

lemma pow_mul_pfree (p j : ℕ) : p ^ j.factorization p * pfree p j = j :=
  Nat.ordProj_mul_ordCompl_eq_self j p

lemma pfree_mul (p a b : ℕ) : pfree p (a * b) = pfree p a * pfree p b := Nat.ordCompl_mul a b p

lemma pfree_dvd_pfree {a b : ℕ} (h : a ∣ b) (p : ℕ) : pfree p a ∣ pfree p b :=
  Nat.ordCompl_dvd_ordCompl_of_dvd h p

lemma coprime_pfree {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) : Nat.Coprime p (pfree p j) :=
  Nat.coprime_ordCompl hp hj

lemma pfree_eq_self {p j : ℕ} (_hp : p.Prime) (h : ¬ p ∣ j) : pfree p j = j := by
  rw [pfree_def, Nat.factorization_eq_zero_of_not_dvd h, pow_zero, Nat.div_one]

lemma pfree_pfree {p j : ℕ} (hp : p.Prime) : pfree p (pfree p j) = pfree p j := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp [pfree]
  exact pfree_eq_self hp fun h => by
    have := coprime_pfree hp hj
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this h)

lemma pfree_pow_mul {p : ℕ} (hp : p.Prime) (k m : ℕ) : pfree p (p ^ k * m) = pfree p m := by
  rw [pfree_mul, pfree_def p (p ^ k), Nat.ordCompl_self_pow hp, one_mul]

lemma pfree_one (p : ℕ) : pfree p 1 = 1 := by simp [pfree]

lemma pfree_zero (p : ℕ) : pfree p 0 = 0 := by simp [pfree]

lemma factorization_pfree {p j : ℕ} (hp : p.Prime) : (pfree p j).factorization p = 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp [pfree]
  exact Nat.factorization_eq_zero_of_not_dvd fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (coprime_pfree hp hj) h)

/-! ### `ordMod` -/

lemma pow_ordMod (q e : ℕ) : ((q : ZMod e) ^ ordMod q e) = 1 := pow_orderOf_eq_one _

lemma ordMod_dvd_iff {q e k : ℕ} : ordMod q e ∣ k ↔ (q : ZMod e) ^ k = 1 := orderOf_dvd_iff_pow_eq_one

lemma ordMod_dvd_iff_modEq {q e k : ℕ} : ordMod q e ∣ k ↔ q ^ k ≡ 1 [MOD e] := by
  rw [ordMod_dvd_iff, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]

lemma ordMod_one (q : ℕ) : ordMod q 1 = 1 := by
  simp [ordMod, Subsingleton.elim (q : ZMod 1) 1]

lemma isUnit_of_coprime {q e : ℕ} (h : Nat.Coprime q e) : IsUnit (q : ZMod e) :=
  (ZMod.unitOfCoprime q h).isUnit

lemma ordMod_eq_orderOf_unit {q e : ℕ} (h : Nat.Coprime q e) :
    ordMod q e = orderOf (ZMod.unitOfCoprime q h) := by
  rw [ordMod, ← orderOf_units]; rfl

lemma ordMod_pos {q e : ℕ} (h : Nat.Coprime q e) (he : e ≠ 0) : 0 < ordMod q e := by
  have : NeZero e := ⟨he⟩
  rw [ordMod_eq_orderOf_unit h]
  exact orderOf_pos _

lemma ordMod_dvd_ordMod {q e e' : ℕ} (h : e ∣ e') : ordMod q e ∣ ordMod q e' := by
  rw [ordMod_dvd_iff]
  have := congrArg (ZMod.castHom h (ZMod e)) (pow_ordMod q e')
  rwa [map_pow, map_natCast, map_one] at this

lemma ordMod_pow (q e : ℕ) {d : ℕ} (hd : d ≠ 0) :
    ordMod (q ^ d) e = ordMod q e / Nat.gcd (ordMod q e) d := by
  simp only [ordMod, Nat.cast_pow]
  exact orderOf_pow' _ hd

end MorganMullen
