import MorganMullen.Sec6NumberOfConditions
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-!
# Section 7 (Lemma 7.5): the Pratt closure of a set of primes

For a prime `r`, `pratt r = {r} ∪ ⋃_{ℓ ∣ r - 1 prime} pratt ℓ` (the primes of the Pratt tree of `r`).
We show `2^{|pratt r|} ≤ r²`, that all elements are primes `≤ r`, and that the set is closed under
`ℓ ↦ primes of ℓ - 1`. For `D ≠ 0`, `prattSet D` is the union over the primes of `D`, and
`prattBound D = lcm(D, lcm_{r ∈ prattSet D} (r - 1))`; every prime `r` of `prattBound D` satisfies
`r - 1 ∣ prattBound D`, and `prattBound D ≤ D^{|prattSet D| + 1}`.
-/

namespace MorganMullen

open Finset

/-- The Pratt closure of `r`: `r` together with the Pratt closures of the primes of `r - 1`. -/
def pratt (r : ℕ) : Finset ℕ :=
  insert r ((r - 1).primeFactors.attach.biUnion fun ℓ => pratt ℓ.1)
termination_by r
decreasing_by
  have h := ℓ.2
  have hd := Nat.dvd_of_mem_primeFactors h
  have h0 : r - 1 ≠ 0 := (Nat.mem_primeFactors.mp h).2.2
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
  omega

lemma pratt_eq (r : ℕ) :
    pratt r = insert r ((r - 1).primeFactors.attach.biUnion fun ℓ => pratt ℓ.1) := by
  rw [pratt]

lemma mem_pratt_iff {r x : ℕ} :
    x ∈ pratt r ↔ x = r ∨ ∃ ℓ ∈ (r - 1).primeFactors, x ∈ pratt ℓ := by
  rw [pratt_eq, Finset.mem_insert, Finset.mem_biUnion]
  constructor
  · rintro (h | ⟨ℓ, -, hℓ⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ℓ.1, ℓ.2, hℓ⟩
  · rintro (h | ⟨ℓ, hℓ, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨ℓ, hℓ⟩, Finset.mem_attach _ _, hx⟩

lemma self_mem_pratt (r : ℕ) : r ∈ pratt r := mem_pratt_iff.mpr (Or.inl rfl)

lemma pratt_subset {r ℓ : ℕ} (h : ℓ ∈ (r - 1).primeFactors) : pratt ℓ ⊆ pratt r :=
  fun _ hx => mem_pratt_iff.mpr (Or.inr ⟨ℓ, h, hx⟩)

lemma lt_of_mem_primeFactors_sub_one {r ℓ : ℕ} (h : ℓ ∈ (r - 1).primeFactors) : ℓ < r := by
  have hd := Nat.dvd_of_mem_primeFactors h
  have h0 : r - 1 ≠ 0 := (Nat.mem_primeFactors.mp h).2.2
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
  omega

/-- Elements of `pratt r` are `≤ r`, and they are primes unless equal to `r`. -/
lemma le_and_prime_of_mem_pratt (r : ℕ) : ∀ x ∈ pratt r, x ≤ r ∧ (x = r ∨ x.Prime) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro x hx
    rcases mem_pratt_iff.mp hx with h | ⟨ℓ, hℓ, hxℓ⟩
    · exact ⟨h.le, Or.inl h⟩
    · have hlt := lt_of_mem_primeFactors_sub_one hℓ
      obtain ⟨h1, h2⟩ := ih ℓ hlt x hxℓ
      refine ⟨h1.trans hlt.le, Or.inr ?_⟩
      rcases h2 with h2 | h2
      · exact h2 ▸ Nat.prime_of_mem_primeFactors hℓ
      · exact h2

lemma le_of_mem_pratt {r x : ℕ} (hx : x ∈ pratt r) : x ≤ r := (le_and_prime_of_mem_pratt r x hx).1

lemma prime_of_mem_pratt {r x : ℕ} (hr : r.Prime) (hx : x ∈ pratt r) : x.Prime := by
  rcases (le_and_prime_of_mem_pratt r x hx).2 with h | h
  · exact h ▸ hr
  · exact h

/-- `pratt r` is closed under `x ↦ primes of x - 1`. -/
lemma pratt_closed (r : ℕ) : ∀ x ∈ pratt r, ∀ ℓ ∈ (x - 1).primeFactors, ℓ ∈ pratt r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro x hx ℓ hℓ
    rcases mem_pratt_iff.mp hx with h | ⟨ℓ', hℓ', hxℓ'⟩
    · subst h
      exact pratt_subset hℓ (self_mem_pratt ℓ)
    · exact pratt_subset hℓ' (ih ℓ' (lt_of_mem_primeFactors_sub_one hℓ') x hxℓ' ℓ hℓ)

lemma card_pratt_le (r : ℕ) :
    (pratt r).card ≤ 1 + ∑ ℓ ∈ (r - 1).primeFactors, (pratt ℓ).card := by
  rw [pratt_eq]
  have h1 := Finset.card_insert_le r ((r - 1).primeFactors.attach.biUnion fun ℓ => pratt ℓ.1)
  have h2 := Finset.card_biUnion_le (s := (r - 1).primeFactors.attach) (t := fun ℓ => pratt ℓ.1)
  rw [Finset.sum_attach (s := (r - 1).primeFactors) (f := fun ℓ => (pratt ℓ).card)] at h2
  omega

lemma pratt_two : pratt 2 = {2} := by
  rw [pratt_eq]
  have : (2 - 1).primeFactors = ∅ := by simp
  rw [this]
  rfl

lemma two_pow_card_pratt_le {r : ℕ} (hr : r.Prime) : 2 ^ (pratt r).card ≤ r ^ 2 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    by_cases h2 : r = 2
    · subst h2; rw [pratt_two]; simp
    have hodd : Odd r := hr.odd_of_ne_two h2
    have hr3 : 3 ≤ r := by
      have := hr.two_le
      rcases hodd with ⟨k, hk⟩
      omega
    set s := (r - 1).primeFactors with hs
    have h2s : 2 ∈ s := by
      rw [hs, Nat.mem_primeFactors]
      refine ⟨Nat.prime_two, ?_, by omega⟩
      rcases hodd with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    set A := ∏ ℓ ∈ s.erase 2, ℓ with hA
    have hA2 : 2 * A ≤ r - 1 := by
      have h1 : 2 * A = ∏ ℓ ∈ s, ℓ := Finset.mul_prod_erase s (fun ℓ => ℓ) h2s
      rw [h1]
      exact Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)
    have hprod : ∏ ℓ ∈ s, 2 ^ (pratt ℓ).card ≤ 2 * A ^ 2 := by
      rw [← Finset.mul_prod_erase s (fun ℓ => 2 ^ (pratt ℓ).card) h2s, pratt_two]
      simp only [Finset.card_singleton, pow_one]
      refine Nat.mul_le_mul_left 2 ?_
      rw [hA, ← Finset.prod_pow]
      refine Finset.prod_le_prod fun ℓ hℓ => ?_
      have hℓs := Finset.mem_of_mem_erase hℓ
      exact ih ℓ (lt_of_mem_primeFactors_sub_one hℓs) (Nat.prime_of_mem_primeFactors hℓs)
    calc 2 ^ (pratt r).card ≤ 2 ^ (1 + ∑ ℓ ∈ s, (pratt ℓ).card) :=
          Nat.pow_le_pow_right (by norm_num) (card_pratt_le r)
      _ = 2 * ∏ ℓ ∈ s, 2 ^ (pratt ℓ).card := by rw [pow_add, pow_one, Finset.prod_pow_eq_pow_sum]
      _ ≤ 2 * (2 * A ^ 2) := Nat.mul_le_mul_left 2 hprod
      _ = (2 * A) ^ 2 := by ring
      _ ≤ (r - 1) ^ 2 := Nat.pow_le_pow_left hA2 2
      _ ≤ r ^ 2 := Nat.pow_le_pow_left (Nat.sub_le r 1) 2

/-- The Pratt closure of the primes of `D`. -/
def prattSet (D : ℕ) : Finset ℕ := D.primeFactors.biUnion pratt

lemma mem_prattSet {D x : ℕ} : x ∈ prattSet D ↔ ∃ r ∈ D.primeFactors, x ∈ pratt r := by
  simp [prattSet]

lemma prime_le_of_mem_prattSet {D x : ℕ} (hx : x ∈ prattSet D) : x.Prime ∧ x ≤ D := by
  obtain ⟨r, hr, hxr⟩ := mem_prattSet.mp hx
  obtain ⟨hrp, hrD, hD0⟩ := Nat.mem_primeFactors.mp hr
  exact ⟨prime_of_mem_pratt hrp hxr,
    (le_of_mem_pratt hxr).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hrD)⟩

lemma prattSet_closed {D x : ℕ} (hx : x ∈ prattSet D) {ℓ : ℕ} (hℓ : ℓ ∈ (x - 1).primeFactors) :
    ℓ ∈ prattSet D := by
  obtain ⟨r, hr, hxr⟩ := mem_prattSet.mp hx
  exact mem_prattSet.mpr ⟨r, hr, pratt_closed r x hxr ℓ hℓ⟩

lemma mem_prattSet_of_mem_primeFactors {D r : ℕ} (hr : r ∈ D.primeFactors) : r ∈ prattSet D :=
  mem_prattSet.mpr ⟨r, hr, self_mem_pratt r⟩

lemma two_pow_card_prattSet_le {D : ℕ} (hD : D ≠ 0) : 2 ^ (prattSet D).card ≤ D ^ 2 := by
  calc 2 ^ (prattSet D).card ≤ 2 ^ (∑ r ∈ D.primeFactors, (pratt r).card) :=
        Nat.pow_le_pow_right (by norm_num) Finset.card_biUnion_le
    _ = ∏ r ∈ D.primeFactors, 2 ^ (pratt r).card := (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ r ∈ D.primeFactors, r ^ 2 :=
        Finset.prod_le_prod fun r hr => two_pow_card_pratt_le (Nat.prime_of_mem_primeFactors hr)
    _ = (∏ r ∈ D.primeFactors, r) ^ 2 := Finset.prod_pow _ _ _
    _ ≤ D ^ 2 := Nat.pow_le_pow_left
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (Nat.prod_primeFactors_dvd D)) 2

/-- `lcm(D, lcm_{r ∈ prattSet D} (r - 1))`. -/
def prattBound (D : ℕ) : ℕ := Nat.lcm D ((prattSet D).lcm fun r => r - 1)

lemma dvd_prattBound (D : ℕ) : D ∣ prattBound D := Nat.dvd_lcm_left _ _

lemma sub_one_dvd_prattBound {D r : ℕ} (hr : r ∈ prattSet D) : r - 1 ∣ prattBound D :=
  (Finset.dvd_lcm (f := fun r => r - 1) hr).trans (Nat.dvd_lcm_right _ _)

lemma prattBound_dvd_mul (D : ℕ) : prattBound D ∣ D * ∏ r ∈ prattSet D, (r - 1) :=
  (Nat.lcm_dvd_mul _ _).trans (mul_dvd_mul_left D (Finset.lcm_dvd_prod _ _))

lemma prattBound_le {D : ℕ} (hD : D ≠ 0) : prattBound D ≤ D ^ ((prattSet D).card + 1) := by
  have hprod : ∏ r ∈ prattSet D, (r - 1) ≤ D ^ (prattSet D).card :=
    Finset.prod_le_pow_card _ _ _ fun r hr => by
      have := (prime_le_of_mem_prattSet hr).2; omega
  have hpos : 0 < ∏ r ∈ prattSet D, (r - 1) := Finset.prod_pos fun r hr => by
    have := (prime_le_of_mem_prattSet hr).1.two_le; omega
  calc prattBound D ≤ D * ∏ r ∈ prattSet D, (r - 1) :=
        Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hD) hpos) (prattBound_dvd_mul D)
    _ ≤ D * D ^ (prattSet D).card := Nat.mul_le_mul_left D hprod
    _ = D ^ ((prattSet D).card + 1) := by ring

lemma prattBound_ne_zero {D : ℕ} (hD : D ≠ 0) : prattBound D ≠ 0 := by
  have hpos : 0 < ∏ r ∈ prattSet D, (r - 1) := Finset.prod_pos fun r hr => by
    have := (prime_le_of_mem_prattSet hr).1.two_le; omega
  exact Nat.lcm_ne_zero hD (by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨r, hr, h0⟩
    have := (prime_le_of_mem_prattSet hr).1.two_le
    omega)

/-- Every prime of `prattBound D` lies in `prattSet D`. -/
lemma mem_prattSet_of_dvd_prattBound {D : ℕ} (hD : D ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ℓ ∣ prattBound D) : ℓ ∈ prattSet D := by
  have h1 := (prattBound_dvd_mul D)
  rcases (Nat.Prime.dvd_mul hℓ).mp (h.trans h1) with h2 | h2
  · exact mem_prattSet_of_mem_primeFactors (Nat.mem_primeFactors.mpr ⟨hℓ, h2, hD⟩)
  · obtain ⟨r, hr, hℓr⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).mp h2
    have hr2 := (prime_le_of_mem_prattSet hr).1.two_le
    exact prattSet_closed hr (Nat.mem_primeFactors.mpr ⟨hℓ, hℓr, by omega⟩)

/-- The closure property of `prattBound D`: `r - 1 ∣ prattBound D` for every prime `r` dividing it. -/
lemma prattBound_closed {D : ℕ} (hD : D ≠ 0) {r : ℕ} (hr : r.Prime) (h : r ∣ prattBound D) :
    r - 1 ∣ prattBound D :=
  sub_one_dvd_prattBound (mem_prattSet_of_dvd_prattBound hD hr h)

end MorganMullen
