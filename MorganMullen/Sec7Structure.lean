import MorganMullen.Sec6NumberOfConditions
import MorganMullen.Sec7Pratt
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Section 7: structure of components

* Lemma 7.1 (cosets), Theorem 7.2 (structure of components), the admissible `K` of type (A) (crude)
  and (B) (closure), Lemma 7.4, Corollary 7.6 (weight of a component), Proposition 7.7 (finite reduction),
  Lemma 7.5 (size of the closure), and the sums `W_cl`, `W_cr` used for Theorem 7.8 (Theorem 7.8 itself:
  `Sec7Weights.lean`).
-/

set_option linter.unusedSectionVars false

namespace MorganMullen

open Finset

section Closure

variable (q o₀ : ℕ)

/-- `K₀ = o₀' (q^{o₀} - 1)`. -/
def Kzero : ℕ := pfree (charOf q) o₀ * (q ^ o₀ - 1)

/-- `lcm(1, …, m)`. -/
def lcmUpTo (m : ℕ) : ℕ := (Icc 1 m).lcm id

/-- (A) `L₀ = lcm(1, …, o₀)_{p'}`. -/
def Lzero : ℕ := pfree (charOf q) (lcmUpTo o₀)

/-- (A) the crude choice `K = lcm(K₀, L₀)`. -/
def Kcrude : ℕ := Nat.lcm (Kzero q o₀) (Lzero q o₀)

/-- `Λ = o₀' lcm(1, …, o₀)`. -/
def Lambda : ℕ := pfree (charOf q) o₀ * lcmUpTo o₀

/-- (B) `O₀ = lcm(o₀, ord_{ℓ^{v_ℓ}}(q) : ℓ ∣ o₀')`, `v_ℓ = v_ℓ(o₀') + v_ℓ(q^{o₀} - 1)`. -/
noncomputable def Ozero : ℕ :=
  Nat.lcm o₀ ((pfree (charOf q) o₀).primeFactors.lcm fun ℓ =>
    ordMod q (ℓ ^ ((pfree (charOf q) o₀).factorization ℓ + (q ^ o₀ - 1).factorization ℓ)))

/-- (B) the closure sequence `D₀ = (O₀)_{p'}`, `D_{i+1} = lcm(D_i, (ord_{D_i}(q))_{p'})`. -/
noncomputable def Dseq : ℕ → ℕ
  | 0 => pfree (charOf q) (Ozero q o₀)
  | i + 1 => Nat.lcm (Dseq i) (pfree (charOf q) (ordMod q (Dseq i)))

/-- The number of steps after which the closure sequence is certainly stable (by Lemma 7.5 every
strict step at least doubles, and `log₂ D_∞ ≤ log₂ D₀ + 2 (log₂ D₀)²`). -/
def closureSteps (D₀ : ℕ) : ℕ := 2 * (Nat.log 2 D₀ + 1) ^ 2 + 1

/-- (B) `D_∞`, the limit of the closure sequence. -/
noncomputable def Dinf : ℕ := Dseq q o₀ (closureSteps (Dseq q o₀ 0))

/-- (B) `K = lcm(K₀, D_∞)`. -/
noncomputable def Kclosure : ℕ := Nat.lcm (Kzero q o₀) (Dinf q o₀)

/-- (B) `O_∞ = lcm(O₀, ord_{D_∞}(q))`. -/
noncomputable def Oinf : ℕ := Nat.lcm (Ozero q o₀) (ordMod q (Dinf q o₀))

/-- `N** = lcm(K, O_∞)` (Proposition 7.7). -/
noncomputable def Nstarstar : ℕ := Nat.lcm (Kclosure q o₀) (Oinf q o₀)

/-- `∑_{o ∣ O, o ≥ o₀} q^{-o} ∑_{d ∣ o, d' ∣ D} d gcd(q^o - 1, D/d')`. -/
noncomputable def Wsum (O D : ℕ) : ℚ :=
  ∑ o ∈ O.divisors.filter (o₀ ≤ ·), ((q : ℚ) ^ o)⁻¹ *
    ∑ d ∈ o.divisors.filter (fun d => pfree (charOf q) d ∣ D),
      (d : ℚ) * (Nat.gcd (q ^ o - 1) (D / pfree (charOf q) d) : ℚ)

/-- `W_cl(q, o₀)` (Corollary 7.6, closure (B)). -/
noncomputable def Wcl : ℚ := Wsum q o₀ (Oinf q o₀) (Dinf q o₀)

/-- `W_cr(q, o₀)` (Corollary 7.6, crude (A)). -/
noncomputable def Wcr : ℚ := Wsum q o₀ (Lambda q o₀) (pfree (charOf q) (Lambda q o₀))

end Closure

/-- An integer coprime to `L` in the progression `x' + t c`, provided no prime divides `L`, `x'`
and `c`. -/
lemma exists_coprime_add_mul {L x' c : ℕ} (hL0 : L ≠ 0)
    (h : ∀ ℓ, ℓ.Prime → ℓ ∣ L → ℓ ∣ c → ¬ ℓ ∣ x') :
    ∃ t : ℕ, Nat.Coprime L (x' + t * c) := by
  classical
  set t := ∏ ℓ ∈ L.primeFactors.filter (fun ℓ => ¬ ℓ ∣ x'), ℓ
  refine ⟨t, Nat.coprime_of_dvd fun ℓ hℓ hℓL hℓs => ?_⟩
  by_cases hx : ℓ ∣ x'
  · -- `ℓ ∤ t` and `ℓ ∤ c`
    have hc : ¬ ℓ ∣ c := fun hc => h ℓ hℓ hℓL hc hx
    have ht : ¬ ℓ ∣ t := by
      intro ht
      obtain ⟨r, hr, hℓr⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).mp ht
      obtain ⟨hrL, hrx⟩ := Finset.mem_filter.mp hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrL
      have : ℓ = r := (Nat.prime_dvd_prime_iff_eq hℓ hrp).mp hℓr
      exact hrx (this ▸ hx)
    have : ℓ ∣ t * c := (Nat.dvd_add_right hx).mp hℓs
    rcases (Nat.Prime.dvd_mul hℓ).mp this with h1 | h1
    · exact ht h1
    · exact hc h1
  · have ht : ℓ ∣ t := Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hℓ, hℓL, hL0⟩, hx⟩)
    have : ℓ ∣ x' := (Nat.dvd_add_left (Dvd.dvd.mul_right ht c)).mp hℓs
    exact hx this


lemma addOrderOf_natCast_eq {m : ℕ} (hm : m ≠ 0) (z : ℕ) :
    addOrderOf (z : ZMod m) = m / Nat.gcd m z := ZMod.addOrderOf_coe z hm

/-- **Lemma 7.1** (cosets). -/
theorem coset_contains_order {m : ℕ} [NeZero m] (x : ZMod m) {d : ℕ} (hd : d ∣ m) :
    ∃ h ∈ AddSubgroup.zmultiples (((m / d : ℕ) : ZMod m)),
      addOrderOf (x + h) = Nat.lcm (addOrderOf x) d := by
  have hm : m ≠ 0 := NeZero.ne m
  set a := addOrderOf x with ha
  have hapos : 0 < a := addOrderOf_pos x
  have ham : a ∣ m := by have := addOrderOf_dvd_card (x := x); rwa [ZMod.card] at this
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hm hd
  set L := Nat.lcm a d with hL
  have hL0 : L ≠ 0 := Nat.lcm_ne_zero hapos.ne' hd0
  have hLm : L ∣ m := Nat.lcm_dvd ham hd
  set M := m / L with hM
  have hML : M * L = m := Nat.div_mul_cancel hLm
  have hMpos : 0 < M := Nat.pos_of_ne_zero (by rintro h0; rw [h0, zero_mul] at hML; exact hm hML.symm)
  -- `x = M x'` and `m/d = M c`
  have hxval : addOrderOf ((x.val : ℕ) : ZMod m) = a := by rw [ZMod.natCast_zmod_val]
  rw [addOrderOf_natCast_eq hm] at hxval
  set g := Nat.gcd m x.val with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hm)
  have hga : g * a = m := by
    rw [← hxval]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have haL : a ∣ L := Nat.dvd_lcm_left _ _
  have hdL : d ∣ L := Nat.dvd_lcm_right _ _
  have hMg : M ∣ g := by
    obtain ⟨k, hk⟩ := haL
    refine ⟨k, ?_⟩
    have : M * k * a = g * a := by rw [hga, mul_assoc, mul_comm k, ← hk, hML]
    exact (Nat.eq_of_mul_eq_mul_right hapos this).symm
  obtain ⟨x', hx'⟩ : M ∣ x.val := hMg.trans (Nat.gcd_dvd_right _ _)
  obtain ⟨c, hc⟩ : d ∣ L := hdL
  have hmd : m / d = M * c := by
    rw [← hML, hc, show M * (d * c) = d * (M * c) by ring, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  -- `gcd(L, x') = L / a`
  have hgcd : Nat.gcd L x' * M = g := by
    rw [hg, hx', ← hML, mul_comm M L, mul_comm M x', Nat.gcd_mul_right]
  -- no prime divides `L`, `c` and `x'`
  have hprime : ∀ ℓ, ℓ.Prime → ℓ ∣ L → ℓ ∣ c → ¬ ℓ ∣ x' := by
    intro ℓ hℓ hℓL hℓc hℓx
    -- then `a ∣ L/ℓ` and `d ∣ L/ℓ`, contradicting `L = lcm a d`
    have hℓg : ℓ ∣ Nat.gcd L x' := Nat.dvd_gcd hℓL hℓx
    obtain ⟨k, hk⟩ := hℓg
    have hLa : L = a * (ℓ * k) := by
      have h1 : Nat.gcd L x' * M * a = L * M := by rw [hgcd, hga, ← hML, mul_comm]
      rw [hk] at h1
      have : M * (a * (ℓ * k)) = M * L := by linarith [h1]
      exact (Nat.eq_of_mul_eq_mul_left hMpos this).symm
    obtain ⟨j, hj⟩ := hℓc
    have hLd : L = d * (ℓ * j) := by rw [hc, hj]
    have h1 : a ∣ L / ℓ := ⟨k, by rw [hLa, mul_left_comm, Nat.mul_div_cancel_left _ hℓ.pos]⟩
    have h2 : d ∣ L / ℓ := ⟨j, by rw [hLd, mul_left_comm, Nat.mul_div_cancel_left _ hℓ.pos]⟩
    have h3 : L ∣ L / ℓ := Nat.lcm_dvd h1 h2
    have h4 : L / ℓ < L := Nat.div_lt_self (Nat.pos_of_ne_zero hL0) hℓ.one_lt
    exact absurd (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hℓL) hℓ.pos) h3)
      (not_le.mpr h4)
  obtain ⟨t, ht⟩ := exists_coprime_add_mul hL0 hprime
  refine ⟨t • ((m / d : ℕ) : ZMod m), AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) t, ?_⟩
  have hval : x + t • ((m / d : ℕ) : ZMod m) = ((M * (x' + t * c) : ℕ) : ZMod m) := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← ZMod.natCast_zmod_val x, ← Nat.cast_add, hx', hmd]
    congr 1; ring
  rw [hval, addOrderOf_natCast_eq hm, ← hML, mul_comm M L, mul_comm M (x' + t * c),
    Nat.gcd_mul_right, ht.gcd_eq_one, one_mul, Nat.mul_div_cancel _ hMpos]


namespace Model
open Finset

variable {q n : ℕ} [NeZero n]

open Finset

/-- **Lemma 7.1**, fibre version. -/
theorem fibre_contains_order {d : ℕ} (hd : d ∣ n) {x : ZMod (nfree q n)} (hx : x ∈ targets q n d) :
    ∃ i : ZMod (nfree q n), ((dfree q d : ℕ) : ZMod _) * i = x ∧
      addOrderOf i = dfree q d * addOrderOf x := by
  obtain ⟨i₀, hi₀⟩ := exists_dfree_mul_eq hd (mem_targets.mp hx)
  have hdn : dfree q d ∣ nfree q n := dfree_dvd_nfree hd
  have hd0 : dfree q d ≠ 0 := (dfree_pos (ne_zero_of_dvd_ne_zero (NeZero.ne n) hd)).ne'
  obtain ⟨h, hh, hord⟩ := coset_contains_order i₀ hdn
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hh
  refine ⟨i₀ + k • ((nfree q n / dfree q d : ℕ) : ZMod (nfree q n)), ?_, ?_⟩
  · rw [mul_add, ← hi₀, add_eq_left, zsmul_eq_mul, mul_left_comm, ← Nat.cast_mul,
      Nat.mul_div_cancel' hdn, ZMod.natCast_self, mul_zero]
  · rw [hord, ← hi₀, natCast_mul_eq_nsmul, addOrderOf_nsmul' _ hd0]
    set a := addOrderOf i₀
    rw [Nat.lcm, Nat.mul_comm a, Nat.mul_div_assoc _ (Nat.gcd_dvd_left a _), Nat.gcd_comm]


lemma exists_mem_fibre_of_mem (hq : IsPrimePow q) {C : Cond q n} (hC : C ∈ conds q n)
    {x : ZMod (nfree q n)} (hx : x ∈ C.2) :
    ∃ i ∈ fibre q n C, ((dfree q C.1 : ℕ) : ZMod _) * i = x := by
  obtain ⟨d, hd, y, hy, rfl⟩ := mem_conds.mp hC
  have hxt : x ∈ targets q n d := orbit_subset_targets hq hy hx
  obtain ⟨i, hi⟩ := exists_dfree_mul_eq (Nat.dvd_of_mem_divisors hd) (mem_targets.mp hxt)
  exact ⟨i, mem_fibre.mpr (by rw [hi]; exact hx), hi⟩

lemma level_dvd_n {C : Cond q n} (hC : C ∈ conds q n) : C.1 ∣ n := by
  obtain ⟨d, hd, y, hy, rfl⟩ := mem_conds.mp hC
  exact Nat.dvd_of_mem_divisors hd

/-- Two elements of the fibre of a condition differ by a power of `q^d` and an element of order
dividing `d'`. -/
lemma fibre_diff (hq : IsPrimePow q) {C : Cond q n} (hC : C ∈ conds q n) {i y : ZMod (nfree q n)}
    (hi : i ∈ fibre q n C) (hy : y ∈ fibre q n C) :
    ∃ m : ℕ, ∃ z : ZMod (nfree q n), ((dfree q C.1 : ℕ) : ZMod _) * z = 0 ∧
      y = (q : ZMod (nfree q n)) ^ (C.1 * m) * i + z := by
  obtain ⟨d, hd, x, hx, rfl⟩ := mem_conds.mp hC
  rw [mem_fibre] at hi hy
  have horb : orbit q n d x = orbit q n d (((dfree q d : ℕ) : ZMod _) * i) :=
    (orbit_eq_of_mem hq hi).symm
  rw [horb] at hy
  obtain ⟨m, hm⟩ := (mem_orbit_iff hq).mp hy
  refine ⟨m, y - (q : ZMod (nfree q n)) ^ (d * m) * i, ?_, by ring⟩
  simp only
  rw [mul_sub, hm, pow_mul, mul_left_comm, sub_self]

lemma addOrderOf_dvd_of_mul_eq_zero {m : ℕ} {k : ℕ} {z : ZMod m} (h : (k : ZMod m) * z = 0) :
    addOrderOf z ∣ k := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← natCast_mul_eq_nsmul]; exact h

lemma addOrderOf_add_dvd {m K : ℕ} {a b : ZMod m} (ha : addOrderOf a ∣ K) (hb : addOrderOf b ∣ K) :
    addOrderOf (a + b) ∣ K :=
  ((AddCommute.all a b).addOrderOf_add_dvd_lcm).trans (Nat.lcm_dvd ha hb)

lemma addOrderOf_dvd_dfree_mul (d : ℕ) (i : ZMod (nfree q n)) :
    addOrderOf i ∣ dfree q d * addOrderOf (((dfree q d : ℕ) : ZMod (nfree q n)) * i) := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero]
  have h : (dfree q d * addOrderOf (((dfree q d : ℕ) : ZMod (nfree q n)) * i)) • i =
      addOrderOf (((dfree q d : ℕ) : ZMod (nfree q n)) * i) • (((dfree q d : ℕ) : ZMod (nfree q n)) * i) := by
    rw [natCast_mul_eq_nsmul, ← mul_nsmul, mul_comm]
  rw [h, addOrderOf_nsmul_eq_zero]

/-- The propagation step of Theorem 7.2 (a). -/
lemma fibre_ord_dvd_of_one (hq : IsPrimePow q) {K : ℕ}
    (hii : pfree (chr q) (ordMod q K) ∣ K) {C : Cond q n} (hC : C ∈ essConds q n)
    {i : ZMod (nfree q n)} (hi : i ∈ fibre q n C) (hiK : addOrderOf i ∣ K) :
    ∀ y ∈ fibre q n C, addOrderOf y ∣ K := by
  obtain ⟨hCc, hess⟩ := mem_essConds.mp hC
  have hx := mem_fibre.mp hi
  have hco := (codim_eq_of_mem hq hCc hx).1
  have he : addOrderOf (((dfree q C.1 : ℕ) : ZMod (nfree q n)) * i) ∣ K :=
    (addOrderOf_mul_dvd _ i).trans hiK
  have hdK : C.1 ∣ ordMod q K := by
    rw [hco] at hess
    exact hess.trans (ordMod_dvd_ordMod he)
  have hd'K : dfree q C.1 ∣ K := (pfree_dvd_pfree hdK _).trans hii
  intro y hy
  obtain ⟨m, z, hz, rfl⟩ := fibre_diff hq hCc hi hy
  refine addOrderOf_add_dvd ?_ ((addOrderOf_dvd_of_mul_eq_zero hz).trans hd'K)
  rw [addOrderOf_qpow_mul hq]; exact hiK

/-- **Theorem 7.2 (a)**. -/
theorem structure_a' (hq : IsPrimePow q) {C₀ : Cond q n} (hC₀ : C₀ ∈ essConds q n)
    {K : ℕ} (hi : dfree q C₀.1 * tord q n C₀ ∣ K) (hii : pfree (chr q) (ordMod q K) ∣ K) :
    ∀ C ∈ component q n (essConds q n) C₀, ∀ i ∈ fibre q n C, addOrderOf i ∣ K := by
  classical
  have hC₀c := essConds_subset hC₀
  -- the base case
  obtain ⟨x₀, hx₀⟩ : C₀.2.Nonempty := by
    obtain ⟨d, -, y, -, h⟩ := mem_conds.mp hC₀c
    exact ⟨y, h ▸ mem_orbit_self d y⟩
  obtain ⟨i₀, hi₀, hi₀x⟩ := exists_mem_fibre_of_mem hq hC₀c hx₀
  have hbase : ∀ y ∈ fibre q n C₀, addOrderOf y ∣ K := by
    refine fibre_ord_dvd_of_one hq hii hC₀ hi₀ ?_
    refine (addOrderOf_dvd_dfree_mul C₀.1 i₀).trans ?_
    rw [hi₀x, ← (codim_eq_of_mem hq hC₀c hx₀).2]; exact hi
  -- propagation along the component
  let P : Cond q n → Prop := fun C => ∀ y ∈ fibre q n C, addOrderOf y ∣ K
  have key : ∀ a b, SameComp q n (essConds q n) a b → (P a ↔ P b) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      obtain ⟨ha, hb, π, hπ, π', hπ', j, h1, -⟩ := hab
      have hπ1 := (Finset.mem_product.mp hπ).1
      have hπ'1 := (Finset.mem_product.mp hπ').1
      have hord : addOrderOf π'.1 = addOrderOf π.1 := by rw [h1, addOrderOf_qpow_mul hq]
      constructor
      · intro hPa
        exact fibre_ord_dvd_of_one hq hii hb hπ'1 (hord ▸ hPa _ hπ1)
      · intro hPb
        exact fibre_ord_dvd_of_one hq hii ha hπ1 (hord ▸ hPb _ hπ'1)
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  intro C hC
  exact (key _ _ (Finset.mem_filter.mp hC).2).mp hbase

/-- **Theorem 7.2 (b)**. -/
theorem structure_b' (hq : IsPrimePow q) {C₀ : Cond q n} (hC₀ : C₀ ∈ essConds q n)
    {K : ℕ} (hi : dfree q C₀.1 * tord q n C₀ ∣ K) (hii : pfree (chr q) (ordMod q K) ∣ K) :
    (∀ C ∈ component q n (essConds q n) C₀,
      tord q n C ∣ K ∧ C.1 ∣ ordMod q K ∧ dfree q C.1 * tord q n C ∣ K ∧
        codim q n C ∣ ordMod q K) ∧
    levelLcm q n (component q n (essConds q n) C₀) ∣ pfree (chr q) (ordMod q K) := by
  classical
  have ha := structure_a' hq hC₀ hi hii
  have hmain : ∀ C ∈ component q n (essConds q n) C₀,
      tord q n C ∣ K ∧ C.1 ∣ ordMod q K ∧ dfree q C.1 * tord q n C ∣ K ∧
        codim q n C ∣ ordMod q K := by
    intro C hC
    have hCe : C ∈ essConds q n := (Finset.mem_filter.mp hC).1
    have hCc := essConds_subset hCe
    obtain ⟨x, hx⟩ : C.2.Nonempty := by
      obtain ⟨d, -, y, -, h⟩ := mem_conds.mp hCc
      exact ⟨y, h ▸ mem_orbit_self d y⟩
    obtain ⟨hco, hto⟩ := codim_eq_of_mem hq hCc hx
    obtain ⟨i, hi', hix⟩ := exists_mem_fibre_of_mem hq hCc hx
    have htK : tord q n C ∣ K := by
      rw [hto, ← hix]; exact (addOrderOf_mul_dvd _ i).trans (ha C hC i hi')
    have hcoK : codim q n C ∣ ordMod q K := by rw [hco]; exact ordMod_dvd_ordMod (hto ▸ htK)
    refine ⟨htK, ?_, ?_, hcoK⟩
    · exact (mem_essConds.mp hCe).2.trans hcoK
    · -- an element of the fibre of order `d' e`
      have hxt : x ∈ targets q n C.1 := by
        obtain ⟨d, hd, y, hy, hCeq⟩ := mem_conds.mp hCc
        rw [hCeq] at hx ⊢; exact orbit_subset_targets hq hy hx
      obtain ⟨j, hj, hjo⟩ := fibre_contains_order (level_dvd_n hCc) hxt
      have hjf : j ∈ fibre q n C := mem_fibre.mpr (by rw [hj]; exact hx)
      rw [hto, ← hjo]; exact ha C hC j hjf
  refine ⟨hmain, Finset.lcm_dvd fun C hC => ?_⟩
  exact pfree_dvd_pfree (hmain C hC).2.1 _

end Model


namespace Model
open Finset
variable {q n : ℕ} [NeZero n]

lemma qUnit_cancel (hq : IsPrimePow q) (j : ℕ) {a b : ZMod (nfree q n)}
    (h : (q : ZMod (nfree q n)) ^ j * a = (q : ZMod (nfree q n)) ^ j * b) : a = b := by
  have hu : IsUnit ((q : ZMod (nfree q n)) ^ j) := by
    have := ((qUnit (n := n) hq) ^ j).isUnit; simpa using this
  exact hu.mul_left_cancel h

lemma card_nsmul_eq_zero_le' (g : ℕ) (hg : 0 < g) :
    (univ.filter fun z : ZMod (nfree q n) => (g : ZMod (nfree q n)) * z = 0).card ≤ g := by
  have := IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod (nfree q n)) hg
  have heq : (univ.filter fun z : ZMod (nfree q n) => (g : ZMod (nfree q n)) * z = 0) =
      (univ.filter fun z : ZMod (nfree q n) => g • z = 0) :=
    Finset.filter_congr fun z _ => by rw [natCast_mul_eq_nsmul]
  rw [heq]; exact this

/-- Elements with prescribed images under two multiplications: at most `gcd` many. -/
lemma card_fibre_two_le (A B : ℕ) (hA : 0 < A) (y : ZMod (nfree q n)) :
    (univ.filter fun x : ZMod (nfree q n) =>
        (A : ZMod (nfree q n)) * x = 0 ∧ (B : ZMod (nfree q n)) * x = y).card ≤ Nat.gcd A B := by
  classical
  set S := univ.filter fun x : ZMod (nfree q n) =>
    (A : ZMod (nfree q n)) * x = 0 ∧ (B : ZMod (nfree q n)) * x = y
  rcases S.eq_empty_or_nonempty with h | ⟨x₁, hx₁⟩
  · rw [h]; exact Nat.zero_le _
  have hg : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_left _ hA
  calc S.card ≤ ((univ.filter fun z : ZMod (nfree q n) =>
        ((Nat.gcd A B : ℕ) : ZMod (nfree q n)) * z = 0).image (fun z => x₁ + z)).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨hxA, hxB⟩ := (Finset.mem_filter.mp hx).2
        obtain ⟨hx₁A, hx₁B⟩ := (Finset.mem_filter.mp hx₁).2
        refine Finset.mem_image.mpr ⟨x - x₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by ring⟩
        rw [natCast_mul_eq_nsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero]
        apply Nat.dvd_gcd
        · exact addOrderOf_dvd_of_mul_eq_zero (by rw [mul_sub, hxA, hx₁A, sub_zero])
        · exact addOrderOf_dvd_of_mul_eq_zero (by rw [mul_sub, hxB, hx₁B, sub_self])
    _ ≤ (univ.filter fun z : ZMod (nfree q n) =>
        ((Nat.gcd A B : ℕ) : ZMod (nfree q n)) * z = 0).card := Finset.card_image_le
    _ ≤ Nat.gcd A B := card_nsmul_eq_zero_le' _ hg

end Model

namespace Model
open Finset
variable {q n : ℕ} [NeZero n]

lemma qpow_order (hq : IsPrimePow q) :
    ∃ r, 0 < r ∧ (q : ZMod (nfree q n)) ^ r = 1 := by
  refine ⟨orderOf (qUnit (n := n) hq), orderOf_pos _, ?_⟩
  have := pow_orderOf_eq_one (qUnit (n := n) hq)
  have h2 := congrArg (fun u : (ZMod (nfree q n))ˣ => (u : ZMod (nfree q n))) this
  simp only [Units.val_pow_eq_pow_val, coe_qUnit, Units.val_one] at h2
  exact h2

lemma exists_qpow_of_qpow_mul_eq (hq : IsPrimePow q) {a y : ZMod (nfree q n)} {j j₂ : ℕ}
    (h : (q : ZMod (nfree q n)) ^ j * a = (q : ZMod (nfree q n)) ^ j₂ * y) :
    ∃ k : ℕ, a = (q : ZMod (nfree q n)) ^ k * y := by
  obtain ⟨r, hr, hr1⟩ := qpow_order (n := n) hq
  refine ⟨r * (j + 1) - j + j₂, ?_⟩
  have hle : j ≤ r * (j + 1) := by nlinarith
  calc a = (q : ZMod (nfree q n)) ^ (r * (j + 1)) * a := by rw [pow_mul, hr1, one_pow, one_mul]
    _ = (q : ZMod (nfree q n)) ^ (r * (j + 1) - j) * ((q : ZMod (nfree q n)) ^ j * a) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    _ = _ := by rw [h, ← mul_assoc, ← pow_add]

lemma qpow_periodic_of {y : ZMod (nfree q n)} {o : ℕ}
    (h : (q : ZMod (nfree q n)) ^ o * y = y) (hpos : 0 < o) (k : ℕ) :
    ∃ k' < o, (q : ZMod (nfree q n)) ^ k * y = (q : ZMod (nfree q n)) ^ k' * y := by
  refine ⟨k % o, Nat.mod_lt _ hpos, ?_⟩
  conv_lhs => rw [← Nat.mod_add_div k o, pow_add, mul_assoc]
  congr 1
  induction (k / o) with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, mul_assoc, h, ih]

lemma sameComp_mem {ℰ : Finset (Cond q n)} {a b : Cond q n} (h : SameComp q n ℰ a b) :
    a = b ∨ (a ∈ ℰ ∧ b ∈ ℰ) := by
  induction h with
  | rel a b hab => exact Or.inr ⟨hab.1, hab.2.1⟩
  | refl a => exact Or.inl rfl
  | symm a b _ ih => rcases ih with h | h
                     · exact Or.inl h.symm
                     · exact Or.inr ⟨h.2, h.1⟩
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with h1 | h1 <;> rcases ih2 with h2 | h2
    · exact Or.inl (h1.trans h2)
    · subst h1; exact Or.inr h2
    · subst h2; exact Or.inr h1
    · exact Or.inr ⟨h1.1, h2.2⟩

lemma mem_component_of_sameComp {ℰ : Finset (Cond q n)} {C₀ b c : Cond q n}
    (hb : b ∈ component q n ℰ C₀) (hbc : SameComp q n ℰ b c) : c ∈ component q n ℰ C₀ := by
  classical
  obtain ⟨hbℰ, h0b⟩ := Finset.mem_filter.mp hb
  refine Finset.mem_filter.mpr ⟨?_, h0b.trans _ _ _ hbc⟩
  rcases sameComp_mem hbc with h | h
  · exact h ▸ hbℰ
  · exact h.2

/-- **Theorem 7.2 (c)**. -/
theorem structure_c' (hq : IsPrimePow q) {C₀ : Cond q n} (hC₀ : C₀ ∈ essConds q n) (o D : ℕ)
    (hD : levelLcm q n (component q n (essConds q n) C₀) ∣ D) :
    ((component q n (essConds q n) C₀).filter fun C => codim q n C = o).card ≤
        ∑ d ∈ o.divisors.filter (fun d => dfree q d ∣ D), d * Nat.gcd (q ^ o - 1) (D / dfree q d) ∧
      ∑ d ∈ o.divisors.filter (fun d => dfree q d ∣ D), d * Nat.gcd (q ^ o - 1) (D / dfree q d) ≤
        (∑ d ∈ o.divisors, d) * Nat.gcd (q ^ o - 1) D := by
  classical
  set comp := component q n (essConds q n) C₀ with hcomp
  have hC₀comp : C₀ ∈ comp := Finset.mem_filter.mpr ⟨hC₀, Relation.EqvGen.refl _⟩
  have hlev : ∀ C ∈ comp, dfree q C.1 ∣ D := fun C hC => (Finset.dvd_lcm hC).trans hD
  have hcompE : ∀ C ∈ comp, C ∈ essConds q n := fun C hC => (Finset.mem_filter.mp hC).1
  have hq2 : 2 ≤ q := hq.two_le
  -- second inequality
  have hsecond : ∑ d ∈ o.divisors.filter (fun d => dfree q d ∣ D), d * Nat.gcd (q ^ o - 1) (D / dfree q d)
      ≤ (∑ d ∈ o.divisors, d) * Nat.gcd (q ^ o - 1) D := by
    rw [Finset.sum_mul]
    calc ∑ d ∈ o.divisors.filter (fun d => dfree q d ∣ D), d * Nat.gcd (q ^ o - 1) (D / dfree q d)
        ≤ ∑ d ∈ o.divisors.filter (fun d => dfree q d ∣ D), d * Nat.gcd (q ^ o - 1) D := by
          refine Finset.sum_le_sum fun d hd => Nat.mul_le_mul_left _ ?_
          rcases Nat.eq_zero_or_pos o with ho | ho
          · subst ho; simp at hd
          have hpos : 0 < Nat.gcd (q ^ o - 1) D := Nat.gcd_pos_of_pos_left _ (by
            have : 1 < q ^ o := Nat.one_lt_pow ho.ne' (by omega)
            omega)
          exact Nat.le_of_dvd hpos (Nat.gcd_dvd_gcd_of_dvd_right _ (Nat.div_dvd_of_dvd
            (Finset.mem_filter.mp hd).2))
      _ ≤ ∑ d ∈ o.divisors, d * Nat.gcd (q ^ o - 1) D :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  refine ⟨?_, hsecond⟩
  rcases Nat.eq_zero_or_pos o with ho0 | hopos
  · -- no condition has codimension `0`
    subst ho0
    have : (comp.filter fun C => codim q n C = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro C hC h0
      have := one_le_codim hq (essConds_subset (hcompE C hC))
      omega
    rw [this]; exact Nat.zero_le _
  -- the invariant `η ↦ q-orbit of η^D`
  obtain ⟨x₀, hx₀⟩ : C₀.2.Nonempty := by
    obtain ⟨d, -, y, -, h⟩ := mem_conds.mp (essConds_subset hC₀)
    exact ⟨y, h ▸ mem_orbit_self d y⟩
  obtain ⟨i₀, hi₀, -⟩ := exists_mem_fibre_of_mem hq (essConds_subset hC₀) hx₀
  set y₀ : ZMod (nfree q n) := (D : ZMod (nfree q n)) * i₀
  let P : Cond q n → Prop := fun C =>
    ∀ i ∈ fibre q n C, ∃ j : ℕ, (D : ZMod (nfree q n)) * i = (q : ZMod (nfree q n)) ^ j * y₀
  have hstep : ∀ C ∈ comp, ∀ i ∈ fibre q n C, (∃ j : ℕ, (D : ZMod (nfree q n)) * i =
      (q : ZMod (nfree q n)) ^ j * y₀) → P C := by
    intro C hC i hi ⟨j, hj⟩ y hy
    obtain ⟨m, z, hz, rfl⟩ := fibre_diff hq (essConds_subset (hcompE C hC)) hi hy
    obtain ⟨c, hc⟩ := hlev C hC
    refine ⟨C.1 * m + j, ?_⟩
    have hDz : (D : ZMod (nfree q n)) * z = 0 := by
      rw [hc, Nat.cast_mul, mul_comm (dfree q C.1 : ZMod (nfree q n)), mul_assoc, hz, mul_zero]
    rw [mul_add, hDz, add_zero, mul_left_comm, hj, ← mul_assoc, ← pow_add]
  have hP₀ : P C₀ := hstep C₀ hC₀comp i₀ hi₀ ⟨0, by simp [y₀]⟩
  have key : ∀ a b, SameComp q n (essConds q n) a b → a ∈ comp → (P a ↔ P b) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      intro ha
      have hb : b ∈ comp := mem_component_of_sameComp ha (Relation.EqvGen.rel _ _ hab)
      obtain ⟨-, -, π, hπ, π', hπ', j, h1, -⟩ := hab
      have hπ1 := (Finset.mem_product.mp hπ).1
      have hπ'1 := (Finset.mem_product.mp hπ').1
      constructor
      · intro hPa
        obtain ⟨j1, hj1⟩ := hPa _ hπ1
        exact hstep b hb _ hπ'1 ⟨j + j1, by rw [h1, mul_left_comm, hj1, ← mul_assoc, ← pow_add]⟩
      · intro hPb
        obtain ⟨j2, hj2⟩ := hPb _ hπ'1
        rw [h1, mul_left_comm] at hj2
        obtain ⟨k, hk⟩ := exists_qpow_of_qpow_mul_eq hq hj2
        exact hstep a ha _ hπ1 ⟨k, hk⟩
    | refl a => intro _; exact Iff.rfl
    | symm a b hab ih =>
      intro hb
      have ha : a ∈ comp := mem_component_of_sameComp hb hab.symm
      exact (ih ha).symm
    | trans a b c hab hbc ih1 ih2 =>
      intro ha
      have hb : b ∈ comp := mem_component_of_sameComp ha hab
      exact (ih1 ha).trans (ih2 hb)
  have hPall : ∀ C ∈ comp, P C := fun C hC =>
    (key C₀ C (Finset.mem_filter.mp hC).2 hC₀comp).mp hP₀
  -- the sets `T_d`
  let T : ℕ → Finset (ZMod (nfree q n)) := fun d => univ.filter fun x =>
    tcodim q n x = o ∧ ∃ j < o, ((D / dfree q d : ℕ) : ZMod (nfree q n)) * x =
      (q : ZMod (nfree q n)) ^ j * y₀
  have hq1 : 1 ≤ q ^ o := Nat.one_le_pow _ _ hq.pos
  have hqo : 1 < q ^ o := Nat.one_lt_pow hopos.ne' (by omega)
  -- periodicity of `y₀` once some `x` with `tcodim x = o` maps into its orbit
  have hper : ∀ d, dfree q d ∣ D → ∀ x : ZMod (nfree q n), tcodim q n x = o → ∀ j : ℕ,
      ((D / dfree q d : ℕ) : ZMod (nfree q n)) * x = (q : ZMod (nfree q n)) ^ j * y₀ →
      (q : ZMod (nfree q n)) ^ o * y₀ = y₀ := by
    intro d _ x hx j hj
    have hxo : (q : ZMod (nfree q n)) ^ o * x = x := (qpow_mul_eq_self_iff hq o x).mpr (by
      rw [show ordMod q (addOrderOf x) = o from hx])
    apply qUnit_cancel hq j
    rw [← hj, ← mul_assoc, mul_comm ((q : ZMod (nfree q n)) ^ j), mul_assoc, ← hj, mul_left_comm,
      hxo]
  have hsub : (comp.filter fun C => codim q n C = o) ⊆
      (o.divisors.filter (fun d => dfree q d ∣ D)).biUnion
        (fun d => (T d).image fun x => ((d, orbit q n d x) : Cond q n)) := by
    intro C hC
    obtain ⟨hCcomp, hco⟩ := Finset.mem_filter.mp hC
    have hCe := hcompE C hCcomp
    obtain ⟨d, hd, x, hx, hess, rfl⟩ := (mem_essConds_iff hq).mp hCe
    rw [codim_orbit hq] at hco
    have hdD : dfree q d ∣ D := hlev _ hCcomp
    refine Finset.mem_biUnion.mpr ⟨d, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨hco ▸ hess, hopos.ne'⟩, hdD⟩, Finset.mem_image.mpr ⟨x, ?_, rfl⟩⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hco, ?_⟩
    -- an element of the fibre over `x`
    obtain ⟨i, hi, hix⟩ := exists_mem_fibre_of_mem hq (essConds_subset hCe) (mem_orbit_self d x)
    obtain ⟨j, hj⟩ := hPall _ hCcomp i hi
    have hDx : ((D / dfree q d : ℕ) : ZMod (nfree q n)) * x = (q : ZMod (nfree q n)) ^ j * y₀ := by
      rw [← hix, ← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hdD]; exact hj
    obtain ⟨j', hj', hjj⟩ := qpow_periodic_of (hper d hdD x hco j hDx) hopos j
    exact ⟨j', hj', hDx.trans hjj⟩
  have hbound : ∀ d ∈ o.divisors.filter (fun d => dfree q d ∣ D),
      ((T d).image fun x => ((d, orbit q n d x) : Cond q n)).card ≤
        d * Nat.gcd (q ^ o - 1) (D / dfree q d) := by
    intro d hd
    obtain ⟨hdo', hdD⟩ := Finset.mem_filter.mp hd
    have hdo : d ∣ o := Nat.dvd_of_mem_divisors hdo'
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hdo'
    have hs : ∀ x ∈ T d, (orbit q n d x).card = o / d := by
      intro x hx
      have hxo : tcodim q n x = o := (Finset.mem_filter.mp hx).2.1
      rw [card_orbit hq, ordMod_pow _ _ hdpos.ne']
      rw [show ordMod q (addOrderOf x) = o from hxo, Nat.gcd_eq_right hdo]
    have hclosed : ∀ x ∈ T d, orbit q n d x ⊆ T d := by
      intro x hx y hy
      obtain ⟨-, hxo, j, -, hj⟩ := Finset.mem_filter.mp hx
      obtain ⟨m, rfl⟩ := (mem_orbit_iff hq).mp hy
      rw [← pow_mul]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [tcodim_qpow_mul hq]; exact hxo, ?_⟩
      have hper' := hper d hdD x hxo j hj
      obtain ⟨j', hj', hjj⟩ := qpow_periodic_of hper' hopos (d * m + j)
      refine ⟨j', hj', ?_⟩
      rw [mul_left_comm, hj, ← mul_assoc, ← pow_add, hjj]
    have hcount := card_image_orbit_mul hq d (T d) hclosed _ hs
    -- `|T_d| ≤ o · gcd(q^o - 1, D/d')`
    have hT : (T d).card ≤ o * Nat.gcd (q ^ o - 1) (D / dfree q d) := by
      calc (T d).card ≤ ((range o).biUnion fun j => univ.filter fun x : ZMod (nfree q n) =>
            ((q ^ o - 1 : ℕ) : ZMod (nfree q n)) * x = 0 ∧
              ((D / dfree q d : ℕ) : ZMod (nfree q n)) * x = (q : ZMod (nfree q n)) ^ j * y₀).card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨-, hxo, j, hj, hjx⟩ := Finset.mem_filter.mp hx
            refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, ?_, hjx⟩⟩
            have hxo' : (q : ZMod (nfree q n)) ^ o * x = x := (qpow_mul_eq_self_iff hq o x).mpr (by
              rw [show ordMod q (addOrderOf x) = o from hxo])
            rw [Nat.cast_sub hq1, sub_mul, Nat.cast_pow, hxo', Nat.cast_one, one_mul, sub_self]
        _ ≤ ∑ j ∈ range o, (univ.filter fun x : ZMod (nfree q n) =>
            ((q ^ o - 1 : ℕ) : ZMod (nfree q n)) * x = 0 ∧
              ((D / dfree q d : ℕ) : ZMod (nfree q n)) * x = (q : ZMod (nfree q n)) ^ j * y₀).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ range o, Nat.gcd (q ^ o - 1) (D / dfree q d) :=
            Finset.sum_le_sum fun j _ => card_fibre_two_le _ _ (by omega) _
        _ = o * Nat.gcd (q ^ o - 1) (D / dfree q d) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    set g := Nat.gcd (q ^ o - 1) (D / dfree q d)
    obtain ⟨m, hm⟩ := hdo
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hm; omega)
    have hod : o / d = m := by rw [hm, Nat.mul_div_cancel_left _ hdpos]
    rw [hod] at hcount
    have hT' : (T d).card ≤ d * g * m := by
      calc (T d).card ≤ o * g := hT
        _ = d * g * m := by rw [hm]; ring
    have : ((T d).image fun x => ((d, orbit q n d x) : Cond q n)).card * m ≤ (d * g) * m := by
      rw [hcount]; exact hT'
    exact Nat.le_of_mul_le_mul_right this hmpos
  calc (comp.filter fun C => codim q n C = o).card
      ≤ ((o.divisors.filter (fun d => dfree q d ∣ D)).biUnion
          (fun d => (T d).image fun x => ((d, orbit q n d x) : Cond q n))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ d ∈ o.divisors.filter (fun d => dfree q d ∣ D),
          ((T d).image fun x => ((d, orbit q n d x) : Cond q n)).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum hbound

end Model

namespace Model

variable (q n : ℕ) [NeZero n]

/-- **Theorem 7.2 (a)** (structure of components): let `C₀` be essential and `K` an integer
with (i) `d₀' e₀ ∣ K` and (ii) `(ord_K(q))_{p'} ∣ K`. Then every `η` in a fibre of a condition of the
component of `C₀` has order dividing `K`. As in the paper, `C₀` may have any codimension (Remark 7.3).
The paper's assumption that `K` is `p`-free is contained in (ii): `ordMod q K = 0` if `p ∣ K` and
`K > 1`, so (ii) forces `p ∤ K` unless `K = 0`, a trivial case. -/
theorem structure_a (hq : IsPrimePow q) {C₀ : Cond q n} (hC₀ : C₀ ∈ essConds q n) {K : ℕ}
    (hi : dfree q C₀.1 * tord q n C₀ ∣ K) (hii : pfree (chr q) (ordMod q K) ∣ K) :
    ∀ C ∈ component q n (essConds q n) C₀, ∀ i ∈ fibre q n C, addOrderOf i ∣ K :=
  structure_a' hq hC₀ hi hii

/-- **Theorem 7.2 (b)**: every condition `(d, ξ)` of the component satisfies `ord ξ ∣ K`, `d ∣ ord_K(q)` and
`d' ord ξ ∣ K`; in particular all codimensions divide `ord_K(q)`, and `D_𝒞 ∣ (ord_K(q))_{p'}` (same
hypotheses as `structure_a`). -/
theorem structure_b (hq : IsPrimePow q) {C₀ : Cond q n} (hC₀ : C₀ ∈ essConds q n) {K : ℕ}
    (hi : dfree q C₀.1 * tord q n C₀ ∣ K) (hii : pfree (chr q) (ordMod q K) ∣ K) :
    (∀ C ∈ component q n (essConds q n) C₀,
      tord q n C ∣ K ∧ C.1 ∣ ordMod q K ∧ dfree q C.1 * tord q n C ∣ K ∧
        codim q n C ∣ ordMod q K) ∧
    levelLcm q n (component q n (essConds q n) C₀) ∣ pfree (chr q) (ordMod q K) :=
  structure_b' hq hC₀ hi hii

open Classical in
/-- **Theorem 7.2 (c)**: for every `o` and every multiple `D` of `D_𝒞`,
`N_𝒞(o) ≤ ∑_{d ∣ o, d' ∣ D} d gcd(q^o - 1, D/d') ≤ σ_1(o) gcd(q^o - 1, D)`. -/
theorem structure_c (hq : IsPrimePow q) {C₀ : Cond q n} (hC₀ : C₀ ∈ essConds q n) (o D : ℕ)
    (hD : levelLcm q n (component q n (essConds q n) C₀) ∣ D) :
    ((component q n (essConds q n) C₀).filter fun C => codim q n C = o).card ≤
        ∑ d ∈ o.divisors.filter (fun d => dfree q d ∣ D), d * Nat.gcd (q ^ o - 1) (D / dfree q d) ∧
      ∑ d ∈ o.divisors.filter (fun d => dfree q d ∣ D), d * Nat.gcd (q ^ o - 1) (D / dfree q d) ≤
        (∑ d ∈ o.divisors, d) * Nat.gcd (q ^ o - 1) D :=
  structure_c' hq hC₀ o D hD

end Model

/-- One lifting step: `p^β ∣ a - 1` (`β ≥ 1`) implies `p^{β+1} ∣ a^p - 1` (in `ℤ`). -/
lemma lift_step {p : ℕ} {β : ℕ} (hβ : 1 ≤ β) {a : ℤ} (h : (p : ℤ) ^ β ∣ a - 1) :
    (p : ℤ) ^ (β + 1) ∣ a ^ p - 1 := by
  have hp : (p : ℤ) ∣ a - 1 := (dvd_pow_self (p : ℤ) (by omega)).trans h
  -- `∑_{i<p} a^i ≡ p (mod p)`
  have hG : (p : ℤ) ∣ ∑ i ∈ range p, a ^ i := by
    have h1 : ∑ i ∈ range p, a ^ i = ∑ i ∈ range p, (a ^ i - 1) + p := by
      rw [Finset.sum_sub_distrib]; simp
    rw [h1]
    refine dvd_add (Finset.dvd_sum fun i _ => hp.trans (sub_one_dvd_pow_sub_one a i)) dvd_rfl
  rw [← geom_sum_mul, pow_succ, mul_comm]
  exact mul_dvd_mul hG h

lemma lift_pow {p : ℕ} {β : ℕ} (hβ : 1 ≤ β) {a : ℤ} (h : (p : ℤ) ^ β ∣ a - 1) (t : ℕ) :
    (p : ℤ) ^ (β + t) ∣ a ^ p ^ t - 1 := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    have := lift_step (by omega : 1 ≤ β + t) ih
    rw [← pow_mul, ← pow_succ] at this
    rwa [Nat.add_succ]

/-- The same statement for `ℕ` congruences. -/
lemma lift_pow_nat {p q m β : ℕ} (hβ : 1 ≤ β) (h : q ^ m ≡ 1 [MOD p ^ β]) (t : ℕ) :
    q ^ (m * p ^ t) ≡ 1 [MOD p ^ (β + t)] := by
  have hq1 : 1 ≤ q ^ m ∨ q ^ m = 0 := by omega
  rw [Nat.modEq_iff_dvd] at h ⊢
  have h' : ((p : ℤ)) ^ β ∣ (q : ℤ) ^ m - 1 := by
    have := h; push_cast at this ⊢
    exact (dvd_neg.mpr this) |> fun h2 => by simpa [neg_sub] using h2
  have := lift_pow hβ h' t
  push_cast
  rw [pow_mul]
  exact (dvd_neg.mpr this) |> fun h2 => by simpa [neg_sub] using h2

/-- `ord_{r^α}(q) ∣ ord_r(q) r^{α-1}`. -/
lemma ordMod_primePow_dvd {q r α : ℕ} (hα : 1 ≤ α) :
    ordMod q (r ^ α) ∣ ordMod q r * r ^ (α - 1) := by
  rw [ordMod_dvd_iff_modEq]
  have h := (ordMod_dvd_iff_modEq (q := q) (e := r) (k := ordMod q r)).mp dvd_rfl
  have h1 : q ^ ordMod q r ≡ 1 [MOD r ^ 1] := by rwa [pow_one]
  have := lift_pow_nat le_rfl h1 (α - 1)
  rwa [Nat.add_sub_cancel' hα] at this



lemma lcmUpTo_ne_zero (m : ℕ) : lcmUpTo m ≠ 0 := by
  unfold lcmUpTo
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

lemma dvd_lcmUpTo {j m : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ m) : j ∣ lcmUpTo m :=
  Finset.dvd_lcm (s := Icc 1 m) (f := id) (Finset.mem_Icc.mpr ⟨h1, h2⟩)

/-- A prime power dividing `lcm(1, …, m)` is at most `m`. -/
lemma primePow_le_of_dvd_lcmUpTo {r α m : ℕ} (hr : r.Prime) (hα : 1 ≤ α)
    (h : r ^ α ∣ lcmUpTo m) : r ^ α ≤ m := by
  have hne : ∀ k ∈ Icc 1 m, (id k : ℕ) ≠ 0 := fun k hk => by
    simp only [id]; exact (Nat.pos_of_ne_zero (by have := (Finset.mem_Icc.mp hk).1; omega)).ne'
  have hv : α ≤ (lcmUpTo m).factorization r := by
    rw [← hr.pow_dvd_iff_le_factorization (lcmUpTo_ne_zero m)]; exact h
  unfold lcmUpTo at hv
  rw [Finset.factorization_lcm hne] at hv
  obtain ⟨j, hj, hjv⟩ := (Finset.le_sup_iff (by rw [Nat.bot_eq_zero]; omega)).mp hv
  have hj0 : j ≠ 0 := hne j hj
  have : r ^ α ∣ j := (hr.pow_dvd_iff_le_factorization hj0).mpr hjv
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) this).trans (Finset.mem_Icc.mp hj).2

lemma prime_le_of_dvd_lcmUpTo {r m : ℕ} (hr : r.Prime) (h : r ∣ lcmUpTo m) : r ≤ m := by
  have := primePow_le_of_dvd_lcmUpTo hr le_rfl (by rwa [pow_one]); rwa [pow_one] at this

lemma ordMod_prime_dvd {q r : ℕ} (hr : r.Prime) (hq : Nat.Coprime q r) : ordMod q r ∣ r - 1 := by
  have : NeZero r := ⟨hr.ne_zero⟩
  rw [ordMod_eq_orderOf_unit hq, ← Nat.totient_prime hr, ← ZMod.card_units_eq_totient]
  exact orderOf_dvd_card

lemma ordMod_lt_primePow {q r α : ℕ} (hr : r.Prime) (hα : 1 ≤ α) (hq : Nat.Coprime q r) :
    ordMod q (r ^ α) < r ^ α := by
  have hq' : Nat.Coprime q (r ^ α) := Nat.Coprime.pow_right α hq
  have : NeZero (r ^ α) := ⟨pow_ne_zero _ hr.ne_zero⟩
  rw [ordMod_eq_orderOf_unit hq']
  calc orderOf (ZMod.unitOfCoprime q hq') ≤ Fintype.card (ZMod (r ^ α))ˣ := orderOf_le_card_univ
    _ = Nat.totient (r ^ α) := ZMod.card_units_eq_totient _
    _ < r ^ α := Nat.totient_lt _ (Nat.one_lt_pow (by omega) hr.one_lt)

/-- `ord_K(q) ∣ M` as soon as `q^M ≡ 1` modulo every prime power dividing `K`. -/
lemma ordMod_dvd_of_primePow {q K M : ℕ} (hq : 1 ≤ q) (hK : K ≠ 0)
    (h : ∀ r, r.Prime → r ∣ K → ordMod q (r ^ K.factorization r) ∣ M) : ordMod q K ∣ M := by
  have hq1 : 1 ≤ q ^ M := Nat.one_le_pow _ _ hq
  rw [ordMod_dvd_iff_modEq, Nat.ModEq.comm, Nat.modEq_iff_dvd' hq1]
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r k hr hrk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hrK : r ∣ K := (dvd_pow_self r hk.ne').trans hrk
  have hkv : k ≤ K.factorization r := (hr.pow_dvd_iff_le_factorization hK).mp hrk
  have := (ordMod_dvd_iff_modEq (q := q) (e := r ^ K.factorization r) (k := M)).mp (h r hr hrK)
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hq1] at this
  exact (Nat.pow_dvd_pow r hkv).trans this



lemma coprime_pfree_of_prime {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) : Nat.Coprime (pfree p j) p :=
  (coprime_pfree hp hj).symm

lemma pfree_eq_self_of_coprime {p j : ℕ} (hp : p.Prime) (h : Nat.Coprime j p) : pfree p j = j :=
  pfree_eq_self hp fun hd => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h.symm hd)

lemma pfree_lcm_dvd {p : ℕ} (hp : p.Prime) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    pfree p (Nat.lcm a b) ∣ Nat.lcm (pfree p a) (pfree p b) := by
  set x := a.factorization p
  set y := b.factorization p
  have hA : a = p ^ x * pfree p a := (pow_mul_pfree p a).symm
  have hB : b = p ^ y * pfree p b := (pow_mul_pfree p b).symm
  have h1 : Nat.lcm a b ∣ p ^ (x + y) * Nat.lcm (pfree p a) (pfree p b) := by
    refine Nat.lcm_dvd ?_ ?_
    · conv_lhs => rw [hA]
      exact mul_dvd_mul (pow_dvd_pow p (Nat.le_add_right x y)) (Nat.dvd_lcm_left _ _)
    · conv_lhs => rw [hB]
      exact mul_dvd_mul (pow_dvd_pow p (Nat.le_add_left y x)) (Nat.dvd_lcm_right _ _)
  have h2 := pfree_dvd_pfree h1 p
  rw [pfree_pow_mul hp] at h2
  have hc : Nat.Coprime (Nat.lcm (pfree p a) (pfree p b)) p :=
    Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _)
      (Nat.Coprime.mul_left (coprime_pfree_of_prime hp ha) (coprime_pfree_of_prime hp hb))
  rwa [pfree_eq_self_of_coprime hp hc] at h2

lemma coprime_of_prime_ne {q p r : ℕ} (hq : IsPrimePow q) (hp : charOf q = p) (hr : r.Prime)
    (hrp : r ≠ p) : Nat.Coprime q r := by
  have hpp : p.Prime := hp ▸ Nat.minFac_prime hq.ne_one
  rw [← hq.minFac_pow_factorization_eq]
  have : charOf q = q.minFac := rfl
  rw [← this, hp]
  exact Nat.Coprime.pow_left _ ((Nat.coprime_primes hpp hr).mpr hrp.symm)



section
variable {q : ℕ} (hq : IsPrimePow q)
include hq

lemma charOf_prime : (charOf q).Prime := Nat.minFac_prime hq.ne_one

lemma charOf_dvd_q : charOf q ∣ q := Nat.minFac_dvd q

lemma coprime_q_of_coprime_charOf {m : ℕ} (h : Nat.Coprime m (charOf q)) : Nat.Coprime q m := by
  rw [← hq.minFac_pow_factorization_eq]
  exact Nat.Coprime.pow_left _ h.symm

lemma coprime_pow_sub_one_charOf {o : ℕ} (ho : 1 ≤ o) : Nat.Coprime (q ^ o - 1) (charOf q) := by
  have hp := charOf_prime hq
  refine ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_).symm
  have h1 : charOf q ∣ q ^ o := (charOf_dvd_q hq).trans (dvd_pow_self q (by omega))
  have h2 : 1 ≤ q ^ o := Nat.one_le_pow _ _ hq.pos
  have : charOf q ∣ q ^ o - (q ^ o - 1) := Nat.dvd_sub h1 hd
  rw [Nat.sub_sub_self h2] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

lemma Kzero_ne_zero {o₀ : ℕ} (ho₀ : 1 ≤ o₀) : Kzero q o₀ ≠ 0 := by
  unfold Kzero
  have h1 : 1 < q ^ o₀ := Nat.one_lt_pow (by omega) hq.one_lt
  exact Nat.mul_ne_zero (pfree_ne_zero _ (by omega)) (by omega)

lemma coprime_Kzero {o₀ : ℕ} (ho₀ : 1 ≤ o₀) : Nat.Coprime (Kzero q o₀) (charOf q) :=
  Nat.Coprime.mul_left (coprime_pfree_of_prime (charOf_prime hq) (by omega))
    (coprime_pow_sub_one_charOf hq ho₀)

lemma coprime_Lzero (o₀ : ℕ) : Nat.Coprime (Lzero q o₀) (charOf q) :=
  coprime_pfree_of_prime (charOf_prime hq) (lcmUpTo_ne_zero o₀)

lemma Kcrude_ne_zero {o₀ : ℕ} (ho₀ : 1 ≤ o₀) : Kcrude q o₀ ≠ 0 :=
  Nat.lcm_ne_zero (Kzero_ne_zero hq ho₀) (pfree_ne_zero _ (lcmUpTo_ne_zero o₀))

lemma coprime_Kcrude {o₀ : ℕ} (ho₀ : 1 ≤ o₀) : Nat.Coprime (Kcrude q o₀) (charOf q) :=
  Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _)
    (Nat.Coprime.mul_left (coprime_Kzero hq ho₀) (coprime_Lzero hq o₀))

/-- Primes dividing the crude `K` are different from `p`, and divide `q^{o₀} - 1` or are `≤ o₀`. -/
lemma prime_dvd_Kcrude {o₀ : ℕ} (ho₀ : 1 ≤ o₀) {r : ℕ} (hr : r.Prime) (hrK : r ∣ Kcrude q o₀) :
    Nat.Coprime q r ∧ (r ∣ q ^ o₀ - 1 ∨ r ≤ o₀) := by
  have hcop : Nat.Coprime r (charOf q) :=
    Nat.Coprime.coprime_dvd_left hrK (coprime_Kcrude hq ho₀)
  refine ⟨coprime_q_of_coprime_charOf hq hcop, ?_⟩
  have := (Nat.Prime.dvd_mul hr).mp (hrK.trans (Nat.lcm_dvd_mul _ _))
  rcases this with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h' | h'
    · right
      exact (Nat.le_of_dvd (by omega) ((h'.trans (pfree_dvd _ _))))
    · left; exact h'
  · right
    exact prime_le_of_dvd_lcmUpTo hr (h.trans (pfree_dvd _ _))

lemma ordMod_prime_dvd_lcmUpTo {o₀ : ℕ} (ho₀ : 1 ≤ o₀) {r : ℕ} (hr : r.Prime)
    (hrK : r ∣ Kcrude q o₀) : ordMod q r ∣ lcmUpTo o₀ := by
  obtain ⟨hcop, h⟩ := prime_dvd_Kcrude hq ho₀ hr hrK
  rcases h with h | h
  · have : ordMod q r ∣ o₀ := by
      rw [ordMod_dvd_iff_modEq, Nat.ModEq.comm, Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)]
      exact h
    exact this.trans (dvd_lcmUpTo ho₀ le_rfl)
  · have hpos : 0 < ordMod q r := ordMod_pos hcop hr.ne_zero
    have hle : ordMod q r ≤ r - 1 := Nat.le_of_dvd (by have := hr.two_le; omega)
      (ordMod_prime_dvd hr hcop)
    exact dvd_lcmUpTo hpos (by omega)

/-- **Lemma 7.4**. -/
theorem Kcrude_spec' {o₀ : ℕ} (ho₀ : 1 ≤ o₀) :
    pfree (charOf q) (ordMod q (Kcrude q o₀)) ∣ Kcrude q o₀ ∧
      ordMod q (Kcrude q o₀) ∣ Lambda q o₀ := by
  have hp := charOf_prime hq
  have hK0 := Kcrude_ne_zero hq ho₀
  have hq1 : 1 ≤ q := hq.pos
  constructor
  · -- `ord_K(q) ∣ lcm(lcm(1..o₀), K)`
    have h1 : ordMod q (Kcrude q o₀) ∣ Nat.lcm (lcmUpTo o₀) (Kcrude q o₀) := by
      refine ordMod_dvd_of_primePow hq1 hK0 fun r hr hrK => ?_
      set α := (Kcrude q o₀).factorization r
      have hα : 1 ≤ α := (hr.dvd_iff_one_le_factorization hK0).mp hrK
      refine (ordMod_primePow_dvd hα).trans ?_
      have hcop : Nat.Coprime (ordMod q r) (r ^ (α - 1)) := by
        refine Nat.Coprime.pow_right _ ?_
        refine Nat.Coprime.coprime_dvd_left (ordMod_prime_dvd hr (prime_dvd_Kcrude hq ho₀ hr hrK).1) ?_
        obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by have := hr.two_le; omega⟩
        rw [hs, Nat.add_sub_cancel]
        simp [Nat.coprime_self_add_right]
      rw [← hcop.lcm_eq_mul]
      exact Nat.lcm_dvd ((ordMod_prime_dvd_lcmUpTo hq ho₀ hr hrK).trans (Nat.dvd_lcm_left _ _))
        ((Nat.pow_dvd_pow r (Nat.sub_le α 1)).trans
          ((Nat.ordProj_dvd _ _).trans (Nat.dvd_lcm_right _ _)))
    have h2 := pfree_dvd_pfree h1 (charOf q)
    have h3 := h2.trans (pfree_lcm_dvd hp (lcmUpTo_ne_zero o₀) hK0)
    rw [pfree_eq_self_of_coprime hp (coprime_Kcrude hq ho₀)] at h3
    have hL : Nat.lcm (pfree (charOf q) (lcmUpTo o₀)) (Kcrude q o₀) = Kcrude q o₀ :=
      Nat.lcm_eq_right (Nat.dvd_lcm_right _ _)
    rwa [hL] at h3
  · refine ordMod_dvd_of_primePow hq1 hK0 fun r hr hrK => ?_
    obtain ⟨hcop, -⟩ := prime_dvd_Kcrude hq ho₀ hr hrK
    set α := (Kcrude q o₀).factorization r with hαdef
    have hα : 1 ≤ α := (hr.dvd_iff_one_le_factorization hK0).mp hrK
    have hKz := Kzero_ne_zero hq ho₀
    have hLz : Lzero q o₀ ≠ 0 := pfree_ne_zero _ (lcmUpTo_ne_zero o₀)
    have hαeq : α = max ((Kzero q o₀).factorization r) ((Lzero q o₀).factorization r) := by
      rw [hαdef, Kcrude, Nat.factorization_lcm hKz hLz]; rfl
    have hLam : lcmUpTo o₀ ∣ Lambda q o₀ := Dvd.intro_left _ rfl
    by_cases hcase : α ≤ (Lzero q o₀).factorization r
    · -- `r^α ∣ lcm(1..o₀)`, hence `r^α ≤ o₀`
      have hdvd : r ^ α ∣ lcmUpTo o₀ :=
        ((hr.pow_dvd_iff_le_factorization hLz).mpr hcase).trans (pfree_dvd _ _)
      have hle := primePow_le_of_dvd_lcmUpTo hr hα hdvd
      have hlt := ordMod_lt_primePow hr hα hcop
      have hpos : 0 < ordMod q (r ^ α) :=
        ordMod_pos (Nat.Coprime.pow_right _ hcop) (pow_ne_zero _ hr.ne_zero)
      exact (dvd_lcmUpTo hpos (by omega)).trans hLam
    · push Not at hcase
      have hαK : α = (Kzero q o₀).factorization r := by
        rw [hαeq] at hcase ⊢; exact max_eq_left_iff.mpr (by omega) |> fun _ => by omega
      have hq1' : 1 < q ^ o₀ := Nat.one_lt_pow (by omega) hq.one_lt
      have hfac : (Kzero q o₀).factorization r =
          (pfree (charOf q) o₀).factorization r + (q ^ o₀ - 1).factorization r := by
        unfold Kzero
        rw [Nat.factorization_mul (pfree_ne_zero _ (by omega)) (by omega)]; rfl
      set t := (pfree (charOf q) o₀).factorization r
      set β := (q ^ o₀ - 1).factorization r
      have hβ : 1 ≤ β := by
        by_contra hβ0
        push Not at hβ0
        have hβ0' : β = 0 := by omega
        have ht : t ≤ (Lzero q o₀).factorization r :=
          (Nat.factorization_le_iff_dvd (pfree_ne_zero _ (by omega)) hLz).mpr
            (pfree_dvd_pfree (dvd_lcmUpTo ho₀ le_rfl) _) r
        omega
      have hmod : q ^ o₀ ≡ 1 [MOD r ^ β] := by
        rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by omega)]
        exact Nat.ordProj_dvd _ _
      have hlift := lift_pow_nat hβ hmod t
      have hαβ : β + t = α := by rw [hαK, hfac]; ring
      rw [hαβ] at hlift
      have h1 : ordMod q (r ^ α) ∣ o₀ * r ^ t := ordMod_dvd_iff_modEq.mpr hlift
      refine h1.trans ?_
      unfold Lambda
      rw [mul_comm]
      exact mul_dvd_mul (Nat.ordProj_dvd _ _) (dvd_lcmUpTo ho₀ le_rfl)

end



lemma Dseq_coprime (q o₀ : ℕ) (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) (i : ℕ) :
    Dseq q o₀ i ≠ 0 ∧ Nat.Coprime (Dseq q o₀ i) (charOf q) := by
  have hp := charOf_prime hq
  induction i with
  | zero =>
    have hO : Ozero q o₀ ≠ 0 := by
      unfold Ozero
      refine Nat.lcm_ne_zero (by omega) ?_
      rw [Ne, Finset.lcm_eq_zero_iff]
      push Not
      intro ℓ hℓ
      have hℓp : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
      have hcop : Nat.Coprime q ℓ := coprime_q_of_coprime_charOf hq
        (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hℓ)
          (coprime_pfree_of_prime hp (by omega)))
      exact (ordMod_pos (Nat.Coprime.pow_right _ hcop) (pow_ne_zero _ hℓp.ne_zero)).ne'
    exact ⟨pfree_ne_zero _ hO, coprime_pfree_of_prime hp hO⟩
  | succ i ih =>
    obtain ⟨h0, hc⟩ := ih
    have hord : ordMod q (Dseq q o₀ i) ≠ 0 :=
      (ordMod_pos (coprime_q_of_coprime_charOf hq hc) h0).ne'
    refine ⟨Nat.lcm_ne_zero h0 (pfree_ne_zero _ hord), ?_⟩
    exact Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _)
      (Nat.Coprime.mul_left hc (coprime_pfree_of_prime hp hord))

theorem Kzero_spec' (q n : ℕ) [NeZero n] (hq : IsPrimePow q) {C₀ : Model.Cond q n}
    (hC₀ : C₀ ∈ Model.essConds q n) :
    Model.dfree q C₀.1 * Model.tord q n C₀ ∣ Kzero q (Model.codim q n C₀) ∧
      Nat.Coprime (Kcrude q (Model.codim q n C₀)) (charOf q) ∧
      Nat.Coprime (Kclosure q (Model.codim q n C₀)) (charOf q) := by
  have ho : 1 ≤ Model.codim q n C₀ := Model.one_le_codim hq (Model.essConds_subset hC₀)
  refine ⟨?_, coprime_Kcrude hq ho, ?_⟩
  · obtain ⟨d, hd, x, hx, hess, rfl⟩ := (Model.mem_essConds_iff hq).mp hC₀
    rw [Model.codim_orbit hq, Model.tord_orbit hq]
    unfold Kzero
    refine mul_dvd_mul (pfree_dvd_pfree hess _) ?_
    have h := (ordMod_dvd_iff_modEq (q := q) (e := addOrderOf x) (k := Model.tcodim q n x)).mp dvd_rfl
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)] at h
    exact h
  · unfold Kclosure Dinf
    have hD := Dseq_coprime q _ hq ho (closureSteps (Dseq q (Model.codim q n C₀) 0))
    exact Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _)
      (Nat.Coprime.mul_left (coprime_Kzero hq ho) hD.2)


/-- **Lemma 7.4**: for the crude choice (A), `(ord_K(q))_{p'} ∣ K` and
`ord_K(q) ∣ o₀' lcm(1, …, o₀)`. -/
theorem Kcrude_spec (q o₀ : ℕ) (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    pfree (charOf q) (ordMod q (Kcrude q o₀)) ∣ Kcrude q o₀ ∧
      ordMod q (Kcrude q o₀) ∣ Lambda q o₀ :=
  Kcrude_spec' hq ho₀

/-! ### Lemma 7.5 and the closure (B) -/

/-- `ord_D(q) ∣ B` when `D ∣ B` and `r - 1 ∣ B` for every prime `r ∣ B`. -/
lemma ordMod_dvd_of_closed {q B D : ℕ} (hq : 1 ≤ q) (hB : ∀ r, r.Prime → r ∣ B → r - 1 ∣ B)
    (hD0 : D ≠ 0) (hDB : D ∣ B) (hcop : Nat.Coprime q D) : ordMod q D ∣ B := by
  refine ordMod_dvd_of_primePow hq hD0 fun r hr hrD => ?_
  set α := D.factorization r
  have hα : 1 ≤ α := (hr.dvd_iff_one_le_factorization hD0).mp hrD
  have hqr : Nat.Coprime q r := Nat.Coprime.coprime_dvd_right hrD hcop
  refine (ordMod_primePow_dvd hα).trans ?_
  have hcop' : Nat.Coprime (r - 1) (r ^ (α - 1)) := by
    refine Nat.Coprime.pow_right _ ?_
    obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by have := hr.two_le; omega⟩
    rw [hs, Nat.add_sub_cancel]
    simp [Nat.coprime_self_add_right]
  refine (Nat.mul_dvd_mul_right (ordMod_prime_dvd hr hqr) _).trans ?_
  rw [← hcop'.lcm_eq_mul]
  exact Nat.lcm_dvd (hB r hr (hrD.trans hDB))
    ((Nat.pow_dvd_pow r (Nat.sub_le α 1)).trans ((Nat.ordProj_dvd _ _).trans hDB))

lemma ordMod_dvd_totient_of_coprime {q m : ℕ} (hm : m ≠ 0) (hc : Nat.Coprime q m) :
    ordMod q m ∣ Nat.totient m := by
  have : NeZero m := ⟨hm⟩
  rw [ordMod_eq_orderOf_unit hc, ← ZMod.card_units_eq_totient]
  exact orderOf_dvd_card

lemma ordMod_lcm_dvd {q a b : ℕ} (hq : 1 ≤ q) :
    ordMod q (Nat.lcm a b) ∣ Nat.lcm (ordMod q a) (ordMod q b) := by
  have h1 : 1 ≤ q ^ Nat.lcm (ordMod q a) (ordMod q b) := Nat.one_le_pow _ _ hq
  have ha : ordMod q a ∣ Nat.lcm (ordMod q a) (ordMod q b) := Nat.dvd_lcm_left _ _
  have hb : ordMod q b ∣ Nat.lcm (ordMod q a) (ordMod q b) := Nat.dvd_lcm_right _ _
  rw [ordMod_dvd_iff_modEq, Nat.ModEq.comm, Nat.modEq_iff_dvd' h1] at ha hb ⊢
  exact Nat.lcm_dvd ha hb

lemma two_mul_le_of_dvd_ne {a b : ℕ} (h : a ∣ b) (hb : b ≠ 0) (hne : b ≠ a) : 2 * a ≤ b := by
  obtain ⟨k, rfl⟩ := h
  have hk0 : k ≠ 0 := by rintro rfl; simp at hb
  have hk1 : k ≠ 1 := by rintro rfl; simp at hne
  have : 2 ≤ k := by omega
  calc 2 * a = a * 2 := mul_comm _ _
    _ ≤ a * k := Nat.mul_le_mul_left a this

section ClosureLemmas

variable (q o₀ : ℕ)

lemma Dseq_succ (i : ℕ) :
    Dseq q o₀ (i + 1) = Nat.lcm (Dseq q o₀ i) (pfree (charOf q) (ordMod q (Dseq q o₀ i))) := rfl

lemma Dseq_zero : Dseq q o₀ 0 = pfree (charOf q) (Ozero q o₀) := rfl

lemma Dseq_dvd_succ (i : ℕ) : Dseq q o₀ i ∣ Dseq q o₀ (i + 1) := Nat.dvd_lcm_left _ _

lemma Dseq_mono {i j : ℕ} (h : i ≤ j) : Dseq q o₀ i ∣ Dseq q o₀ j := by
  induction h with
  | refl => exact dvd_rfl
  | step _ ih => exact ih.trans (Dseq_dvd_succ q o₀ _)

variable {q o₀} in
lemma Dseq_stable {i : ℕ} (h : Dseq q o₀ (i + 1) = Dseq q o₀ i) :
    ∀ j, i ≤ j → Dseq q o₀ j = Dseq q o₀ i := by
  intro j hj
  induction hj with
  | refl => rfl
  | step _ ih => rw [Dseq_succ, ih, ← Dseq_succ, h]

lemma Kzero_factorization (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) (ℓ : ℕ) :
    (Kzero q o₀).factorization ℓ =
      (pfree (charOf q) o₀).factorization ℓ + (q ^ o₀ - 1).factorization ℓ := by
  have hq1 : 1 < q ^ o₀ := Nat.one_lt_pow (by omega) hq.one_lt
  unfold Kzero
  rw [Nat.factorization_mul (pfree_ne_zero _ (by omega)) (by omega)]; rfl

lemma Ozero_ne_zero (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) : Ozero q o₀ ≠ 0 := by
  have hp := charOf_prime hq
  unfold Ozero
  refine Nat.lcm_ne_zero (by omega) ?_
  rw [Ne, Finset.lcm_eq_zero_iff]
  push Not
  intro ℓ hℓ
  have hℓp : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hcop : Nat.Coprime q ℓ := coprime_q_of_coprime_charOf hq
    (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hℓ)
      (coprime_pfree_of_prime hp (by omega)))
  exact (ordMod_pos (Nat.Coprime.pow_right _ hcop) (pow_ne_zero _ hℓp.ne_zero)).ne'

/-- `O₀ ∣ o₀ o₀' φ(o₀')`. -/
lemma Ozero_dvd (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    Ozero q o₀ ∣ o₀ * pfree (charOf q) o₀ * Nat.totient (pfree (charOf q) o₀) := by
  set o' := pfree (charOf q) o₀ with ho'def
  have ho' : o' ≠ 0 := pfree_ne_zero _ (by omega)
  have hco' : Nat.Coprime q o' := coprime_q_of_coprime_charOf hq
    (coprime_pfree_of_prime (charOf_prime hq) (by omega))
  unfold Ozero
  refine Nat.lcm_dvd (Dvd.dvd.mul_right (dvd_mul_right o₀ o') _) (Finset.lcm_dvd fun ℓ hℓ => ?_)
  rcases Nat.eq_zero_or_pos ((q ^ o₀ - 1).factorization ℓ) with hβ | hβ
  · rw [hβ, add_zero]
    have h1 : ℓ ^ o'.factorization ℓ ∣ o' := Nat.ordProj_dvd _ _
    exact (ordMod_dvd_ordMod h1).trans
      ((ordMod_dvd_totient_of_coprime ho' hco').trans (dvd_mul_left _ _))
  · have hmod : q ^ o₀ ≡ 1 [MOD ℓ ^ (q ^ o₀ - 1).factorization ℓ] := by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)]
      exact Nat.ordProj_dvd _ _
    have hlift := lift_pow_nat hβ hmod (o'.factorization ℓ)
    rw [add_comm] at hlift
    have h1 : ordMod q (ℓ ^ (o'.factorization ℓ + (q ^ o₀ - 1).factorization ℓ)) ∣
        o₀ * ℓ ^ o'.factorization ℓ := ordMod_dvd_iff_modEq.mpr hlift
    exact h1.trans (Dvd.dvd.mul_right (mul_dvd_mul_left o₀ (Nat.ordProj_dvd _ _)) _)

lemma Dzero_le (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) : Dseq q o₀ 0 ≤ o₀ ^ 3 := by
  have h : Dseq q o₀ 0 ∣ o₀ * pfree (charOf q) o₀ * Nat.totient (pfree (charOf q) o₀) :=
    (pfree_dvd (charOf q) (Ozero q o₀)).trans (Ozero_dvd q o₀ hq ho₀)
  set o' := pfree (charOf q) o₀
  have ho'pos : 0 < o' := pfree_pos _ (by omega)
  have ho'le : o' ≤ o₀ := Nat.le_of_dvd (by omega) (pfree_dvd _ _)
  have htot : Nat.totient o' ≤ o' := Nat.totient_le _
  have htpos : 0 < Nat.totient o' := Nat.totient_pos.mpr ho'pos
  calc Dseq q o₀ 0 ≤ o₀ * o' * Nat.totient o' := Nat.le_of_dvd (by positivity) h
    _ ≤ o₀ * o₀ * o₀ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl ho'le) (htot.trans ho'le)
    _ = o₀ ^ 3 := by ring

lemma Dseq_dvd_prattBound (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) (i : ℕ) :
    Dseq q o₀ i ∣ prattBound (Dseq q o₀ 0) := by
  have hD0 := (Dseq_coprime q o₀ hq ho₀ 0).1
  induction i with
  | zero => exact dvd_prattBound _
  | succ i ih =>
    rw [Dseq_succ]
    refine Nat.lcm_dvd ih ((pfree_dvd _ _).trans ?_)
    obtain ⟨h0, hc⟩ := Dseq_coprime q o₀ hq ho₀ i
    exact ordMod_dvd_of_closed hq.pos (fun r hr hrB => prattBound_closed hD0 hr hrB) h0 ih
      (coprime_q_of_coprime_charOf hq hc)

/-- **Lemma 7.5**, explicit form. -/
theorem closure_bound' (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    Dseq q o₀ 0 ≤ o₀ ^ 3 ∧ ∃ P : ℕ, 2 ^ P ≤ Dseq q o₀ 0 ^ 2 ∧
      ∀ i, Dseq q o₀ i ≤ Dseq q o₀ 0 ^ (P + 1) := by
  have hD0 := (Dseq_coprime q o₀ hq ho₀ 0).1
  refine ⟨Dzero_le q o₀ hq ho₀, (prattSet (Dseq q o₀ 0)).card, two_pow_card_prattSet_le hD0,
    fun i => ?_⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (prattBound_ne_zero hD0))
    (Dseq_dvd_prattBound q o₀ hq ho₀ i)).trans (prattBound_le hD0)

theorem closure_size' (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    Dseq q o₀ 0 ≤ o₀ ^ 3 ∧
      ∀ i, Real.logb 2 (Dseq q o₀ i) ≤
        Real.logb 2 (Dseq q o₀ 0) + 2 * Real.logb 2 (Dseq q o₀ 0) ^ 2 := by
  obtain ⟨h1, P, hP, hD⟩ := closure_bound' q o₀ hq ho₀
  refine ⟨h1, fun i => ?_⟩
  have hD0 : (1 : ℝ) ≤ (Dseq q o₀ 0 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Dseq_coprime q o₀ hq ho₀ 0).1
  have hDi : (0 : ℝ) < (Dseq q o₀ i : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Dseq_coprime q o₀ hq ho₀ i).1
  have hL : 0 ≤ Real.logb 2 (Dseq q o₀ 0 : ℝ) := Real.logb_nonneg (by norm_num) hD0
  have h1 : Real.logb 2 (Dseq q o₀ i : ℝ) ≤ Real.logb 2 ((Dseq q o₀ 0 : ℝ) ^ (P + 1)) :=
    Real.logb_le_logb_of_le (by norm_num) hDi (by exact_mod_cast hD i)
  rw [Real.logb_pow] at h1
  push_cast at h1
  have h2 : Real.logb 2 ((2 : ℝ) ^ P) ≤ Real.logb 2 ((Dseq q o₀ 0 : ℝ) ^ 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast hP)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  push_cast at h2
  nlinarith [mul_nonneg (sub_nonneg.mpr (show (P : ℝ) * 1 ≤ 2 * Real.logb 2 (Dseq q o₀ 0) from h2)) hL]

/-- Some step of the closure sequence before `closureSteps D₀` is stationary. -/
lemma Dseq_exists_stable (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    ∃ i < closureSteps (Dseq q o₀ 0), Dseq q o₀ (i + 1) = Dseq q o₀ i := by
  by_contra hcon
  push Not at hcon
  set S := closureSteps (Dseq q o₀ 0) with hSdef
  set D₀ := Dseq q o₀ 0 with hD₀def
  have hD0 : D₀ ≠ 0 := (Dseq_coprime q o₀ hq ho₀ 0).1
  have hgrow : ∀ i ≤ S, 2 ^ i * D₀ ≤ Dseq q o₀ i := by
    intro i
    induction i with
    | zero => intro _; simp [D₀]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := two_mul_le_of_dvd_ne (Dseq_dvd_succ q o₀ i) (Dseq_coprime q o₀ hq ho₀ (i + 1)).1
        (hcon i (by omega))
      calc 2 ^ (i + 1) * D₀ = 2 * (2 ^ i * D₀) := by ring
        _ ≤ 2 * Dseq q o₀ i := Nat.mul_le_mul_left 2 h1
        _ ≤ _ := h2
  obtain ⟨-, P, hP, hbound⟩ := closure_bound' q o₀ hq ho₀
  have h1 : 2 ^ S * D₀ ≤ D₀ ^ P * D₀ := by
    rw [← pow_succ]; exact (hgrow S le_rfl).trans (hbound S)
  have h2 : 2 ^ S ≤ D₀ ^ P := Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_ne_zero hD0)
  set N := Nat.log 2 D₀ with hN
  have hND : D₀ < 2 ^ (N + 1) := Nat.lt_pow_succ_log_self (by norm_num) D₀
  have h3 : D₀ ^ P ≤ 2 ^ ((N + 1) * P) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hND.le P
  have h4 : S ≤ (N + 1) * P := (Nat.pow_le_pow_iff_right (by norm_num)).mp (h2.trans h3)
  have h5 : 2 ^ P < 2 ^ (2 * (N + 1)) := by
    calc 2 ^ P ≤ D₀ ^ 2 := hP
      _ < (2 ^ (N + 1)) ^ 2 := Nat.pow_lt_pow_left hND (by norm_num)
      _ = 2 ^ (2 * (N + 1)) := by rw [← pow_mul, mul_comm]
  have h6 : P < 2 * (N + 1) := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h5
  have hS : S = 2 * (N + 1) ^ 2 + 1 := rfl
  have h7 : (N + 1) * P ≤ (N + 1) * (2 * N + 1) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

lemma ordMod_Kzero_dvd_Ozero (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    ordMod q (Kzero q o₀) ∣ Ozero q o₀ := by
  have hK0 := Kzero_ne_zero hq ho₀
  refine ordMod_dvd_of_primePow hq.pos hK0 fun ℓ hℓ hℓK => ?_
  have ho' : pfree (charOf q) o₀ ≠ 0 := pfree_ne_zero _ (by omega)
  have hq1 : 1 < q ^ o₀ := Nat.one_lt_pow (by omega) hq.one_lt
  rw [Kzero_factorization q o₀ hq ho₀]
  by_cases hℓo : ℓ ∣ pfree (charOf q) o₀
  · have hmem : ℓ ∈ (pfree (charOf q) o₀).primeFactors := Nat.mem_primeFactors.mpr ⟨hℓ, hℓo, ho'⟩
    unfold Ozero
    exact (Finset.dvd_lcm (f := fun ℓ => ordMod q (ℓ ^ ((pfree (charOf q) o₀).factorization ℓ +
      (q ^ o₀ - 1).factorization ℓ))) hmem).trans (Nat.dvd_lcm_right _ _)
  · rw [Nat.factorization_eq_zero_of_not_dvd hℓo, zero_add]
    have h1 : q ^ o₀ ≡ 1 [MOD ℓ ^ (q ^ o₀ - 1).factorization ℓ] := by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by omega)]; exact Nat.ordProj_dvd _ _
    exact (ordMod_dvd_iff_modEq.mpr h1).trans (by unfold Ozero; exact Nat.dvd_lcm_left _ _)

lemma Oinf_ne_zero (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) : Oinf q o₀ ≠ 0 :=
  Nat.lcm_ne_zero (Ozero_ne_zero q o₀ hq ho₀)
    (ordMod_pos (coprime_q_of_coprime_charOf hq (Dseq_coprime q o₀ hq ho₀ _).2)
      (Dseq_coprime q o₀ hq ho₀ _).1).ne'

theorem Kclosure_spec' (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    (∀ i, closureSteps (Dseq q o₀ 0) ≤ i → Dseq q o₀ i = Dinf q o₀) ∧
    pfree (charOf q) (ordMod q (Kclosure q o₀)) ∣ Kclosure q o₀ ∧
    pfree (charOf q) (ordMod q (Kclosure q o₀)) ∣ Dinf q o₀ ∧
    ordMod q (Kclosure q o₀) ∣ Oinf q o₀ := by
  have hp := charOf_prime hq
  have hstab : ∀ i, closureSteps (Dseq q o₀ 0) ≤ i → Dseq q o₀ i = Dinf q o₀ := by
    obtain ⟨i₀, hi₀, hst⟩ := Dseq_exists_stable q o₀ hq ho₀
    intro i hi
    rw [Dinf, Dseq_stable hst i (by omega), Dseq_stable hst _ hi₀.le]
  have hfix : pfree (charOf q) (ordMod q (Dinf q o₀)) ∣ Dinf q o₀ := by
    have h := hstab (closureSteps (Dseq q o₀ 0) + 1) (by omega)
    rw [Dseq_succ] at h
    calc pfree (charOf q) (ordMod q (Dinf q o₀))
        ∣ Nat.lcm (Dinf q o₀) (pfree (charOf q) (ordMod q (Dinf q o₀))) := Nat.dvd_lcm_right _ _
      _ = Dinf q o₀ := h
  have hDinf0 : Dinf q o₀ ≠ 0 := (Dseq_coprime q o₀ hq ho₀ _).1
  have hO0 := Ozero_ne_zero q o₀ hq ho₀
  have hoD : ordMod q (Dinf q o₀) ≠ 0 :=
    (ordMod_pos (coprime_q_of_coprime_charOf hq (Dseq_coprime q o₀ hq ho₀ _).2) hDinf0).ne'
  have h4 : ordMod q (Kclosure q o₀) ∣ Oinf q o₀ :=
    (ordMod_lcm_dvd hq.pos).trans (Nat.lcm_dvd
      ((ordMod_Kzero_dvd_Ozero q o₀ hq ho₀).trans (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _))
  have h3 : pfree (charOf q) (ordMod q (Kclosure q o₀)) ∣ Dinf q o₀ := by
    refine (pfree_dvd_pfree h4 _).trans ((pfree_lcm_dvd hp hO0 hoD).trans (Nat.lcm_dvd ?_ hfix))
    exact Dseq_mono q o₀ (Nat.zero_le (closureSteps (Dseq q o₀ 0)))
  exact ⟨hstab, h3.trans (Nat.dvd_lcm_right _ _), h3, h4⟩

theorem closure_cert' (Ohat Dhat M : ℕ) (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀)
    (h1 : o₀ ∣ Ohat) (h2 : q ^ Ohat ≡ 1 [MOD Kzero q o₀]) (h3 : pfree (charOf q) Ohat ∣ Dhat)
    (h4 : q ^ M ≡ 1 [MOD Dhat]) (h5 : pfree (charOf q) M ∣ Dhat) (h6 : M ∣ Ohat) :
    (∀ i, Dseq q o₀ i ∣ Dhat) ∧ Dinf q o₀ ∣ Dhat ∧ Oinf q o₀ ∣ Ohat ∧
      Nstarstar q o₀ ∣ Nat.lcm (Nat.lcm (Kzero q o₀) Dhat) Ohat := by
  have hO : Ozero q o₀ ∣ Ohat := by
    unfold Ozero
    refine Nat.lcm_dvd h1 (Finset.lcm_dvd fun ℓ _ => ?_)
    have hv : ℓ ^ ((pfree (charOf q) o₀).factorization ℓ + (q ^ o₀ - 1).factorization ℓ) ∣
        Kzero q o₀ := by
      rw [← Kzero_factorization q o₀ hq ho₀ ℓ]; exact Nat.ordProj_dvd _ _
    exact (ordMod_dvd_ordMod hv).trans (ordMod_dvd_iff_modEq.mpr h2)
  have hD : ∀ i, Dseq q o₀ i ∣ Dhat := by
    intro i
    induction i with
    | zero => exact (pfree_dvd_pfree hO _).trans h3
    | succ i ih =>
      rw [Dseq_succ]
      exact Nat.lcm_dvd ih ((pfree_dvd_pfree ((ordMod_dvd_ordMod ih).trans
        (ordMod_dvd_iff_modEq.mpr h4)) _).trans h5)
  have hOinf : Oinf q o₀ ∣ Ohat :=
    Nat.lcm_dvd hO (((ordMod_dvd_ordMod (hD _)).trans (ordMod_dvd_iff_modEq.mpr h4)).trans h6)
  refine ⟨hD, hD _, hOinf, ?_⟩
  unfold Nstarstar Kclosure
  exact Nat.lcm_dvd (Nat.lcm_dvd ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
    ((hD _).trans ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _))))
    (hOinf.trans (Nat.dvd_lcm_right _ _))

end ClosureLemmas

/-- The closure (B): the sequence `D_i` is stable from `closureSteps D₀` on, `K = lcm(K₀, D_∞)`
satisfies (ii), `(ord_K(q))_{p'} ∣ D_∞` and `ord_K(q) ∣ O_∞`. -/
theorem Kclosure_spec (q o₀ : ℕ) (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    (∀ i, closureSteps (Dseq q o₀ 0) ≤ i → Dseq q o₀ i = Dinf q o₀) ∧
    pfree (charOf q) (ordMod q (Kclosure q o₀)) ∣ Kclosure q o₀ ∧
    pfree (charOf q) (ordMod q (Kclosure q o₀)) ∣ Dinf q o₀ ∧
    ordMod q (Kclosure q o₀) ∣ Oinf q o₀ := by
  exact Kclosure_spec' q o₀ hq ho₀

/-- **Certificate for the closure (B)**: explicit multiples `D̂` of `D_∞` and `Ô` of `O_∞`
(and hence a multiple of `N**`), checkable by modular exponentiation only. -/
theorem closure_cert (q o₀ Ohat Dhat M : ℕ) (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀)
    (h1 : o₀ ∣ Ohat) (h2 : q ^ Ohat ≡ 1 [MOD Kzero q o₀]) (h3 : pfree (charOf q) Ohat ∣ Dhat)
    (h4 : q ^ M ≡ 1 [MOD Dhat]) (h5 : pfree (charOf q) M ∣ Dhat) (h6 : M ∣ Ohat) :
    (∀ i, Dseq q o₀ i ∣ Dhat) ∧ Dinf q o₀ ∣ Dhat ∧ Oinf q o₀ ∣ Ohat ∧
      Nstarstar q o₀ ∣ Nat.lcm (Nat.lcm (Kzero q o₀) Dhat) Ohat := by
  exact closure_cert' q o₀ Ohat Dhat M hq ho₀ h1 h2 h3 h4 h5 h6

/-- **Lemma 7.5**, explicit form: `D₀ ≤ o₀³`, and with `P` the size of the Pratt closure of the
primes of `D₀`, `2^P ≤ D₀²` and every `D_i ≤ D₀^{P+1}`. -/
theorem closure_bound (q o₀ : ℕ) (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    Dseq q o₀ 0 ≤ o₀ ^ 3 ∧ ∃ P : ℕ, 2 ^ P ≤ Dseq q o₀ 0 ^ 2 ∧
      ∀ i, Dseq q o₀ i ≤ Dseq q o₀ 0 ^ (P + 1) := by
  exact closure_bound' q o₀ hq ho₀

/-- **Lemma 7.5** (size of the closure): `D₀ ≤ o₀³` and
`log₂ D_i ≤ log₂ D₀ + 2 (log₂ D₀)²` for every `i` (hence for `D_∞`). -/
theorem closure_size (q o₀ : ℕ) (hq : IsPrimePow q) (ho₀ : 1 ≤ o₀) :
    Dseq q o₀ 0 ≤ o₀ ^ 3 ∧
      ∀ i, Real.logb 2 (Dseq q o₀ i) ≤
        Real.logb 2 (Dseq q o₀ 0) + 2 * Real.logb 2 (Dseq q o₀ 0) ^ 2 := by
  exact closure_size' q o₀ hq ho₀

/-- Both admissible `K` satisfy (i) for every essential condition `C₀` of codimension `o₀`:
`d₀' e₀ ∣ K₀`, and they are `p`-free. -/
theorem Kzero_spec (q n : ℕ) [NeZero n] (hq : IsPrimePow q) {C₀ : Model.Cond q n}
    (hC₀ : C₀ ∈ Model.essConds q n) :
    Model.dfree q C₀.1 * Model.tord q n C₀ ∣ Kzero q (Model.codim q n C₀) ∧
      Nat.Coprime (Kcrude q (Model.codim q n C₀)) (charOf q) ∧
      Nat.Coprime (Kclosure q (Model.codim q n C₀)) (charOf q) :=
  Kzero_spec' q n hq hC₀

namespace Model

section CompHelpers

variable {q n : ℕ} [NeZero n]

lemma mem_component_self' {ℰ : Finset (Cond q n)} {C : Cond q n} (hC : C ∈ ℰ) :
    C ∈ component q n ℰ C := by
  classical
  exact Finset.mem_filter.mpr ⟨hC, Relation.EqvGen.refl _⟩

lemma eq_component_of_mem {ℰ K : Finset (Cond q n)} (hK : K ∈ components q n ℰ) {C : Cond q n}
    (hC : C ∈ K) : K = component q n ℰ C := by
  classical
  obtain ⟨C', -, rfl⟩ := Finset.mem_image.mp hK
  have h0 : SameComp q n ℰ C' C := (Finset.mem_filter.mp hC).2
  ext D
  simp only [component, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h0.symm.trans _ _ _ h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h0.trans _ _ _ h2⟩

/-- The weight of a component whose codimensions divide `O` and are `≥ o₀`, and whose levels have
`p`-free parts dividing `D`, is at most `Wsum q o₀ O D`. -/
lemma weight_component_le (hq : IsPrimePow q) {C₀ : Cond q n} (hC₀ : C₀ ∈ essConds q n)
    {o₀ O D : ℕ} (hO : O ≠ 0)
    (hcod : ∀ C ∈ component q n (essConds q n) C₀, codim q n C ∣ O ∧ o₀ ≤ codim q n C)
    (hD : levelLcm q n (component q n (essConds q n) C₀) ∣ D) :
    weight q n (component q n (essConds q n) C₀) ≤ Wsum q o₀ O D := by
  classical
  set K := component q n (essConds q n) C₀ with hKdef
  have hmaps : ∀ C ∈ K, codim q n C ∈ O.divisors.filter (o₀ ≤ ·) := fun C hC =>
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(hcod C hC).1, hO⟩, (hcod C hC).2⟩
  unfold weight Wsum
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun o _ => ?_
  have hc := (structure_c q n hq hC₀ o D hD).1
  calc ∑ C ∈ K with codim q n C = o, ((q : ℚ) ^ codim q n C)⁻¹
      = ∑ C ∈ K with codim q n C = o, ((q : ℚ) ^ o)⁻¹ :=
        Finset.sum_congr rfl fun C hC => by rw [(Finset.mem_filter.mp hC).2]
    _ = ((K.filter fun C => codim q n C = o).card : ℚ) * ((q : ℚ) ^ o)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((∑ d ∈ o.divisors.filter (fun d => dfree q d ∣ D),
          d * Nat.gcd (q ^ o - 1) (D / dfree q d) : ℕ) : ℚ) * ((q : ℚ) ^ o)⁻¹ := by
        gcongr
    _ = ((q : ℚ) ^ o)⁻¹ * ∑ d ∈ o.divisors.filter (fun d => pfree (charOf q) d ∣ D),
          (d : ℚ) * (Nat.gcd (q ^ o - 1) (D / pfree (charOf q) d) : ℚ) := by
        rw [mul_comm]; push_cast; rfl

end CompHelpers

end Model

namespace Model

variable (q n : ℕ) [NeZero n]

/-- **Corollary 7.6** (weight of a component): a component without codimension-one
conditions and with minimal codimension `o₀` has weight at most `W_cl(q, o₀)` and at most
`W_cr(q, o₀)`. -/
theorem weight_le_Wcl_Wcr (hq : IsPrimePow q) {K : Finset (Cond q n)}
    (hK : K ∈ components q n (essConds q n)) (hK2 : ∀ C ∈ K, 2 ≤ codim q n C) {o₀ : ℕ}
    (hmin : IsMinCodim q n K o₀) :
    weight q n K ≤ Wcl q o₀ ∧ weight q n K ≤ Wcr q o₀ := by
  obtain ⟨⟨C₀, hC₀K, hco⟩, hmin'⟩ := hmin
  have hC₀ : C₀ ∈ essConds q n := (components_partition _).1 K hK hC₀K
  have hKeq : K = component q n (essConds q n) C₀ := eq_component_of_mem hK hC₀K
  have h2 : 2 ≤ codim q n C₀ := hK2 C₀ hC₀K
  have ho₀ : 1 ≤ o₀ := by omega
  obtain ⟨hKz, hcr, hcl⟩ := Kzero_spec q n hq hC₀
  rw [hco] at hKz hcr hcl
  have hmin2 : ∀ C ∈ component q n (essConds q n) C₀, o₀ ≤ codim q n C :=
    fun C hC => hmin' C (hKeq ▸ hC)
  rw [hKeq]
  constructor
  · obtain ⟨-, hii, hDinf, hOinf⟩ := Kclosure_spec q o₀ hq ho₀
    obtain ⟨hb1, hb2⟩ := structure_b q n hq hC₀ (hKz.trans (Nat.dvd_lcm_left _ _)) hii
    have hO : Oinf q o₀ ≠ 0 := Oinf_ne_zero q o₀ hq ho₀
    exact weight_component_le hq hC₀ hO
      (fun C hC => ⟨(hb1 C hC).2.2.2.trans hOinf, hmin2 C hC⟩) (hb2.trans hDinf)
  · obtain ⟨hii, hLam⟩ := Kcrude_spec q o₀ hq ho₀
    obtain ⟨hb1, hb2⟩ := structure_b q n hq hC₀ (hKz.trans (Nat.dvd_lcm_left _ _)) hii
    have hL : Lambda q o₀ ≠ 0 := Nat.mul_ne_zero (pfree_ne_zero _ (by omega)) (lcmUpTo_ne_zero o₀)
    exact weight_component_le hq hC₀ hL
      (fun C hC => ⟨(hb1 C hC).2.2.2.trans hLam, hmin2 C hC⟩) (hb2.trans (pfree_dvd_pfree hLam _))

/-- The embedding `μ_{n₀'} ⊆ μ_{n'}` for `n₀ ∣ n`, on exponents: `x ↦ (n'/n₀') x`. -/
def embedT (n₀ : ℕ) [NeZero n₀] (x : ZMod (nfree q n₀)) : ZMod (nfree q n) :=
  ((nfree q n / nfree q n₀ : ℕ) : ZMod (nfree q n)) * (x.val : ZMod (nfree q n))

/-- The induced map on conditions. -/
def embedC (n₀ : ℕ) [NeZero n₀] (C : Cond q n₀) : Cond q n :=
  (C.1, C.2.image (embedT q n n₀))

end Model

namespace Model

section Transfer

/-! ### Transfer between `n₀ ∣ n` and `n` (Proposition 7.7) -/

variable {q n n₀ : ℕ} [NeZero n] [NeZero n₀]

lemma nfree_dvd_nfree_of_dvd (h : n₀ ∣ n) : nfree q n₀ ∣ nfree q n := pfree_dvd_pfree h _

lemma nfree_div_mul (h : n₀ ∣ n) : nfree q n / nfree q n₀ * nfree q n₀ = nfree q n :=
  Nat.div_mul_cancel (nfree_dvd_nfree_of_dvd h)

lemma nfree_div_pos (h : n₀ ∣ n) : 0 < nfree q n / nfree q n₀ :=
  Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) (nfree_dvd_nfree_of_dvd h))
    (Nat.pos_of_ne_zero (NeZero.ne _))

lemma embedT_eq_natCast (x : ZMod (nfree q n₀)) :
    embedT q n n₀ x = ((nfree q n / nfree q n₀ * x.val : ℕ) : ZMod (nfree q n)) := by
  unfold embedT; rw [Nat.cast_mul]

lemma embedT_natCast (h : n₀ ∣ n) (k : ℕ) :
    embedT q n n₀ (k : ZMod (nfree q n₀)) =
      ((nfree q n / nfree q n₀ * k : ℕ) : ZMod (nfree q n)) := by
  rw [embedT_eq_natCast, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff']
  obtain ⟨M, hM⟩ : ∃ M, nfree q n / nfree q n₀ = M := ⟨_, rfl⟩
  have hMn : M * nfree q n₀ = nfree q n := hM ▸ nfree_div_mul h
  rw [hM, ← hMn, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]

lemma embedT_add (h : n₀ ∣ n) (x y : ZMod (nfree q n₀)) :
    embedT q n n₀ (x + y) = embedT q n n₀ x + embedT q n n₀ y := by
  have : x + y = ((x.val + y.val : ℕ) : ZMod (nfree q n₀)) := by simp
  rw [this, embedT_natCast h, embedT_eq_natCast, embedT_eq_natCast]
  push_cast; ring

lemma embedT_zero : embedT q n n₀ 0 = 0 := by
  simp [embedT]

lemma embedT_natCast_mul (h : n₀ ∣ n) (a : ℕ) (x : ZMod (nfree q n₀)) :
    embedT q n n₀ ((a : ZMod (nfree q n₀)) * x) = (a : ZMod (nfree q n)) * embedT q n n₀ x := by
  have : (a : ZMod (nfree q n₀)) * x = ((a * x.val : ℕ) : ZMod (nfree q n₀)) := by simp
  rw [this, embedT_natCast h, embedT_eq_natCast]
  push_cast; ring

lemma embedT_qpow_mul (h : n₀ ∣ n) (j : ℕ) (x : ZMod (nfree q n₀)) :
    embedT q n n₀ ((q : ZMod (nfree q n₀)) ^ j * x) =
      (q : ZMod (nfree q n)) ^ j * embedT q n n₀ x := by
  have := embedT_natCast_mul (q := q) h (q ^ j) x
  simpa using this

lemma embedT_injective (h : n₀ ∣ n) : Function.Injective (embedT q n n₀) := by
  intro x y hxy
  rw [embedT_eq_natCast, embedT_eq_natCast, ZMod.natCast_eq_natCast_iff'] at hxy
  obtain ⟨M, hM⟩ : ∃ M, nfree q n / nfree q n₀ = M := ⟨_, rfl⟩
  have hMn : M * nfree q n₀ = nfree q n := hM ▸ nfree_div_mul h
  have hMpos : 0 < M := hM ▸ nfree_div_pos h
  rw [hM, ← hMn, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hxy
  have h1 := Nat.eq_of_mul_eq_mul_left hMpos hxy
  rw [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at h1
  exact ZMod.val_injective _ h1

/-- `embedT` as an additive homomorphism. -/
def embedHom (h : n₀ ∣ n) : ZMod (nfree q n₀) →+ ZMod (nfree q n) where
  toFun := embedT q n n₀
  map_zero' := embedT_zero
  map_add' := embedT_add h

lemma addOrderOf_embedT (h : n₀ ∣ n) (x : ZMod (nfree q n₀)) :
    addOrderOf (embedT q n n₀ x) = addOrderOf x :=
  addOrderOf_injective (embedHom (q := q) h) (embedT_injective h) x

lemma tcodim_embedT (h : n₀ ∣ n) (x : ZMod (nfree q n₀)) :
    tcodim q n (embedT q n n₀ x) = tcodim q n₀ x := by
  simp only [tcodim, addOrderOf_embedT h]

lemma exists_embedT (h : n₀ ∣ n) {y : ZMod (nfree q n)} (hy : addOrderOf y ∣ nfree q n₀) :
    ∃ x, embedT q n n₀ x = y := by
  have h0 : ((nfree q n₀ * y.val : ℕ) : ZMod (nfree q n)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, natCast_mul_eq_nsmul,
      ← addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hy
  rw [ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨M, hM⟩ : ∃ M, nfree q n / nfree q n₀ = M := ⟨_, rfl⟩
  have hMn : M * nfree q n₀ = nfree q n := hM ▸ nfree_div_mul h
  have h0' : M * nfree q n₀ ∣ y.val * nfree q n₀ := by rw [hMn, mul_comm]; exact h0
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero (NeZero.ne _)) h0'
  refine ⟨(k : ZMod (nfree q n₀)), ?_⟩
  rw [embedT_natCast h, hM, ← hk, ZMod.natCast_zmod_val]

lemma mem_targets_iff_dvd {m : ℕ} [NeZero m] {d : ℕ} (hd : d ∣ m) {x : ZMod (nfree q m)} :
    x ∈ targets q m d ↔ dfree q d * addOrderOf x ∣ nfree q m := by
  rw [mem_targets, dvd_bigN_iff, bigN, Nat.dvd_div_iff_mul_dvd (dfree_dvd_nfree hd)]

lemma orbit_image_embedT (hq : IsPrimePow q) (h : n₀ ∣ n) (d : ℕ) (x : ZMod (nfree q n₀)) :
    (orbit q n₀ d x).image (embedT q n n₀) = orbit q n d (embedT q n n₀ x) := by
  ext y
  rw [Finset.mem_image, mem_orbit_iff hq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_orbit_iff hq).mp hz
    exact ⟨j, by rw [← pow_mul, ← pow_mul, embedT_qpow_mul h]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, (mem_orbit_iff hq).mpr ⟨j, rfl⟩, by rw [← pow_mul, ← pow_mul, embedT_qpow_mul h]⟩

lemma embedC_orbit (hq : IsPrimePow q) (h : n₀ ∣ n) (d : ℕ) (x : ZMod (nfree q n₀)) :
    embedC q n n₀ (d, orbit q n₀ d x) = (d, orbit q n d (embedT q n n₀ x)) := by
  simp only [embedC, orbit_image_embedT hq h]

lemma codim_embedC (h : n₀ ∣ n) (C : Cond q n₀) :
    codim q n (embedC q n n₀ C) = codim q n₀ C := by
  classical
  unfold codim embedC
  rw [Finset.sup_image]
  congr 1
  funext x
  exact tcodim_embedT h x

lemma tord_embedC (h : n₀ ∣ n) (C : Cond q n₀) :
    tord q n (embedC q n n₀ C) = tord q n₀ C := by
  classical
  unfold tord embedC
  rw [Finset.sup_image]
  congr 1
  funext x
  exact addOrderOf_embedT h x

lemma embedC_injective (h : n₀ ∣ n) : Function.Injective (embedC q n n₀) := by
  classical
  rintro ⟨d, S⟩ ⟨d', S'⟩ hC
  simp only [embedC, Prod.mk.injEq] at hC
  obtain ⟨rfl, hS⟩ := hC
  rw [Finset.image_injective (embedT_injective h) hS]

lemma embedC_mem_essConds (hq : IsPrimePow q) (h : n₀ ∣ n) {C : Cond q n₀}
    (hC : C ∈ essConds q n₀) : embedC q n n₀ C ∈ essConds q n := by
  obtain ⟨d, hd, x, hx, hess, rfl⟩ := (mem_essConds_iff hq).mp hC
  have hdn₀ : d ∣ n₀ := Nat.dvd_of_mem_divisors hd
  rw [embedC_orbit hq h]
  refine (mem_essConds_iff hq).mpr ⟨d, Nat.mem_divisors.mpr ⟨hdn₀.trans h, NeZero.ne _⟩,
    embedT q n n₀ x, ?_, by rw [tcodim_embedT h]; exact hess, rfl⟩
  have hx' : x ∈ targets q n₀ d := mem_targets.mpr hx
  rw [mem_targets_iff_dvd hdn₀] at hx'
  rw [← mem_targets, mem_targets_iff_dvd (hdn₀.trans h), addOrderOf_embedT h]
  exact hx'.trans (nfree_dvd_nfree_of_dvd h)

lemma exists_embedC_of_mem (hq : IsPrimePow q) (h : n₀ ∣ n) {C : Cond q n}
    (hC : C ∈ essConds q n) (h1 : C.1 ∣ n₀) (h2 : dfree q C.1 * tord q n C ∣ nfree q n₀) :
    ∃ C₀ ∈ essConds q n₀, embedC q n n₀ C₀ = C := by
  obtain ⟨d, -, y, -, hess, rfl⟩ := (mem_essConds_iff hq).mp hC
  simp only at h1 h2
  rw [tord_orbit hq] at h2
  obtain ⟨x, rfl⟩ := exists_embedT h ((Dvd.intro_left _ rfl).trans h2)
  rw [addOrderOf_embedT h] at h2
  rw [tcodim_embedT h] at hess
  refine ⟨(d, orbit q n₀ d x), (mem_essConds_iff hq).mpr ⟨d, Nat.mem_divisors.mpr
    ⟨h1, NeZero.ne _⟩, x, ?_, hess, rfl⟩, embedC_orbit hq h d x⟩
  rw [← mem_targets, mem_targets_iff_dvd h1]
  exact h2

lemma fibre_embedC (hq : IsPrimePow q) (h : n₀ ∣ n) {C : Cond q n₀} (hC : C ∈ conds q n₀) :
    fibre q n (embedC q n n₀ C) = (fibre q n₀ C).image (embedT q n n₀) := by
  classical
  obtain ⟨d, hd, x, hx, rfl⟩ := mem_conds.mp hC
  have hdn₀ : d ∣ n₀ := Nat.dvd_of_mem_divisors hd
  rw [mem_targets_iff_dvd hdn₀] at hx
  ext i
  rw [mem_fibre, Finset.mem_image]
  simp only [embedC]
  constructor
  · intro hi
    obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
    have hzx : addOrderOf z = addOrderOf x := by
      obtain ⟨j, rfl⟩ := (mem_orbit_iff hq).mp hz
      rw [← pow_mul, addOrderOf_qpow_mul hq]
    have hord : addOrderOf i ∣ nfree q n₀ := by
      refine (addOrderOf_dvd_dfree_mul d i).trans ?_
      rw [← hzi, addOrderOf_embedT h, hzx]
      exact hx
    obtain ⟨i₀, rfl⟩ := exists_embedT h hord
    refine ⟨i₀, mem_fibre.mpr ?_, rfl⟩
    have : embedT q n n₀ (((dfree q d : ℕ) : ZMod (nfree q n₀)) * i₀) = embedT q n n₀ z := by
      rw [embedT_natCast_mul h, hzi]
    rw [embedT_injective h this]
    exact hz
  · rintro ⟨i₀, hi₀, rfl⟩
    rw [← embedT_natCast_mul h]
    exact Finset.mem_image_of_mem _ (mem_fibre.mp hi₀)

lemma qrel_embedT_iff (h : n₀ ∣ n) {i i' : ZMod (nfree q n₀)} :
    QRel q n (embedT q n n₀ i) (embedT q n n₀ i') ↔ QRel q n₀ i i' := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, embedT_injective h (by rw [embedT_qpow_mul h]; exact hj)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, embedT_qpow_mul h j i⟩

lemma fibreRel_embedC_iff (hq : IsPrimePow q) (h : n₀ ∣ n) {C C' : Cond q n₀}
    (hC : C ∈ conds q n₀) (hC' : C' ∈ conds q n₀) :
    (∃ i ∈ fibre q n (embedC q n n₀ C), ∃ i' ∈ fibre q n (embedC q n n₀ C'), QRel q n i i') ↔
      (∃ i ∈ fibre q n₀ C, ∃ i' ∈ fibre q n₀ C', QRel q n₀ i i') := by
  classical
  rw [fibre_embedC hq h hC, fibre_embedC hq h hC']
  constructor
  · rintro ⟨_, hi, _, hi', hr⟩
    obtain ⟨i, hi1, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨i', hi1', rfl⟩ := Finset.mem_image.mp hi'
    exact ⟨i, hi1, i', hi1', (qrel_embedT_iff h).mp hr⟩
  · rintro ⟨i, hi, i', hi', hr⟩
    exact ⟨_, Finset.mem_image_of_mem _ hi, _, Finset.mem_image_of_mem _ hi',
      (qrel_embedT_iff h).mpr hr⟩

lemma sameComp_embedC (hq : IsPrimePow q) (h : n₀ ∣ n) {C C' : Cond q n₀}
    (hCC' : SameComp q n₀ (essConds q n₀) C C') :
    SameComp q n (essConds q n) (embedC q n n₀ C) (embedC q n n₀ C') := by
  rw [sameComp_iff_qChain hq] at hCC' ⊢
  induction hCC' with
  | rel a b hab =>
    obtain ⟨ha, hb, hr⟩ := hab
    exact Relation.EqvGen.rel _ _ ⟨embedC_mem_essConds hq h ha, embedC_mem_essConds hq h hb,
      (fibreRel_embedC_iff hq h (essConds_subset ha) (essConds_subset hb)).mpr hr⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

/-- **Core of Proposition 7.7**: if every condition of the `n`-component of `embedC C₀` is a
condition for `n₀`, the `n`-component is the image of the `n₀`-component. -/
theorem component_embedC (hq : IsPrimePow q) (h : n₀ ∣ n) {C₀ : Cond q n₀}
    (hC₀ : C₀ ∈ essConds q n₀)
    (hgood : ∀ C ∈ component q n (essConds q n) (embedC q n n₀ C₀),
      C.1 ∣ n₀ ∧ dfree q C.1 * tord q n C ∣ nfree q n₀) :
    component q n (essConds q n) (embedC q n n₀ C₀) =
      (component q n₀ (essConds q n₀) C₀).image (embedC q n n₀) := by
  classical
  set comp := component q n (essConds q n) (embedC q n n₀ C₀) with hcomp
  -- every member of `comp` comes from an essential condition for `n₀`
  have hpre : ∀ C ∈ comp, ∃ C₁ ∈ essConds q n₀, embedC q n n₀ C₁ = C := fun C hC =>
    exists_embedC_of_mem hq h (Finset.mem_filter.mp hC).1 (hgood C hC).1 (hgood C hC).2
  -- chains inside `comp` pull back
  have back : ∀ a b, Relation.EqvGen (fun C C' => C ∈ essConds q n ∧ C' ∈ essConds q n ∧
        ∃ i ∈ fibre q n C, ∃ i' ∈ fibre q n C', QRel q n i i') a b → a ∈ comp →
      ∀ a₁ b₁, a₁ ∈ essConds q n₀ → b₁ ∈ essConds q n₀ → embedC q n n₀ a₁ = a →
        embedC q n n₀ b₁ = b →
        Relation.EqvGen (fun C C' => C ∈ essConds q n₀ ∧ C' ∈ essConds q n₀ ∧
          ∃ i ∈ fibre q n₀ C, ∃ i' ∈ fibre q n₀ C', QRel q n₀ i i') a₁ b₁ := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      intro _ a₁ b₁ ha₁ hb₁ rfl rfl
      exact Relation.EqvGen.rel _ _ ⟨ha₁, hb₁, (fibreRel_embedC_iff hq h (essConds_subset ha₁)
        (essConds_subset hb₁)).mp hab.2.2⟩
    | refl a =>
      intro _ a₁ b₁ _ _ ha hb
      rw [embedC_injective h (ha.trans hb.symm)]
      exact Relation.EqvGen.refl _
    | symm a b hab ih =>
      intro hb a₁ b₁ ha₁ hb₁ hea heb
      have ha : a ∈ comp := mem_component_of_sameComp hb ((sameComp_iff_qChain hq).mpr hab).symm
      exact (ih ha b₁ a₁ hb₁ ha₁ heb hea).symm
    | trans a b c hab hbc ih1 ih2 =>
      intro ha a₁ c₁ ha₁ hc₁ ha' hc'
      have hb : b ∈ comp := mem_component_of_sameComp ha ((sameComp_iff_qChain hq).mpr hab)
      obtain ⟨b₁, hb₁, hb'⟩ := hpre b hb
      exact (ih1 ha a₁ b₁ ha₁ hb₁ ha' hb').trans _ _ _ (ih2 hb b₁ c₁ hb₁ hc₁ hb' hc')
  have hC₀n : embedC q n n₀ C₀ ∈ essConds q n := embedC_mem_essConds hq h hC₀
  ext C
  constructor
  · intro hC
    obtain ⟨C₁, hC₁, rfl⟩ := hpre C hC
    refine Finset.mem_image.mpr ⟨C₁, Finset.mem_filter.mpr ⟨hC₁, ?_⟩, rfl⟩
    have hs := (sameComp_iff_qChain hq).mp (Finset.mem_filter.mp hC).2
    exact (sameComp_iff_qChain hq).mpr
      (back _ _ hs (Finset.mem_filter.mpr ⟨hC₀n, Relation.EqvGen.refl _⟩) C₀ C₁ hC₀ hC₁ rfl rfl)
  · intro hC
    obtain ⟨C₁, hC₁, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hC₁e, hs⟩ := Finset.mem_filter.mp hC₁
    exact Finset.mem_filter.mpr ⟨embedC_mem_essConds hq h hC₁e, sameComp_embedC hq h hs⟩

end Transfer

end Model


namespace Model

section Prop26

variable {q n : ℕ} [NeZero n]

lemma dvd_pfree_gcd {p a m N : ℕ} (hm : a ∣ m) (hN : a ∣ N) (hc : Nat.Coprime a p) :
    a ∣ pfree p (Nat.gcd m N) := by
  have h1 : a ∣ Nat.gcd m N := Nat.dvd_gcd hm hN
  rw [← pow_mul_pfree p (Nat.gcd m N)] at h1
  exact (Nat.Coprime.pow_right _ hc).dvd_of_dvd_mul_left h1

/-- Theorem 7.2 (b) for the closure `K`: every condition of the component of an essential `C₀` of
codimension `o₀ ≥ 2` is a condition for `gcd(n, N**)`. -/
lemma good_of_codim (hq : IsPrimePow q) {o₀ : ℕ} (ho₀ : 2 ≤ o₀) {C₀ : Cond q n}
    (hC₀ : C₀ ∈ essConds q n) (hco : codim q n C₀ = o₀) :
    ∀ C ∈ component q n (essConds q n) C₀,
      C.1 ∣ Nat.gcd n (Nstarstar q o₀) ∧
        dfree q C.1 * tord q n C ∣ pfree (chr q) (Nat.gcd n (Nstarstar q o₀)) := by
  classical
  obtain ⟨hKz, -, hcl⟩ := Kzero_spec q n hq hC₀
  rw [hco] at hKz hcl
  obtain ⟨-, hii, -, hOinf⟩ := Kclosure_spec q o₀ hq (by omega)
  obtain ⟨hb1, -⟩ := structure_b q n hq hC₀ (hKz.trans (Nat.dvd_lcm_left _ _)) hii
  intro C hC
  obtain ⟨-, h1, h2, -⟩ := hb1 C hC
  have hCc : C ∈ conds q n := essConds_subset (Finset.mem_filter.mp hC).1
  have hKN : Kclosure q o₀ ∣ Nstarstar q o₀ := Nat.dvd_lcm_left _ _
  have hON : Oinf q o₀ ∣ Nstarstar q o₀ := Nat.dvd_lcm_right _ _
  refine ⟨Nat.dvd_gcd (level_dvd_n hCc) ((h1.trans hOinf).trans hON), ?_⟩
  refine dvd_pfree_gcd ?_ (h2.trans hKN) (Nat.Coprime.coprime_dvd_left h2 hcl)
  obtain ⟨d, hd, x, hx, rfl⟩ := mem_conds.mp hCc
  rw [mem_targets_iff_dvd (Nat.dvd_of_mem_divisors hd)] at hx
  rw [tord_orbit hq]
  exact hx.trans (nfree_dvd q n)

end Prop26

end Model

/-- **Proposition 7.7** (finite reduction): for every `n`, the components with minimal
codimension `o₀ ≥ 2` for `(q, n)` coincide, as sets of conditions with their codimensions, with those
for `(q, gcd(n, N**))` (via the embedding `μ_{n₀'} ⊆ μ_{n'}`). -/
theorem finite_reduction (q n : ℕ) [NeZero n] (hq : IsPrimePow q) {o₀ : ℕ} (ho₀ : 2 ≤ o₀) :
    haveI : NeZero (Nat.gcd n (Nstarstar q o₀)) := ⟨Nat.gcd_ne_zero_left (NeZero.ne n)⟩
    (∀ K ∈ Model.components q n (Model.essConds q n), Model.IsMinCodim q n K o₀ →
      ∃ K₀ ∈ Model.components q (Nat.gcd n (Nstarstar q o₀))
          (Model.essConds q (Nat.gcd n (Nstarstar q o₀))),
        Model.IsMinCodim q (Nat.gcd n (Nstarstar q o₀)) K₀ o₀ ∧
        K = K₀.image (Model.embedC q n (Nat.gcd n (Nstarstar q o₀))) ∧
        ∀ C ∈ K₀, Model.codim q n (Model.embedC q n (Nat.gcd n (Nstarstar q o₀)) C) =
          Model.codim q (Nat.gcd n (Nstarstar q o₀)) C) ∧
    (∀ K₀ ∈ Model.components q (Nat.gcd n (Nstarstar q o₀))
          (Model.essConds q (Nat.gcd n (Nstarstar q o₀))),
        Model.IsMinCodim q (Nat.gcd n (Nstarstar q o₀)) K₀ o₀ →
      K₀.image (Model.embedC q n (Nat.gcd n (Nstarstar q o₀))) ∈
        Model.components q n (Model.essConds q n)) := by
  have : NeZero (Nat.gcd n (Nstarstar q o₀)) := ⟨Nat.gcd_ne_zero_left (NeZero.ne n)⟩
  have h : Nat.gcd n (Nstarstar q o₀) ∣ n := Nat.gcd_dvd_left _ _
  constructor
  · intro K hK hmin
    obtain ⟨⟨C₀, hC₀K, hco⟩, hmin'⟩ := hmin
    have hC₀ : C₀ ∈ Model.essConds q n := (Model.components_partition _).1 K hK hC₀K
    have hKeq := Model.eq_component_of_mem hK hC₀K
    have hgood := Model.good_of_codim hq ho₀ hC₀ hco
    obtain ⟨C₀₀, hC₀₀, rfl⟩ := Model.exists_embedC_of_mem hq h hC₀
      (hgood _ (Model.mem_component_self' hC₀)).1 (hgood _ (Model.mem_component_self' hC₀)).2
    have hcomp := Model.component_embedC hq h hC₀₀ hgood
    refine ⟨Model.component q _ (Model.essConds q _) C₀₀, Finset.mem_image_of_mem _ hC₀₀,
      ⟨⟨C₀₀, Model.mem_component_self' hC₀₀, by rw [← Model.codim_embedC h]; exact hco⟩,
        fun C hC => ?_⟩, hKeq.trans hcomp, fun C _ => Model.codim_embedC h C⟩
    rw [← Model.codim_embedC h]
    exact hmin' _ (by rw [hKeq, hcomp]; exact Finset.mem_image_of_mem _ hC)
  · intro K₀ hK₀ hmin
    obtain ⟨⟨C₀₀, hC₀₀K, hco⟩, -⟩ := hmin
    have hC₀₀ := (Model.components_partition _).1 K₀ hK₀ hC₀₀K
    have hK₀eq := Model.eq_component_of_mem hK₀ hC₀₀K
    have hC₀ := Model.embedC_mem_essConds hq h hC₀₀
    have hco' : Model.codim q n (Model.embedC q n _ C₀₀) = o₀ := by
      rw [Model.codim_embedC h]; exact hco
    have hgood := Model.good_of_codim hq ho₀ hC₀ hco'
    rw [hK₀eq, ← Model.component_embedC hq h hC₀₀ hgood]
    exact Finset.mem_image_of_mem _ hC₀

/-- **Proposition 7.7**, consequence for weights: every component for `(q, n)` with minimal
codimension `o₀ ≥ 2` has the same weight as a component with minimal codimension `o₀` for some
`n₀ ∣ N**`. -/
theorem finite_reduction_weight (q n : ℕ) [NeZero n] (hq : IsPrimePow q) {o₀ : ℕ} (ho₀ : 2 ≤ o₀)
    {K : Finset (Model.Cond q n)} (hK : K ∈ Model.components q n (Model.essConds q n))
    (hmin : Model.IsMinCodim q n K o₀) :
    ∃ n₀, ∃ _ : NeZero n₀, n₀ ∣ Nstarstar q o₀ ∧
      ∃ K₀ ∈ Model.components q n₀ (Model.essConds q n₀), Model.IsMinCodim q n₀ K₀ o₀ ∧
        Model.weight q n₀ K₀ = Model.weight q n K := by
  have : NeZero (Nat.gcd n (Nstarstar q o₀)) := ⟨Nat.gcd_ne_zero_left (NeZero.ne n)⟩
  have hinj := Model.embedC_injective (q := q) (n := n) (Nat.gcd_dvd_left n (Nstarstar q o₀))
  obtain ⟨h1, -⟩ := finite_reduction q n hq ho₀
  obtain ⟨K₀, hK₀, hmin₀, hKeq, hcod⟩ := h1 K hK hmin
  refine ⟨Nat.gcd n (Nstarstar q o₀), ⟨Nat.gcd_ne_zero_left (NeZero.ne n)⟩, Nat.gcd_dvd_right _ _,
    K₀, hK₀, hmin₀, ?_⟩
  subst hKeq
  unfold Model.weight
  rw [Finset.sum_image (fun C _ C' _ hCC' => hinj hCC')]
  exact Finset.sum_congr rfl fun C hC => by rw [hcod C hC]

end MorganMullen
