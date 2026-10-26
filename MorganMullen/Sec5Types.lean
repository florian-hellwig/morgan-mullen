import MorganMullen.Sec3Components
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Section 5 (Lemma 5.2): exact `M` and `S`

The essential conditions are counted by their *types* `(d, e)` (`d ∣ n`, `e ∣ n'/d'`, `d ∣ ord_e(q)`):
there are exactly `ν_{d,e} = d φ(e)/ord_e(q)` of each type, so `M = ∑ ν_{d,e}` and
`S = ∑_{ord_e(q) ≥ 2} ν_{d,e} q^{-ord_e(q)}`; the number of conditions of codimension `o` is bounded.
-/

set_option linter.unusedSectionVars false

namespace MorganMullen
namespace Model
open Finset

variable {q n : ℕ} [NeZero n]

lemma ordMod_pow_dvd_iff (q e d k : ℕ) : ordMod (q ^ d) e ∣ k ↔ ordMod q e ∣ d * k := by
  rw [ordMod_dvd_iff, ordMod_dvd_iff, Nat.cast_pow, ← pow_mul]

lemma qpowd_mul_eq_self_iff (hq : IsPrimePow q) (d k : ℕ) (x : ZMod (nfree q n)) :
    ((q : ZMod (nfree q n)) ^ d) ^ k * x = x ↔ ordMod (q ^ d) (addOrderOf x) ∣ k := by
  rw [← pow_mul, qpow_mul_eq_self_iff hq, ordMod_pow_dvd_iff]

lemma coprime_q_addOrderOf (hq : IsPrimePow q) (x : ZMod (nfree q n)) :
    Nat.Coprime q (addOrderOf x) :=
  coprime_q_of_dvd_nfree hq (NeZero.ne n) (addOrderOf_dvd_nfree x)

lemma ordMod_le_of_coprime {q e : ℕ} (h : Nat.Coprime q e) (he : e ≠ 0) : ordMod q e ≤ e := by
  have : NeZero e := ⟨he⟩
  rw [ordMod_eq_orderOf_unit h]
  calc orderOf (ZMod.unitOfCoprime q h) ≤ Fintype.card (ZMod e)ˣ := orderOf_le_card_univ
    _ ≤ Fintype.card (ZMod e) := Fintype.card_le_of_injective _ Units.val_injective
    _ = e := ZMod.card e

/-- The size of the orbit of a target under `x ↦ q^d x` is `ord_e(q^d)`. -/
lemma card_orbit (hq : IsPrimePow q) (d : ℕ) (x : ZMod (nfree q n)) :
    (orbit q n d x).card = ordMod (q ^ d) (addOrderOf x) := by
  set s := ordMod (q ^ d) (addOrderOf x) with hs
  set u : ZMod (nfree q n) := (q : ZMod (nfree q n)) ^ d
  have hcop : Nat.Coprime (q ^ d) (addOrderOf x) := (coprime_q_addOrderOf hq x).pow_left d
  have hspos : 0 < s := ordMod_pos hcop (addOrderOf_pos' x).ne'
  have hsle : s ≤ nfree q n :=
    (ordMod_le_of_coprime hcop (addOrderOf_pos' x).ne').trans
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) (addOrderOf_dvd_nfree x))
  have hper : ∀ j, u ^ j * x = u ^ (j % s) * x := by
    intro j
    conv_lhs => rw [← Nat.mod_add_div j s, pow_add, mul_assoc, pow_mul]
    congr 1
    induction (j / s) with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, mul_comm (_ ^ m), mul_assoc, ih, (qpowd_mul_eq_self_iff hq d s x).mpr dvd_rfl]
  have hunit : IsUnit u := by
    have := ((qUnit (n := n) hq) ^ d).isUnit; simpa [u] using this
  have himg : orbit q n d x = (range s).image fun j => u ^ j * x := by
    ext y; simp only [orbit, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, -, rfl⟩; exact ⟨j % s, Nat.mod_lt _ hspos, (hper j).symm⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj.trans_le hsle, rfl⟩
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  have key : ∀ a b, a < b → b < s → u ^ a * x = u ^ b * x → False := by
    intro a b hab hb habx
    have h1 : u ^ (b - a) * x = x := by
      have hu' : IsUnit (u ^ a) := hunit.pow a
      apply hu'.mul_left_cancel
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab.le]
      exact habx.symm
    have h2 := (qpowd_mul_eq_self_iff hq d (b - a) x).mp h1
    have : s ≤ b - a := Nat.le_of_dvd (by omega) h2
    omega
  intro j hj j' hj' hjj
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  rcases lt_trichotomy j j' with h | h | h
  · exact (key j j' h hj' hjj).elim
  · exact h
  · exact (key j' j h hj hjj.symm).elim

/-- Counting orbits: if `X` is a union of orbits all of size `s`, then there are `|X|/s` of them. -/
lemma card_image_orbit_mul (hq : IsPrimePow q) (d : ℕ) (X : Finset (ZMod (nfree q n)))
    (hX : ∀ x ∈ X, orbit q n d x ⊆ X) (s : ℕ) (hs : ∀ x ∈ X, (orbit q n d x).card = s) :
    (X.image fun x => ((d, orbit q n d x) : Cond q n)).card * s = X.card := by
  classical
  rw [Finset.card_eq_sum_card_image (fun x => ((d, orbit q n d x) : Cond q n)) X,
    Finset.sum_const_nat]
  intro C hC
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hC
  rw [← hs x0 hx0]
  congr 1
  ext y
  simp only [Finset.mem_filter, Prod.mk.injEq, true_and]
  constructor
  · rintro ⟨-, hy⟩; rw [← hy]; exact mem_orbit_self d y
  · intro hy; exact ⟨hX x0 hx0 hy, orbit_eq_of_mem hq hy⟩

lemma mem_essTypes {d e : ℕ} :
    (d, e) ∈ essTypes q n ↔ d ∈ n.divisors ∧ e ∈ (nfree q n).divisors ∧ e ∣ bigN q n d ∧
      d ∣ ordMod q e := by
  classical
  simp [essTypes, and_assoc]

lemma ordMod_dvd_totient (hq : IsPrimePow q) {e : ℕ} (he : e ∣ nfree q n) :
    ordMod q e ∣ Nat.totient e := by
  have hc := coprime_q_of_dvd_nfree hq (NeZero.ne n) he
  have hepos : e ≠ 0 := ne_zero_of_dvd_ne_zero (NeZero.ne _) he
  have : NeZero e := ⟨hepos⟩
  rw [ordMod_eq_orderOf_unit hc, ← ZMod.card_units_eq_totient]
  exact orderOf_dvd_card

/-- **Lemma 5.2**: `ν_{d,e} ord_e(q) = d φ(e)`. -/
theorem nu_mul (hq : IsPrimePow q) {d e : ℕ} (hde : (d, e) ∈ essTypes q n) :
    nu q d e * ordMod q e = d * Nat.totient e := by
  obtain ⟨-, he, -, -⟩ := mem_essTypes.mp hde
  exact Nat.div_mul_cancel (Dvd.dvd.mul_left (ordMod_dvd_totient hq (Nat.dvd_of_mem_divisors he)) d)

lemma mem_essConds_iff (hq : IsPrimePow q) {C : Cond q n} :
    C ∈ essConds q n ↔ ∃ d ∈ n.divisors, ∃ x : ZMod (nfree q n),
      ((bigN q n d : ℕ) : ZMod (nfree q n)) * x = 0 ∧ d ∣ tcodim q n x ∧ C = (d, orbit q n d x) := by
  rw [mem_essConds, mem_conds]
  constructor
  · rintro ⟨⟨d, hd, x, hx, rfl⟩, hess⟩
    rw [codim_orbit hq] at hess
    exact ⟨d, hd, x, mem_targets.mp hx, hess, rfl⟩
  · rintro ⟨d, hd, x, hx, hess, rfl⟩
    exact ⟨⟨d, hd, x, mem_targets.mpr hx, rfl⟩, by rw [codim_orbit hq]; exact hess⟩

lemma dvd_bigN_iff {d : ℕ} {y : ZMod (nfree q n)} :
    ((bigN q n d : ℕ) : ZMod (nfree q n)) * y = 0 ↔ addOrderOf y ∣ bigN q n d := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero, natCast_mul_eq_nsmul]

lemma type_mem_essTypes (hq : IsPrimePow q) {C : Cond q n} (hC : C ∈ essConds q n) :
    (C.1, tord q n C) ∈ essTypes q n := by
  obtain ⟨d, hd, x, hx, hess, rfl⟩ := (mem_essConds_iff hq).mp hC
  rw [tord_orbit hq, mem_essTypes]
  refine ⟨hd, Nat.mem_divisors.mpr ⟨addOrderOf_dvd_nfree x, NeZero.ne _⟩,
    dvd_bigN_iff.mp hx, hess⟩

/-- **Lemma 5.2**: exactly `ν_{d,e}` essential conditions of type `(d, e)`, each of
codimension `ord_e(q)`. -/
theorem card_essConds_type (hq : IsPrimePow q) {d e : ℕ} (hde : (d, e) ∈ essTypes q n) :
    ((essConds q n).filter fun C => C.1 = d ∧ tord q n C = e).card = nu q d e ∧
      ∀ C ∈ essConds q n, C.1 = d → tord q n C = e → codim q n C = ordMod q e := by
  classical
  obtain ⟨hd, he, heN, hdo⟩ := mem_essTypes.mp hde
  have he' : e ∣ nfree q n := Nat.dvd_of_mem_divisors he
  constructor
  · set X : Finset (ZMod (nfree q n)) := univ.filter fun x => addOrderOf x = e
    have hXcard : X.card = Nat.totient e := by
      have := IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod (nfree q n)) (d := e)
        (by rw [ZMod.card]; exact he')
      simpa [X] using this
    have himg : ((essConds q n).filter fun C => C.1 = d ∧ tord q n C = e) =
        X.image fun x => ((d, orbit q n d x) : Cond q n) := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_image, X, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hC, rfl, hCe⟩
        obtain ⟨d', hd', x, hx, hess, rfl⟩ := (mem_essConds_iff hq).mp hC
        exact ⟨x, by rw [← hCe, tord_orbit hq], rfl⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨(mem_essConds_iff hq).mpr ⟨d, hd, x, ?_, ?_, rfl⟩, rfl, by rw [tord_orbit hq, hx]⟩
        · rw [dvd_bigN_iff, hx]; exact heN
        · unfold tcodim; rw [hx]; exact hdo
    have hs : ∀ x ∈ X, (orbit q n d x).card = ordMod q e / d := by
      intro x hx
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [card_orbit hq, hx, ordMod_pow _ _ (Nat.pos_of_mem_divisors hd).ne',
        Nat.gcd_eq_right hdo]
    have hclosed : ∀ x ∈ X, orbit q n d x ⊆ X := by
      intro x hx y hy
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨j, rfl⟩ := (mem_orbit_iff hq).mp hy
      rw [← pow_mul, addOrderOf_qpow_mul hq, hx]
    have key := card_image_orbit_mul hq d X hclosed _ hs
    rw [← himg, hXcard] at key
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hopos : 0 < ordMod q e := ordMod_pos (coprime_q_of_dvd_nfree hq (NeZero.ne n) he')
      (Nat.pos_of_mem_divisors he).ne'
    obtain ⟨m, hm⟩ := hdo
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hm; omega)
    rw [hm, Nat.mul_div_cancel_left _ hdpos] at key
    unfold nu
    set c := ((essConds q n).filter fun C => C.1 = d ∧ tord q n C = e).card
    rw [hm, ← key, show d * (c * m) = c * (d * m) by ring, Nat.mul_div_cancel _ (Nat.mul_pos hdpos hmpos)]
  · rintro C hC rfl hCe
    obtain ⟨d', hd', x, hx, hess, rfl⟩ := (mem_essConds_iff hq).mp hC
    rw [codim_orbit hq]
    rw [tord_orbit hq] at hCe
    unfold tcodim; rw [hCe]


/-- **Lemma 5.2**: `M = ∑_{(d,e)} ν_{d,e}`. -/
theorem numM_eq (hq : IsPrimePow q) : numM q n = ∑ de ∈ essTypes q n, nu q de.1 de.2 := by
  classical
  unfold numM
  rw [Finset.card_eq_sum_card_fiberwise (f := fun C : Cond q n => (C.1, tord q n C))
    (t := essTypes q n) (fun C hC => type_mem_essTypes hq hC)]
  refine Finset.sum_congr rfl fun de hde => ?_
  rw [← (card_essConds_type hq hde).1]
  congr 1
  ext C; simp [Prod.ext_iff]

lemma codim_of_type (hq : IsPrimePow q) {C : Cond q n} (hC : C ∈ essConds q n) :
    codim q n C = ordMod q (tord q n C) := by
  classical
  exact (card_essConds_type hq (type_mem_essTypes hq hC)).2 C hC rfl rfl

open Classical in
/-- **Lemma 5.2**: `S = ∑_{(d,e) : ord_e(q) ≥ 2} ν_{d,e} q^{-ord_e(q)}`. -/
theorem sumS_eq (hq : IsPrimePow q) :
    sumS q n = ∑ de ∈ (essTypes q n).filter (fun de => 2 ≤ ordMod q de.2),
      (nu q de.1 de.2 : ℚ) * ((q : ℚ) ^ ordMod q de.2)⁻¹ := by
  unfold sumS weight
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun C : Cond q n => (C.1, tord q n C))
    (t := (essTypes q n).filter (fun de => 2 ≤ ordMod q de.2))]
  · refine Finset.sum_congr rfl fun de hde => ?_
    have hde' := (Finset.mem_filter.mp hde).1
    have hset : (((essConds q n).filter fun C => 2 ≤ codim q n C).filter
        fun C => (C.1, tord q n C) = de) =
        (essConds q n).filter fun C => C.1 = de.1 ∧ tord q n C = de.2 := by
      ext C
      simp only [Finset.mem_filter, Prod.ext_iff]
      constructor
      · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨h1, ?_⟩, h2, h3⟩
        rw [codim_of_type hq h1, h3]; exact (Finset.mem_filter.mp hde).2
    rw [hset, Finset.sum_congr rfl (g := fun _ => ((q : ℚ) ^ ordMod q de.2)⁻¹)]
    · rw [Finset.sum_const, nsmul_eq_mul, (card_essConds_type hq hde').1]
    · intro C hC
      obtain ⟨hCe, -, h2⟩ := Finset.mem_filter.mp hC
      rw [codim_of_type hq hCe, h2]
  · intro C hC
    obtain ⟨hCe, h2⟩ := Finset.mem_filter.mp hC
    refine Finset.mem_filter.mpr ⟨type_mem_essTypes hq hCe, ?_⟩
    rw [← codim_of_type hq hCe]; exact h2

open Classical in
/-- **Lemma 5.2**, last part. -/
theorem card_codim_le (hq : IsPrimePow q) (o : ℕ) (ho : 1 ≤ o) :
    (((essConds q n).filter fun C => codim q n C = o).card : ℚ) ≤
        ((∑ d ∈ o.divisors, d : ℕ) : ℚ) / o *
          ((univ.filter fun i : ZMod (nfree q n) => tcodim q n i = o).card : ℚ) ∧
      ((univ.filter fun i : ZMod (nfree q n) => tcodim q n i = o).card : ℚ) ≤
        min (nfree q n : ℚ) ((q : ℚ) ^ o - 1) := by
  set Y : Finset (ZMod (nfree q n)) := univ.filter fun i => tcodim q n i = o with hY
  have hopos : (0 : ℚ) < o := by exact_mod_cast ho
  constructor
  · have hsub : ((essConds q n).filter fun C => codim q n C = o) ⊆
        o.divisors.biUnion fun d => Y.image fun x => ((d, orbit q n d x) : Cond q n) := by
      intro C hC
      obtain ⟨hCe, hco⟩ := Finset.mem_filter.mp hC
      obtain ⟨d, hd, x, hx, hess, rfl⟩ := (mem_essConds_iff hq).mp hCe
      rw [codim_orbit hq] at hco
      refine Finset.mem_biUnion.mpr ⟨d, Nat.mem_divisors.mpr ⟨hco ▸ hess, by omega⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hco⟩, rfl⟩
    have hcard : ∀ d ∈ o.divisors,
        ((Y.image fun x => ((d, orbit q n d x) : Cond q n)).card : ℚ) = (d : ℚ) / o * Y.card := by
      intro d hd
      have hdo : d ∣ o := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hs : ∀ x ∈ Y, (orbit q n d x).card = o / d := by
        intro x hx
        simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [card_orbit hq, ordMod_pow _ _ hdpos.ne']
        have : ordMod q (addOrderOf x) = o := hx
        rw [this, Nat.gcd_eq_right hdo]
      have hclosed : ∀ x ∈ Y, orbit q n d x ⊆ Y := by
        intro x hx y hy
        simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨j, rfl⟩ := (mem_orbit_iff hq).mp hy
        rw [← pow_mul, tcodim_qpow_mul hq, hx]
      have key := card_image_orbit_mul hq d Y hclosed _ hs
      have key' : ((Y.image fun x => ((d, orbit q n d x) : Cond q n)).card : ℚ) * ((o / d : ℕ) : ℚ)
          = Y.card := by exact_mod_cast key
      rw [Nat.cast_div hdo (by exact_mod_cast hdpos.ne')] at key'
      have hdq : (0 : ℚ) < d := by exact_mod_cast hdpos
      field_simp at key' ⊢
      linarith
    calc (((essConds q n).filter fun C => codim q n C = o).card : ℚ)
        ≤ ((o.divisors.biUnion fun d => Y.image fun x => ((d, orbit q n d x) : Cond q n)).card : ℚ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ d ∈ o.divisors, ((Y.image fun x => ((d, orbit q n d x) : Cond q n)).card : ℚ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ d ∈ o.divisors, (d : ℚ) / o * Y.card := Finset.sum_congr rfl hcard
      _ = ((∑ d ∈ o.divisors, d : ℕ) : ℚ) / o * Y.card := by
          rw [← Finset.sum_mul]; congr 1; push_cast; simp only [div_eq_mul_inv, Finset.sum_mul]
  · refine le_min ?_ ?_
    · have : Y.card ≤ nfree q n := by
        calc Y.card ≤ (univ : Finset (ZMod (nfree q n))).card := Finset.card_le_univ _
          _ = nfree q n := by rw [Finset.card_univ, ZMod.card]
      exact_mod_cast this
    · have hq2 : 2 ≤ q := hq.two_le
      have hpow : 1 < q ^ o := Nat.one_lt_pow (by omega) (by omega)
      have hsub : Y ⊆ univ.filter fun i : ZMod (nfree q n) => (q ^ o - 1) • i = 0 := by
        intro i hi
        simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        have h1 : (q : ZMod (nfree q n)) ^ o * i = i :=
          (qpow_mul_eq_self_iff hq o i).mpr (by rw [show ordMod q (addOrderOf i) = o from hi])
        rw [← natCast_mul_eq_nsmul, Nat.cast_sub hpow.le, sub_mul, Nat.cast_pow, h1,
          Nat.cast_one, one_mul, sub_self]
      have := (Finset.card_le_card hsub).trans
        (IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod (nfree q n)) (n := q ^ o - 1) (by omega))
      have h' : ((q ^ o - 1 : ℕ) : ℚ) = (q : ℚ) ^ o - 1 := by
        rw [Nat.cast_sub hpow.le]; push_cast; ring
      rw [← h']; exact_mod_cast this

end Model
end MorganMullen
