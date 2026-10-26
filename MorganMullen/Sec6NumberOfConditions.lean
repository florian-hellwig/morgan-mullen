import MorganMullen.Sec5Types
import MorganMullen.Sec6Runs

/-!
# Section 6: the number of essential conditions

* `ρ(η)`, `s(η)`, Lemma 6.1: `M = ∑_η ρ(η)` (`numM_eq_sum_rho`), `S = ∑_η s(η)` (`sumS_eq_sum_sEta`).
* `f_a`, `f`, `R_a`, `R*_a`; Lemma 6.2 (`f(o) ≤ 1`); Proposition 6.3 (local bound);
  Corollary 6.4 (`M ≤ n`); Proposition 6.5 (`q ≤ 4`).
-/

set_option linter.unusedSectionVars false

namespace MorganMullen

open Finset

namespace Model

variable (q n : ℕ) [NeZero n]

/-- `e_d(η) = ord(η^{d'})` for `η = ζ^i`. -/
noncomputable def ed (d : ℕ) (i : ZMod (nfree q n)) : ℕ :=
  addOrderOf (((dfree q d : ℕ) : ZMod (nfree q n)) * i)

/-- The level `d` is *valid* at `η = ζ^i`: `d ∣ n` and `d ∣ ord_{e_d(η)}(q)`. -/
def ValidAt (d : ℕ) (i : ZMod (nfree q n)) : Prop := d ∣ n ∧ d ∣ ordMod q (ed q n d i)

open Classical in
/-- `ρ(η) = ∑_{d valid at η} p^c / ord_{e_d(η)}(q)`. -/
noncomputable def rho (i : ZMod (nfree q n)) : ℚ :=
  ∑ d ∈ n.divisors.filter (fun d => ValidAt q n d i),
    ((chr q : ℚ) ^ dval q d) / ordMod q (ed q n d i)

open Classical in
/-- `s(η) = ∑_{d} p^c q^{-o_d(η)} / o_d(η)` over the levels `d = p^c d'` valid at `η = ζ^i` with
`o_d(η) = ord_{e_d(η)}(q) ≥ 2` (before Lemma 6.1). -/
noncomputable def sEta (i : ZMod (nfree q n)) : ℚ :=
  ∑ d ∈ n.divisors.filter (fun d => ValidAt q n d i ∧ 2 ≤ ordMod q (ed q n d i)),
    (chr q : ℚ) ^ dval q d / ordMod q (ed q n d i) * ((q : ℚ) ^ ordMod q (ed q n d i))⁻¹

end Model

/-- `f_a(o) = ∑_{d ∣ o, v_p(d) ≤ a} p^{v_p(d) - a} min(1/d, d/o)` (with `p = minFac q`). -/
noncomputable def fa (q a o : ℕ) : ℚ :=
  ∑ d ∈ o.divisors.filter (fun d => d.factorization (charOf q) ≤ a),
    (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a *
      min (1 / (d : ℚ)) ((d : ℚ) / o)

/-- `f(o) = ∑_{d ∣ o} min(1/d, d/o)`. -/
noncomputable def ff (o : ℕ) : ℚ := ∑ d ∈ o.divisors, min (1 / (d : ℚ)) ((d : ℚ) / o)

open Classical in
/-- `R_a(k) = ∑_{d ∣ o, v_p(d) ≤ a, d ∣ ord_{k/gcd(k,d')}(q)} p^{v_p(d)-a} / ord_{k/gcd(k,d')}(q)`, `o = ord_k(q)`. -/
noncomputable def Ra (q a k : ℕ) : ℚ :=
  ∑ d ∈ (ordMod q k).divisors.filter (fun d => d.factorization (charOf q) ≤ a ∧
      d ∣ ordMod q (k / Nat.gcd k (pfree (charOf q) d))),
    (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a /
      ordMod q (k / Nat.gcd k (pfree (charOf q) d))

open Classical in
/-- `R*_a(o) = max {R_a(k) : k ∣ q^o - 1, ord_k(q) = o}` (and `0` if there is no such `k`). -/
noncomputable def RaStar (q a o : ℕ) : ℚ :=
  ((q ^ o - 1).divisors.filter fun k => ordMod q k = o).fold max 0 (Ra q a)

end MorganMullen

namespace MorganMullen
open Finset

lemma sum_le_of_sub_range {T : Finset ℕ} {m : ℕ} (h : ∀ d ∈ T, d ≤ m) : (∑ d ∈ T, d) * 2 ≤ m * (m + 1) := by
  have hsub : T ⊆ range (m + 1) := fun d hd => mem_range.mpr (Nat.lt_succ_of_le (h d hd))
  have := Finset.sum_le_sum_of_subset (f := id) hsub
  have h2 := Finset.sum_range_id_mul_two (m + 1)
  simp only [id] at this
  rw [Nat.add_sub_cancel] at h2
  calc (∑ d ∈ T, d) * 2 ≤ (∑ i ∈ range (m + 1), i) * 2 := Nat.mul_le_mul_right 2 this
    _ = (m + 1) * m := h2
    _ = m * (m + 1) := by ring

/-- **Lemma 6.2** (divisor sums): `∑_{d ∣ o} min(d, o/d) ≤ o`. -/
theorem sum_min_divisors_le (o : ℕ) (ho : 1 ≤ o) :
    ∑ d ∈ o.divisors, min d (o / d) ≤ o := by
  classical
  -- split `min d (o/d)` according to `d * d ≤ o`
  have hsplit : ∀ d ∈ o.divisors, min d (o / d) =
      (if d * d ≤ o then d else 0) + (if o < d * d then o / d else 0) := by
    intro d hd
    have hdo := Nat.dvd_of_mem_divisors hd
    have hdpos := Nat.pos_of_mem_divisors hd
    by_cases h : d * d ≤ o
    · have : d ≤ o / d := (Nat.le_div_iff_mul_le hdpos).mpr h
      simp [h, not_lt.mpr h, min_eq_left this]
    · push Not at h
      have : o / d < d := (Nat.div_lt_iff_lt_mul hdpos).mpr h
      simp [not_le.mpr h, h, min_eq_right this.le]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the second sum equals the sum over `d` with `d * d < o`, via `d ↦ o/d`
  have hsecond : ∑ d ∈ o.divisors, (if o < d * d then o / d else 0) =
      ∑ d ∈ o.divisors, (if d * d < o then d else 0) := by
    rw [← Nat.sum_div_divisors o (fun d => if d * d < o then d else 0)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdo := Nat.dvd_of_mem_divisors hd
    have hdpos := Nat.pos_of_mem_divisors hd
    obtain ⟨c, hc⟩ := hdo
    have hc' : o / d = c := by rw [hc, Nat.mul_div_cancel_left _ hdpos]
    rw [hc']
    have : o < d * d ↔ c * c < o := by
      rw [hc]
      constructor
      · intro h
        have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; omega)
        nlinarith
      · intro h
        have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; omega)
        nlinarith
    simp [this]
  rw [hsecond]
  set s := Nat.sqrt o with hs
  have hsq : s * s ≤ o := Nat.sqrt_le o
  have hsq' : o < (s + 1) * (s + 1) := Nat.lt_succ_sqrt o
  have hle_s : ∀ d, d * d ≤ o → d ≤ s := fun d h => Nat.le_sqrt.mpr h
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  by_cases hA : s ∣ o ∧ s * s < o
  · -- both sums run over divisors `≤ s`, and `d * d = o` is impossible
    have h1 : ∀ d ∈ o.divisors.filter (fun d => d * d ≤ o), d ≤ s :=
      fun d hd => hle_s d (Finset.mem_filter.mp hd).2
    have h2 : ∀ d ∈ o.divisors.filter (fun d => d * d < o), d ≤ s :=
      fun d hd => hle_s d (Finset.mem_filter.mp hd).2.le
    have b1 := sum_le_of_sub_range h1
    have b2 := sum_le_of_sub_range h2
    obtain ⟨t, ht⟩ := hA.1
    have hts : s + 1 ≤ t := by
      by_contra hc; push Not at hc
      have : s * t ≤ s * s := Nat.mul_le_mul_left s (by omega)
      rw [← ht] at this; omega
    have : s * (s + 1) ≤ o := by rw [ht]; exact Nat.mul_le_mul_left s hts
    omega
  · have h2 : ∀ d ∈ o.divisors.filter (fun d => d * d < o), d ≤ s - 1 := by
      intro d hd
      obtain ⟨hdd, hlt⟩ := Finset.mem_filter.mp hd
      have hds : d ≤ s := hle_s d hlt.le
      rcases Nat.lt_or_ge d s with h | h
      · omega
      · have : d = s := le_antisymm hds h
        subst this
        exact absurd ⟨Nat.dvd_of_mem_divisors hdd, hlt⟩ hA
    have b2 := sum_le_of_sub_range h2
    -- first sum = second sum + (the term `d * d = o`, which is at most `s`)
    have hdecomp : ∑ d ∈ o.divisors.filter (fun d => d * d ≤ o), d ≤
        (∑ d ∈ o.divisors.filter (fun d => d * d < o), d) + s := by
      have : o.divisors.filter (fun d => d * d ≤ o) ⊆
          insert s (o.divisors.filter (fun d => d * d < o)) := by
        intro d hd
        obtain ⟨hdd, hle⟩ := Finset.mem_filter.mp hd
        rcases Nat.lt_or_ge (d * d) o with h | h
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hdd, h⟩)
        · have hdo : d * d = o := le_antisymm hle h
          have : d = s := by
            apply le_antisymm (hle_s d hle)
            by_contra hc; push Not at hc
            have : (d + 1) * (d + 1) ≤ s * s := Nat.mul_le_mul hc hc
            nlinarith
          exact this ▸ Finset.mem_insert_self _ _
      calc ∑ d ∈ o.divisors.filter (fun d => d * d ≤ o), d
          ≤ ∑ d ∈ insert s (o.divisors.filter (fun d => d * d < o)), d :=
            Finset.sum_le_sum_of_subset this
        _ ≤ s + ∑ d ∈ o.divisors.filter (fun d => d * d < o), d := by
            by_cases hm : s ∈ o.divisors.filter (fun d => d * d < o)
            · rw [Finset.insert_eq_of_mem hm]; omega
            · rw [Finset.sum_insert hm]
        _ = _ := by ring
    have H : (s - 1) * (s - 1 + 1) = s * s - s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · simp [h0]
      · rw [Nat.sub_add_cancel h0, Nat.sub_mul, one_mul]
    have hss : s ≤ s * s := Nat.le_mul_self s
    omega



/-- Elements of `ZMod k` that are `≡ 1 (mod e)`: there are at most `k/e` of them. -/
lemma card_congr_one_le {k e : ℕ} [NeZero k] (he : e ∣ k) :
    (univ.filter fun y : ZMod k => ((y.val : ℕ) : ZMod e) = 1).card ≤ k / e := by
  rcases Nat.eq_zero_or_pos e with rfl | hepos
  · rw [zero_dvd_iff] at he; exact absurd he (NeZero.ne k)
  calc (univ.filter fun y : ZMod k => ((y.val : ℕ) : ZMod e) = 1).card
      ≤ ((range (k / e)).image fun t => (((1 % e) + e * t : ℕ) : ZMod k)).card := by
        apply Finset.card_le_card
        intro y hy
        have hy' : ((y.val : ℕ) : ZMod e) = ((1 : ℕ) : ZMod e) := by simpa using (Finset.mem_filter.mp hy).2
        rw [ZMod.natCast_eq_natCast_iff'] at hy'
        refine Finset.mem_image.mpr ⟨y.val / e, Finset.mem_range.mpr ?_, ?_⟩
        · have hlt := ZMod.val_lt y
          obtain ⟨c, hc⟩ := he
          have hkc : k / e = c := by rw [hc, Nat.mul_div_cancel_left _ hepos]
          rw [hkc]
          exact Nat.div_lt_of_lt_mul (by rw [← hc]; exact hlt)
        · have := Nat.div_add_mod y.val e
          rw [← hy', add_comm, this, ZMod.natCast_zmod_val]
    _ ≤ (range (k / e)).card := Finset.card_image_le
    _ = k / e := Finset.card_range _

/-- The key inequality of Proposition 6.3: for `e ∣ k` (coprime to `q`), `ord_k(q) ≤ ord_e(q) · (k/e)`. -/
lemma ordMod_le_mul_div {q k e : ℕ} (hk : k ≠ 0) (hq : Nat.Coprime q k) (he : e ∣ k) :
    ordMod q k ≤ ordMod q e * (k / e) := by
  have : NeZero k := ⟨hk⟩
  have hqe : Nat.Coprime q e := Nat.Coprime.coprime_dvd_right he hq
  have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero hk he
  have hoe : 0 < ordMod q e := ordMod_pos hqe he0
  have hdvd : ordMod q e ∣ ordMod q k := ordMod_dvd_ordMod he
  set u := ZMod.unitOfCoprime q hq
  set v := u ^ ordMod q e
  have hv : orderOf v = ordMod q k / ordMod q e := by
    rw [orderOf_pow_of_dvd hoe.ne' (by rw [← ordMod_eq_orderOf_unit hq]; exact hdvd),
      ← ordMod_eq_orderOf_unit hq]
  -- all powers of `v` are `≡ 1 (mod e)`
  have hmaps : ∀ j ∈ range (orderOf v), ((v ^ j : (ZMod k)ˣ) : ZMod k) ∈
      (univ.filter fun y : ZMod k => ((y.val : ℕ) : ZMod e) = 1) := by
    intro j _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [ZMod.natCast_val, ← ZMod.castHom_apply (h := he)]
    have h1 : (ZMod.castHom he (ZMod e)) ((v ^ j : (ZMod k)ˣ) : ZMod k) = 1 := by
      simp only [v, u, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, map_pow, map_natCast]
      rw [← pow_mul, pow_mul, pow_ordMod, one_pow]
    exact h1
  have hinj : Set.InjOn (fun j : ℕ => ((v ^ j : (ZMod k)ˣ) : ZMod k)) (range (orderOf v)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range] at ha hb
    exact pow_injOn_Iio_orderOf ha hb (Units.ext hab)
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  have hle := hcard.trans (card_congr_one_le he)
  rw [hv] at hle
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, Nat.mul_div_cancel_left _ hoe] at hle
  rw [hm]
  exact Nat.mul_le_mul_left _ hle

theorem ff_le_one (o : ℕ) (ho : 1 ≤ o) : ff o ≤ 1 := by
  have hterm : ∀ d ∈ o.divisors, min (1 / (d : ℚ)) ((d : ℚ) / o) = ((min d (o / d) : ℕ) : ℚ) / o := by
    intro d hd
    have hdo := Nat.dvd_of_mem_divisors hd
    have hdpos : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hopos : (0 : ℚ) < o := by exact_mod_cast ho
    obtain ⟨c, hc⟩ := hdo
    have hc' : o / d = c := by rw [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_mem_divisors hd)]
    rw [hc', Nat.cast_min]
    have hoq : (o : ℚ) = d * c := by exact_mod_cast hc
    rw [hoq] at hopos ⊢
    have hcpos : (0 : ℚ) < c := by
      by_contra h; push Not at h
      have : (d : ℚ) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdpos.le h
      linarith
    rw [← min_div_div_right hopos.le]
    have e1 : (d : ℚ) / (d * c) = 1 / c := by field_simp
    have e2 : (c : ℚ) / (d * c) = 1 / d := by field_simp
    rw [e1, e2, min_comm]
  unfold ff
  rw [Finset.sum_congr rfl hterm]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv, div_le_one (by exact_mod_cast ho)]
  exact_mod_cast sum_min_divisors_le o ho

/-- `f_a(o) ≤ f(o)`: the weights `p^{v_p(d) - a}` are at most `1`. -/
lemma fa_le_ff (q a o : ℕ) : fa q a o ≤ ff o := by
  have hp : (1 : ℚ) ≤ (charOf q : ℚ) := by exact_mod_cast Nat.minFac_pos q
  unfold fa ff
  calc ∑ d ∈ o.divisors.filter (fun d => d.factorization (charOf q) ≤ a),
        (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a *
          min (1 / (d : ℚ)) ((d : ℚ) / o)
      ≤ ∑ d ∈ o.divisors.filter (fun d => d.factorization (charOf q) ≤ a),
          min (1 / (d : ℚ)) ((d : ℚ) / o) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have h0 : 0 ≤ min (1 / (d : ℚ)) ((d : ℚ) / o) := le_min (by positivity) (by positivity)
        have h1 : (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact pow_le_pow_right₀ hp (Finset.mem_filter.mp hd).2
        exact mul_le_of_le_one_left h0 h1
    _ ≤ ∑ d ∈ o.divisors, min (1 / (d : ℚ)) ((d : ℚ) / o) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => le_min (by positivity) (by positivity))

/-! ### Proposition 6.5 (a), `n` odd: the argument by hand -/

/-- `∑_{d ∣ o} min(d, o/d) = ∑_{d ∣ o, d² ≤ o} d + ∑_{d ∣ o, d² < o} d` (as in Lemma 6.2). -/
lemma sum_min_divisors_split (o : ℕ) :
    ∑ d ∈ o.divisors, min d (o / d) =
      ∑ d ∈ o.divisors.filter (fun d => d * d ≤ o), d +
        ∑ d ∈ o.divisors.filter (fun d => d * d < o), d := by
  classical
  have hsplit : ∀ d ∈ o.divisors, min d (o / d) =
      (if d * d ≤ o then d else 0) + (if o < d * d then o / d else 0) := by
    intro d hd
    have hdpos := Nat.pos_of_mem_divisors hd
    by_cases h : d * d ≤ o
    · have : d ≤ o / d := (Nat.le_div_iff_mul_le hdpos).mpr h
      simp [h, not_lt.mpr h, min_eq_left this]
    · push Not at h
      have : o / d < d := (Nat.div_lt_iff_lt_mul hdpos).mpr h
      simp [not_le.mpr h, h, min_eq_right this.le]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hsecond : ∑ d ∈ o.divisors, (if o < d * d then o / d else 0) =
      ∑ d ∈ o.divisors, (if d * d < o then d else 0) := by
    rw [← Nat.sum_div_divisors o (fun d => if d * d < o then d else 0)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have ho0 : o ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hdo := Nat.dvd_of_mem_divisors hd
    have hdpos := Nat.pos_of_mem_divisors hd
    obtain ⟨c, hc⟩ := hdo
    have hc' : o / d = c := by rw [hc, Nat.mul_div_cancel_left _ hdpos]
    rw [hc']
    have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hc; exact ho0 hc)
    have : o < d * d ↔ c * c < o := by
      rw [hc]
      constructor
      · intro h
        nlinarith
      · intro h
        nlinarith
    simp [this]
  rw [hsecond, ← Finset.sum_filter, ← Finset.sum_filter]

/-- A set of odd numbers `≤ m` has sum at most `1 + 3 + ⋯ = ⌈m/2⌉² = ((m+1)/2)²`. -/
lemma sum_odd_le {T : Finset ℕ} {m : ℕ} (h : ∀ d ∈ T, d % 2 = 1 ∧ d ≤ m) :
    ∑ d ∈ T, d ≤ ((m + 1) / 2) ^ 2 := by
  set K := (m + 1) / 2 with hK
  have hsub : T ⊆ (range K).image (fun j => 2 * j + 1) := by
    intro d hd
    obtain ⟨h1, h2⟩ := h d hd
    exact Finset.mem_image.mpr ⟨d / 2, Finset.mem_range.mpr (by omega), by omega⟩
  have hinj : Set.InjOn (fun j => 2 * j + 1) (range K : Set ℕ) := by
    intro x _ y _ hxy
    simp only at hxy
    omega
  have hodd : ∀ k : ℕ, ∑ j ∈ range k, (2 * j + 1) = k ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  calc ∑ d ∈ T, d ≤ ∑ d ∈ (range K).image (fun j => 2 * j + 1), d :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ j ∈ range K, (2 * j + 1) := Finset.sum_image hinj
    _ = K ^ 2 := hodd K

/-- **Proposition 6.5 (a)**, `n` odd, the argument of the paper: for `q = 4` (`p = 2`) and `a = 0`
only odd `d` occur in `f_0(o)`, and `f_0(o) ≤ 2/3` for every `o ≥ 2`. For even `o`, `d ↦ o/d` maps
the odd divisors injectively to even ones with the same value of `min(d, o/d)`, so Lemma 6.2 gives
`f_0(o) ≤ 1/2`. For odd `o` all divisors are odd: if `o = s²` the sum is at most
`2(1 + 3 + ⋯ + (s-2)) + s = (s² + 1)/2`, otherwise at most `2⌈s/2⌉² ≤ (s+1)²/2 ≤ (2/3)(s² + 1)`
for `s = ⌊√o⌋ ≥ 6`, and the odd non-squares below `36` are checked directly. -/
theorem fa_four_zero_le (o : ℕ) (ho : 2 ≤ o) : fa 4 0 o ≤ 2 / 3 := by
  classical
  have hc : charOf 4 = 2 := by decide
  have ho0 : o ≠ 0 := by omega
  -- `o f_0(o) = ∑_{d ∣ o, d odd} min(d, o/d)`
  have hSN : Msmall.SN 2 0 o = ∑ d ∈ o.divisors.filter (fun d => d % 2 = 1), min d (o / d) := by
    unfold Msmall.SN
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    by_cases h2 : d % 2 = 1
    · have : d.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
      simp [this, h2]
    · have : 0 < d.factorization 2 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two hd0 (by omega)
      simp [h2, show ¬ d.factorization 2 ≤ 0 by omega]
  have key : 3 * Msmall.SN 2 0 o ≤ 2 * o := by
    rw [hSN]
    rcases Nat.even_or_odd o with he | hoddo
    · -- `o` even
      have hall := sum_min_divisors_le o (by omega)
      have hsplit := Finset.sum_filter_add_sum_filter_not o.divisors (fun d => d % 2 = 1)
        (fun d => min d (o / d))
      have himg : ∑ d ∈ o.divisors.filter (fun d => d % 2 = 1), min d (o / d) ≤
          ∑ d ∈ o.divisors.filter (fun d => ¬ d % 2 = 1), min d (o / d) := by
        have hinj : Set.InjOn (fun d => o / d) (o.divisors.filter (fun d => d % 2 = 1) : Set ℕ) := by
          intro x hx y hy hxy
          have hx' := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hx).1
          have hy' := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hy).1
          have := congrArg (fun t => o / t) hxy
          simp only at this
          rwa [Nat.div_div_self hx' ho0, Nat.div_div_self hy' ho0] at this
        have e1 : ∑ d ∈ o.divisors.filter (fun d => d % 2 = 1), min d (o / d) =
            ∑ d ∈ (o.divisors.filter (fun d => d % 2 = 1)).image (fun d => o / d),
              min d (o / d) := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun d hd => ?_
          have hdo := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
          rw [Nat.div_div_self hdo ho0, min_comm]
        rw [e1]
        apply Finset.sum_le_sum_of_subset
        intro e he'
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he'
        obtain ⟨hdd, hodd⟩ := Finset.mem_filter.mp hd
        have hdo := Nat.dvd_of_mem_divisors hdd
        refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdo, ho0⟩, ?_⟩
        obtain ⟨c, hc⟩ := hdo
        have hdpos : 0 < d := Nat.pos_of_mem_divisors hdd
        have hcd : o / d = c := by rw [hc, Nat.mul_div_cancel_left _ hdpos]
        rw [hcd]
        intro hc1
        have h1 : o % 2 = 1 := by rw [hc, Nat.mul_mod, hodd, hc1]
        obtain ⟨k, hk⟩ := he
        omega
      omega
    · -- `o` odd: all divisors are odd
      have hodd' : ∀ d ∈ o.divisors, d % 2 = 1 := by
        intro d hd
        obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors hd
        by_contra h
        have h2 : 2 ∣ d := by omega
        have h3 : 2 ∣ o := hc ▸ Dvd.dvd.mul_right h2 c
        obtain ⟨k, hk⟩ := hoddo
        omega
      have hfilt : o.divisors.filter (fun d => d % 2 = 1) = o.divisors :=
        Finset.filter_true_of_mem hodd'
      rw [hfilt, sum_min_divisors_split o]
      have hsq_le : Nat.sqrt o * Nat.sqrt o ≤ o := Nat.sqrt_le o
      have hlt_sq : o < (Nat.sqrt o + 1) * (Nat.sqrt o + 1) := Nat.lt_succ_sqrt o
      have hle_s : ∀ d, d * d ≤ o → d ≤ Nat.sqrt o := fun d h => Nat.le_sqrt.mpr h
      by_cases hsq : Nat.sqrt o * Nat.sqrt o = o
      · -- `o = s²`, `s ≥ 3` odd
        set s := Nat.sqrt o with hs
        have hs3 : 2 ≤ s := by
          by_contra h; push Not at h
          interval_cases s <;> omega
        have hsodd : s % 2 = 1 := by
          by_contra h
          have : 2 ∣ s := by omega
          have : 2 ∣ o := hsq ▸ Dvd.dvd.mul_right this s
          obtain ⟨k, hk⟩ := hoddo
          omega
        have hB : ∑ d ∈ o.divisors.filter (fun d => d * d < o), d ≤ ((s - 1 + 1) / 2) ^ 2 := by
          apply sum_odd_le
          intro d hd
          obtain ⟨hdd, hlt⟩ := Finset.mem_filter.mp hd
          refine ⟨hodd' d hdd, ?_⟩
          have : d < s := by
            by_contra h; push Not at h
            have : s * s ≤ d * d := Nat.mul_le_mul h h
            omega
          omega
        have hA : ∑ d ∈ o.divisors.filter (fun d => d * d ≤ o), d ≤
            s + ∑ d ∈ o.divisors.filter (fun d => d * d < o), d := by
          have hsub : o.divisors.filter (fun d => d * d ≤ o) ⊆
              insert s (o.divisors.filter (fun d => d * d < o)) := by
            intro d hd
            obtain ⟨hdd, hle⟩ := Finset.mem_filter.mp hd
            rcases Nat.lt_or_ge (d * d) o with h | h
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hdd, h⟩)
            · have hdo : d * d = o := le_antisymm hle h
              have hds : d = s := by
                apply le_antisymm (hle_s d hle)
                by_contra hc; push Not at hc
                have : (d + 1) * (d + 1) ≤ s * s := Nat.mul_le_mul hc hc
                nlinarith
              exact hds ▸ Finset.mem_insert_self _ _
          calc ∑ d ∈ o.divisors.filter (fun d => d * d ≤ o), d
              ≤ ∑ d ∈ insert s (o.divisors.filter (fun d => d * d < o)), d :=
                Finset.sum_le_sum_of_subset hsub
            _ ≤ s + ∑ d ∈ o.divisors.filter (fun d => d * d < o), d := by
                by_cases hm : s ∈ o.divisors.filter (fun d => d * d < o)
                · rw [Finset.insert_eq_of_mem hm]; omega
                · rw [Finset.sum_insert hm]
        obtain ⟨t, ht⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
        have hK : (s - 1 + 1) / 2 = t := by omega
        rw [hK] at hB
        have ho' : o = (2 * t + 1) * (2 * t + 1) := by rw [← ht, hsq]
        have ht1 : 1 ≤ t := by omega
        nlinarith
      · by_cases hsmall : o < 36
        · -- the odd non-squares below `36`
          have hmem : o ∈ ([3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 27, 29, 31, 33, 35] : List ℕ) := by
            obtain ⟨k, hk⟩ := hoddo
            interval_cases o <;> first
              | omega
              | (exfalso; apply hsq; rw [show (9 : ℕ) = 3 * 3 by norm_num, Nat.sqrt_eq])
              | (exfalso; apply hsq; rw [show (25 : ℕ) = 5 * 5 by norm_num, Nat.sqrt_eq])
              | simp
          have hcheck : ∀ o ∈ ([3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 27, 29, 31, 33, 35] : List ℕ),
              3 * (∑ d ∈ o.divisors.filter (fun d => d * d ≤ o), d +
                ∑ d ∈ o.divisors.filter (fun d => d * d < o), d) ≤ 2 * o := by decide
          exact hcheck o hmem
        · -- `o` not a square, `s = ⌊√o⌋ ≥ 6`
          set s := Nat.sqrt o with hs
          have hs6 : 6 ≤ s := Nat.le_sqrt.mpr (by omega)
          have hosq : s * s + 1 ≤ o := by omega
          have hA : ∑ d ∈ o.divisors.filter (fun d => d * d ≤ o), d ≤ ((s + 1) / 2) ^ 2 :=
            sum_odd_le fun d hd => ⟨hodd' d (Finset.mem_filter.mp hd).1,
              hle_s d (Finset.mem_filter.mp hd).2⟩
          have hB : ∑ d ∈ o.divisors.filter (fun d => d * d < o), d ≤ ((s + 1) / 2) ^ 2 :=
            sum_odd_le fun d hd => ⟨hodd' d (Finset.mem_filter.mp hd).1,
              hle_s d (Finset.mem_filter.mp hd).2.le⟩
          have hK : 2 * ((s + 1) / 2) ≤ s + 1 := Nat.mul_div_le (s + 1) 2
          set K := (s + 1) / 2
          have h4K : 4 * K ^ 2 ≤ (s + 1) ^ 2 := by nlinarith
          nlinarith
  change Msmall.faX (charOf 4) 0 o ≤ 2 / 3
  rw [hc, Msmall.faX_eq_SN (by norm_num) 0 (by omega)]
  have ho' : (0 : ℚ) < o := by exact_mod_cast (show 0 < o by omega)
  rw [pow_zero, mul_one, div_le_iff₀ ho']
  have : ((3 * Msmall.SN 2 0 o : ℕ) : ℚ) ≤ ((2 * o : ℕ) : ℚ) := by exact_mod_cast key
  push_cast at this
  linarith

end MorganMullen

namespace MorganMullen
namespace Model
open Finset

variable {q n : ℕ} [NeZero n]

lemma exists_dfree_mul_eq {d : ℕ} (hd : d ∣ n) {y : ZMod (nfree q n)}
    (hy : ((bigN q n d : ℕ) : ZMod (nfree q n)) * y = 0) :
    ∃ i : ZMod (nfree q n), ((dfree q d : ℕ) : ZMod _) * i = y := by
  have hdN := dfree_mul_bigN (q := q) hd
  have hdpos : 0 < dfree q d := dfree_pos (ne_zero_of_dvd_ne_zero (NeZero.ne n) hd)
  have h0 : ((bigN q n d * y.val : ℕ) : ZMod (nfree q n)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact hy
  rw [ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨c, hc⟩ := h0
  have hNpos : 0 < bigN q n d := bigN_pos hd
  have hc' : bigN q n d * y.val = bigN q n d * (dfree q d * c) := by
    rw [hc, ← hdN]; ring
  have : y.val = dfree q d * c := Nat.eq_of_mul_eq_mul_left hNpos hc'
  exact ⟨c, by rw [← Nat.cast_mul, ← this, ZMod.natCast_zmod_val]⟩

lemma card_fibre_single {d : ℕ} (hd : d ∣ n) (i : ZMod (nfree q n)) :
    (univ.filter fun i' : ZMod (nfree q n) =>
        ((dfree q d : ℕ) : ZMod _) * i' = ((dfree q d : ℕ) : ZMod _) * i).card = dfree q d := by
  rw [fibre_coset hd i, Finset.card_image_of_injOn, Finset.card_range]
  intro t ht t' ht' htt
  simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
  simp only [add_right_inj] at htt
  have hdN := dfree_mul_bigN (q := q) hd
  rw [ZMod.natCast_eq_natCast_iff'] at htt
  have hNpos : 0 < bigN q n d := bigN_pos hd
  have h1 : t * bigN q n d < nfree q n := by
    rw [← hdN]; exact Nat.mul_lt_mul_of_pos_right ht hNpos
  have h2 : t' * bigN q n d < nfree q n := by
    rw [← hdN]; exact Nat.mul_lt_mul_of_pos_right ht' hNpos
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at htt
  exact Nat.eq_of_mul_eq_mul_right hNpos htt

lemma addOrderOf_dvd_bigN_of_mul {d : ℕ} (hd : d ∣ n) (i : ZMod (nfree q n)) :
    addOrderOf (((dfree q d : ℕ) : ZMod (nfree q n)) * i) ∣ bigN q n d := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← natCast_mul_eq_nsmul, ← mul_assoc, ← Nat.cast_mul,
    mul_comm (bigN q n d), dfree_mul_bigN hd, ZMod.natCast_self, zero_mul]

lemma card_ed_eq {d : ℕ} (hd : d ∣ n) {e : ℕ} (he : e ∣ bigN q n d) :
    (univ.filter fun i : ZMod (nfree q n) => ed q n d i = e).card = dfree q d * Nat.totient e := by
  have hen : e ∣ nfree q n := he.trans (Dvd.intro_left _ (dfree_mul_bigN hd))
  set Y : Finset (ZMod (nfree q n)) := univ.filter fun y => addOrderOf y = e
  have hY : Y.card = Nat.totient e := by
    have := IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod (nfree q n)) (d := e)
      (by rw [ZMod.card]; exact hen)
    simpa [Y] using this
  rw [Finset.card_eq_sum_card_fiberwise (f := fun i : ZMod (nfree q n) => ((dfree q d : ℕ) : ZMod _) * i)
    (t := Y)]
  · rw [Finset.sum_congr rfl (g := fun _ => dfree q d), Finset.sum_const, smul_eq_mul, hY, mul_comm]
    intro y hy
    have hyo : addOrderOf y = e := by simpa [Y] using hy
    have hNy : ((bigN q n d : ℕ) : ZMod (nfree q n)) * y = 0 := by
      rw [natCast_mul_eq_nsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero, hyo]; exact he
    obtain ⟨i0, hi0⟩ := exists_dfree_mul_eq hd hNy
    refine Eq.trans ?_ (card_fibre_single hd i0)
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; rw [h, hi0]
    · intro h
      refine ⟨?_, by rw [h, hi0]⟩
      show addOrderOf (((dfree q d : ℕ) : ZMod _) * i) = e
      rw [h, hi0, hyo]
  · intro i hi
    have := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
    simpa [Y, ed] using this



end Model
end MorganMullen

namespace MorganMullen
namespace Model
open Finset
variable {q n : ℕ} [NeZero n]

lemma ed_mem_divisors (d : ℕ) (i : ZMod (nfree q n)) : ed q n d i ∈ (nfree q n).divisors :=
  Nat.mem_divisors.mpr ⟨addOrderOf_dvd_nfree _, NeZero.ne _⟩

lemma card_ed_eq_zero {d : ℕ} (hd : d ∣ n) {e : ℕ} (he : ¬ e ∣ bigN q n d) :
    (univ.filter fun i : ZMod (nfree q n) => ed q n d i = e).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ h
  exact he (h ▸ addOrderOf_dvd_bigN_of_mul hd i)

lemma chr_pow_dval_mul_dfree (d : ℕ) : (chr q) ^ dval q d * dfree q d = d := pow_mul_pfree _ _

/-- **Lemma 6.1**, first identity: `M = ∑_{η ∈ μ_{n'}} ρ(η)`. -/
theorem numM_eq_sum_rho (hq : IsPrimePow q) : (numM q n : ℚ) = ∑ i, rho q n i := by
  classical
  rw [numM_eq hq, Nat.cast_sum]
  have hnu : ∀ de ∈ essTypes q n, (nu q de.1 de.2 : ℚ) =
      de.1 * Nat.totient de.2 / ordMod q de.2 := by
    intro de hde
    have h := nu_mul hq hde
    obtain ⟨-, he, -, -⟩ := mem_essTypes.mp hde
    have hpos : (0 : ℚ) < ordMod q de.2 := by
      exact_mod_cast ordMod_pos (coprime_q_of_dvd_nfree hq (NeZero.ne n) (Nat.dvd_of_mem_divisors he))
        (Nat.pos_of_mem_divisors he).ne'
    rw [eq_div_iff hpos.ne']; exact_mod_cast h
  rw [Finset.sum_congr rfl hnu]
  -- rewrite the left side as a double sum over divisors
  have hL : ∑ de ∈ essTypes q n, (de.1 : ℚ) * Nat.totient de.2 / ordMod q de.2 =
      ∑ d ∈ n.divisors, ∑ e ∈ (nfree q n).divisors,
        if e ∣ bigN q n d ∧ d ∣ ordMod q e then (d : ℚ) * Nat.totient e / ordMod q e else 0 := by
    rw [essTypes, Finset.sum_filter, Finset.sum_product]
  rw [hL]
  unfold rho
  simp_rw [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun (d : ℕ) (hd : d ∈ n.divisors) => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  -- right side: group by e = ed d i
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := (nfree q n).divisors)
    (g := fun i => ed q n d i) (fun i _ => ed_mem_divisors d i)
    (fun i => if ValidAt q n d i then ((chr q : ℚ) ^ dval q d) / ordMod q (ed q n d i) else 0)]
  refine Finset.sum_congr rfl fun e he => ?_
  have hterm : ∀ i ∈ (univ.filter fun i : ZMod (nfree q n) => ed q n d i = e),
      (if ValidAt q n d i then ((chr q : ℚ) ^ dval q d) / ordMod q (ed q n d i) else 0) =
      if d ∣ ordMod q e then ((chr q : ℚ) ^ dval q d) / ordMod q e else 0 := by
    intro i hi
    have hie : ed q n d i = e := (Finset.mem_filter.mp hi).2
    simp only [ValidAt, hie, hdn, true_and]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  by_cases heN : e ∣ bigN q n d
  · rw [card_ed_eq hdn heN]
    by_cases hdo : d ∣ ordMod q e
    · simp only [heN, hdo, and_self, ite_true]
      push_cast
      conv_lhs => rw [← chr_pow_dval_mul_dfree (q := q) d]
      push_cast; ring
    · simp [hdo]
  · rw [card_ed_eq_zero hdn heN]; simp [heN]

/-- **Lemma 6.1**, second identity: `S = ∑_{η ∈ μ_{n'}} s(η)` (the total weight `ν_{d,e} q^{-ord_e(q)}`
of the conditions of each essential type `(d, e)` with `ord_e(q) ≥ 2`, distributed over `μ_{n'}` as for `M`). -/
theorem sumS_eq_sum_sEta (hq : IsPrimePow q) : sumS q n = ∑ i, sEta q n i := by
  classical
  rw [sumS_eq hq, Finset.sum_filter]
  have hnu : ∀ de ∈ essTypes q n,
      (if 2 ≤ ordMod q de.2 then (nu q de.1 de.2 : ℚ) * ((q : ℚ) ^ ordMod q de.2)⁻¹ else 0) =
      if 2 ≤ ordMod q de.2 then
        (de.1 : ℚ) * Nat.totient de.2 / ordMod q de.2 * ((q : ℚ) ^ ordMod q de.2)⁻¹ else 0 := by
    intro de hde
    have h := nu_mul hq hde
    obtain ⟨-, he, -, -⟩ := mem_essTypes.mp hde
    have hpos : (0 : ℚ) < ordMod q de.2 := by
      exact_mod_cast ordMod_pos (coprime_q_of_dvd_nfree hq (NeZero.ne n) (Nat.dvd_of_mem_divisors he))
        (Nat.pos_of_mem_divisors he).ne'
    have e : (nu q de.1 de.2 : ℚ) = de.1 * Nat.totient de.2 / ordMod q de.2 := by
      rw [eq_div_iff hpos.ne']; exact_mod_cast h
    rw [e]
  rw [Finset.sum_congr rfl hnu]
  have hL : ∑ de ∈ essTypes q n, (if 2 ≤ ordMod q de.2 then
        (de.1 : ℚ) * Nat.totient de.2 / ordMod q de.2 * ((q : ℚ) ^ ordMod q de.2)⁻¹ else 0) =
      ∑ d ∈ n.divisors, ∑ e ∈ (nfree q n).divisors,
        if e ∣ bigN q n d ∧ d ∣ ordMod q e then
          (if 2 ≤ ordMod q e then (d : ℚ) * Nat.totient e / ordMod q e * ((q : ℚ) ^ ordMod q e)⁻¹
            else 0) else 0 := by
    rw [essTypes, Finset.sum_filter, Finset.sum_product]
  rw [hL]
  unfold sEta
  simp_rw [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun (d : ℕ) (hd : d ∈ n.divisors) => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := (nfree q n).divisors)
    (g := fun i => ed q n d i) (fun i _ => ed_mem_divisors d i)
    (fun i => if ValidAt q n d i ∧ 2 ≤ ordMod q (ed q n d i) then
      (chr q : ℚ) ^ dval q d / ordMod q (ed q n d i) * ((q : ℚ) ^ ordMod q (ed q n d i))⁻¹ else 0)]
  refine Finset.sum_congr rfl fun e he => ?_
  have hterm : ∀ i ∈ (univ.filter fun i : ZMod (nfree q n) => ed q n d i = e),
      (if ValidAt q n d i ∧ 2 ≤ ordMod q (ed q n d i) then
        (chr q : ℚ) ^ dval q d / ordMod q (ed q n d i) * ((q : ℚ) ^ ordMod q (ed q n d i))⁻¹
        else 0) =
      if d ∣ ordMod q e ∧ 2 ≤ ordMod q e then
        (chr q : ℚ) ^ dval q d / ordMod q e * ((q : ℚ) ^ ordMod q e)⁻¹ else 0 := by
    intro i hi
    have hie : ed q n d i = e := (Finset.mem_filter.mp hi).2
    simp only [ValidAt, hie, hdn, true_and]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  by_cases heN : e ∣ bigN q n d
  · rw [card_ed_eq hdn heN]
    by_cases hdo : d ∣ ordMod q e ∧ 2 ≤ ordMod q e
    · obtain ⟨h1, h2⟩ := hdo
      simp only [heN, h1, h2, and_self, ↓reduceIte]
      push_cast
      conv_lhs => rw [← chr_pow_dval_mul_dfree (q := q) d]
      push_cast; ring
    · rw [ite_eq_right hdo, mul_zero]
      rcases not_and_or.mp hdo with h | h <;> simp [h]
  · rw [card_ed_eq_zero hdn heN]; simp [heN]

lemma ed_eq (d : ℕ) (hd : d ≠ 0) (i : ZMod (nfree q n)) :
    ed q n d i = addOrderOf i / Nat.gcd (addOrderOf i) (dfree q d) := by
  unfold ed
  rw [natCast_mul_eq_nsmul, addOrderOf_nsmul' _ (dfree_pos (q := q) hd).ne']

lemma chr_pos' : 0 < chr q := chr_pos q

lemma factorization_le_of_dvd {d m : ℕ} (hd : d ∣ m) (hm : m ≠ 0) (p : ℕ) :
    d.factorization p ≤ m.factorization p :=
  (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hm hd) hm).mpr hd p

/-- **Proposition 6.3**, local part. -/
theorem rho_le (hq : IsPrimePow q) (i : ZMod (nfree q n)) :
    rho q n i / (chr q : ℚ) ^ a q n ≤ Ra q (a q n) (addOrderOf i) ∧
      Ra q (a q n) (addOrderOf i) ≤
        min (RaStar q (a q n) (tcodim q n i)) (fa q (a q n) (tcodim q n i)) ∧
      fa q (a q n) (tcodim q n i) ≤ ff (tcodim q n i) ∧ ff (tcodim q n i) ≤ 1 := by
  classical
  set k := addOrderOf i with hk
  set o := tcodim q n i with ho
  have hkpos : 0 < k := addOrderOf_pos' i
  have hcop : Nat.Coprime q k := coprime_q_addOrderOf hq i
  have ho1 : 1 ≤ o := one_le_tcodim hq i
  have hoeq : o = ordMod q k := rfl
  have hp : 0 < (chr q : ℚ) := by exact_mod_cast chr_pos q
  have hpa : 0 < (chr q : ℚ) ^ a q n := pow_pos hp _
  -- general facts about the terms
  have ho_e : ∀ d, d ≠ 0 → 0 < ordMod q (k / Nat.gcd k (pfree (charOf q) d)) := by
    intro d hd
    have hdvd : k / Nat.gcd k (pfree (charOf q) d) ∣ k := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    exact ordMod_pos (Nat.Coprime.coprime_dvd_right hdvd hcop)
      (Nat.pos_of_ne_zero (fun h => by
        rw [h] at hdvd; exact absurd (Nat.eq_zero_of_zero_dvd hdvd) hkpos.ne')).ne'
  set F : ℕ → ℚ := fun d => (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a q n /
    ordMod q (k / Nat.gcd k (pfree (charOf q) d)) with hF
  have hFnn : ∀ d, d ≠ 0 → 0 ≤ F d := by
    intro d hd
    have := ho_e d hd
    simp only [hF]
    positivity
  -- the inequality `1/ord_e(q) ≤ min(1/d, d/o)` for the terms of `R_a`
  have hkey : ∀ d, d ≠ 0 → d ∣ ordMod q (k / Nat.gcd k (pfree (charOf q) d)) →
      (1 : ℚ) / ordMod q (k / Nat.gcd k (pfree (charOf q) d)) ≤ min (1 / (d : ℚ)) ((d : ℚ) / o) := by
    intro d hd hdo
    set g := Nat.gcd k (pfree (charOf q) d)
    set e := k / g
    have hoe := ho_e d hd
    have hdle : d ≤ ordMod q e := Nat.le_of_dvd hoe hdo
    have hge : g * e = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hedvd : e ∣ k := Dvd.intro_left g hge
    have hke : k / e = g := by
      rw [← hge, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hge; omega)]
    have hK := ordMod_le_mul_div hkpos.ne' hcop hedvd
    rw [hke] at hK
    have hgd : g ≤ d := (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) ((Nat.gcd_dvd_right _ _).trans
      (pfree_dvd _ _)))
    have hod : o ≤ ordMod q e * d := hK.trans (Nat.mul_le_mul_left _ hgd)
    have hoepos : (0 : ℚ) < ordMod q e := by exact_mod_cast hoe
    have hdpos : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hopos : (0 : ℚ) < o := by exact_mod_cast ho1
    refine le_min ?_ ?_
    · exact one_div_le_one_div_of_le hdpos (by exact_mod_cast hdle)
    · rw [div_le_div_iff₀ hoepos hopos, one_mul]
      have : (o : ℚ) ≤ ordMod q e * d := by exact_mod_cast hod
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ρ(η)/p^a ≤ R_a(k)
    calc rho q n i / (chr q : ℚ) ^ a q n
        = ∑ d ∈ n.divisors.filter (fun d => ValidAt q n d i), F d := by
          unfold rho
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun d hd => ?_
          have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1).ne'
          simp only [hF, ed_eq d hd0]
          rw [← hk]
          unfold dval dfree chr
          ring
      _ ≤ ∑ d ∈ (ordMod q k).divisors.filter (fun d => d.factorization (charOf q) ≤ a q n ∧
            d ∣ ordMod q (k / Nat.gcd k (pfree (charOf q) d))), F d := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            obtain ⟨hdn, hval⟩ := Finset.mem_filter.mp hd
            obtain ⟨hdn', hdo⟩ := hval
            have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hdn).ne'
            rw [ed_eq d hd0] at hdo
            refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, (ordMod_pos hcop hkpos.ne').ne'⟩,
              factorization_le_of_dvd hdn' (NeZero.ne n) _, hdo⟩
            exact hdo.trans (ordMod_dvd_ordMod (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
          · intro d hd _
            exact hFnn d (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1).ne'
      _ = Ra q (a q n) k := rfl
  · refine le_min ?_ ?_
    · -- R_a(k) ≤ R*_a(o)
      unfold RaStar
      rw [Finset.le_fold_max]
      right
      refine ⟨k, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, ?_⟩, rfl⟩, le_rfl⟩
      · have h1 : 1 ≤ q ^ o := Nat.one_le_pow _ _ hq.pos
        have := (ordMod_dvd_iff_modEq (q := q) (e := k) (k := o)).mp dvd_rfl
        exact (Nat.modEq_iff_dvd' h1).mp this.symm
      · have : 1 < q ^ o := Nat.one_lt_pow (by omega) hq.one_lt
        omega
    · -- R_a(k) ≤ f_a(o)
      unfold Ra fa
      calc ∑ d ∈ (ordMod q k).divisors.filter (fun d => d.factorization (charOf q) ≤ a q n ∧
              d ∣ ordMod q (k / Nat.gcd k (pfree (charOf q) d))),
            (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a q n /
              ordMod q (k / Nat.gcd k (pfree (charOf q) d))
          ≤ ∑ d ∈ (ordMod q k).divisors.filter (fun d => d.factorization (charOf q) ≤ a q n ∧
              d ∣ ordMod q (k / Nat.gcd k (pfree (charOf q) d))),
            (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a q n *
              min (1 / (d : ℚ)) ((d : ℚ) / o) := by
            refine Finset.sum_le_sum fun d hd => ?_
            obtain ⟨hdk, -, hdo⟩ := Finset.mem_filter.mp hd
            have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hdk).ne'
            rw [div_eq_mul_one_div _ ((ordMod q _ : ℕ) : ℚ)]
            exact mul_le_mul_of_nonneg_left (hkey d hd0 hdo) (by positivity)
        _ ≤ ∑ d ∈ o.divisors.filter (fun d => d.factorization (charOf q) ≤ a q n),
            (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a q n *
              min (1 / (d : ℚ)) ((d : ℚ) / o) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro d hd
              obtain ⟨hdk, hv, -⟩ := Finset.mem_filter.mp hd
              exact Finset.mem_filter.mpr ⟨hdk, hv⟩
            · intro d hd _
              have hd0 : (0 : ℚ) < d := by
                exact_mod_cast Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
              have : (0 : ℚ) < o := by exact_mod_cast ho1
              positivity
  · -- f_a(o) ≤ f(o)
    unfold fa ff
    calc ∑ d ∈ o.divisors.filter (fun d => d.factorization (charOf q) ≤ a q n),
          (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a q n *
            min (1 / (d : ℚ)) ((d : ℚ) / o)
        ≤ ∑ d ∈ o.divisors.filter (fun d => d.factorization (charOf q) ≤ a q n),
            min (1 / (d : ℚ)) ((d : ℚ) / o) := by
          refine Finset.sum_le_sum fun d hd => ?_
          obtain ⟨hdk, hv⟩ := Finset.mem_filter.mp hd
          have hd0 : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hdk
          have hopos : (0 : ℚ) < o := by exact_mod_cast ho1
          have hmin : 0 ≤ min (1 / (d : ℚ)) ((d : ℚ) / o) := by positivity
          have hle : (charOf q : ℚ) ^ d.factorization (charOf q) / (charOf q : ℚ) ^ a q n ≤ 1 := by
            rw [div_le_one hpa]
            exact pow_le_pow_right₀ (by exact_mod_cast chr_pos q) hv
          calc _ ≤ 1 * min (1 / (d : ℚ)) ((d : ℚ) / o) := mul_le_mul_of_nonneg_right hle hmin
            _ = _ := one_mul _
      _ ≤ ∑ d ∈ o.divisors, min (1 / (d : ℚ)) ((d : ℚ) / o) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro d hd _
          have hd0 : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
          have hopos : (0 : ℚ) < o := by exact_mod_cast ho1
          positivity
  · exact ff_le_one o ho1

/-- `p^a n' = n`. -/
lemma pa_mul_nfree' : (chr q : ℚ) ^ a q n * (nfree q n : ℚ) = n := by
  have := pa_mul_nfree q n
  unfold pa at this
  exact_mod_cast this

/-- **Proposition 6.3**, global part: `M ≤ p^a ∑_η min(R*_a(o_η), f_a(o_η)) ≤ n`. -/
theorem numM_le_sum_min (hq : IsPrimePow q) :
    (numM q n : ℚ) ≤ (chr q : ℚ) ^ a q n *
        ∑ i, min (RaStar q (a q n) (tcodim q n i)) (fa q (a q n) (tcodim q n i)) ∧
      (chr q : ℚ) ^ a q n *
        ∑ i, min (RaStar q (a q n) (tcodim q n i)) (fa q (a q n) (tcodim q n i)) ≤ n := by
  have hp : 0 < (chr q : ℚ) := by exact_mod_cast chr_pos q
  have hpa : 0 < (chr q : ℚ) ^ a q n := pow_pos hp _
  constructor
  · rw [numM_eq_sum_rho hq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h1, h2, -, -⟩ := rho_le hq i
    have := h1.trans h2
    rw [div_le_iff₀ hpa] at this
    linarith [mul_comm ((chr q : ℚ) ^ a q n) (min (RaStar q (a q n) (tcodim q n i)) (fa q (a q n) (tcodim q n i)))]
  · calc (chr q : ℚ) ^ a q n *
          ∑ i, min (RaStar q (a q n) (tcodim q n i)) (fa q (a q n) (tcodim q n i))
        ≤ (chr q : ℚ) ^ a q n * ∑ _i : ZMod (nfree q n), (1 : ℚ) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hpa.le
          obtain ⟨-, -, h3, h4⟩ := rho_le hq i
          exact (min_le_right _ _).trans (h3.trans h4)
      _ = n := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
          exact pa_mul_nfree'

/-- **Corollary 6.4**: `M ≤ n`. -/
theorem numM_le_n (hq : IsPrimePow q) : numM q n ≤ n := by
  have ⟨h1, h2⟩ := numM_le_sum_min (n := n) hq
  exact_mod_cast h1.trans h2

/-- **Proposition 6.3**, last part. -/
theorem numM_le_of_T (hq : IsPrimePow q) (T : Finset ℕ) (ϑ Θ : ℚ)
    (hϑΘ : ϑ ≤ Θ)
    (hout : ∀ o, 1 ≤ o → o ∉ T → min (RaStar q (a q n) o) (fa q (a q n) o) ≤ ϑ)
    (hin : ∀ o ∈ T, min (RaStar q (a q n) o) (fa q (a q n) o) ≤ Θ) :
    (numM q n : ℚ) ≤ ϑ * n + (Θ - ϑ) * (chr q : ℚ) ^ a q n *
      (Nat.gcd (nfree q n) (q ^ (T.lcm id) - 1) : ℚ) := by
  classical
  have hp : 0 < (chr q : ℚ) := by exact_mod_cast chr_pos q
  have hpa : 0 < (chr q : ℚ) ^ a q n := pow_pos hp _
  set ℓ := T.lcm id
  set U : Finset (ZMod (nfree q n)) := univ.filter fun i => tcodim q n i ∈ T
  -- the elements with `o_η ∈ T` are killed by `q^ℓ - 1`
  have hU : (U.card : ℚ) ≤ Nat.gcd (nfree q n) (q ^ ℓ - 1) := by
    set g := Nat.gcd (nfree q n) (q ^ ℓ - 1)
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))
    have hsub : U ⊆ univ.filter fun i : ZMod (nfree q n) => g • i = 0 := by
      intro i hi
      have hiT : tcodim q n i ∈ T := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
      refine Nat.dvd_gcd (addOrderOf_dvd_nfree i) ?_
      have hdvd : tcodim q n i ∣ ℓ := Finset.dvd_lcm hiT
      have h1 : (q : ZMod (nfree q n)) ^ ℓ * i = i := (qpow_mul_eq_self_iff hq ℓ i).mpr hdvd
      have hq1 : 1 ≤ q ^ ℓ := Nat.one_le_pow _ _ hq.pos
      rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← natCast_mul_eq_nsmul, Nat.cast_sub hq1, sub_mul,
        Nat.cast_pow, h1, Nat.cast_one, one_mul, sub_self]
    have := (Finset.card_le_card hsub).trans
      (IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod (nfree q n)) hgpos)
    exact_mod_cast this
  have hsum : ∑ i, min (RaStar q (a q n) (tcodim q n i)) (fa q (a q n) (tcodim q n i)) ≤
      ϑ * nfree q n + (Θ - ϑ) * U.card := by
    calc ∑ i, min (RaStar q (a q n) (tcodim q n i)) (fa q (a q n) (tcodim q n i))
        ≤ ∑ i : ZMod (nfree q n), (if tcodim q n i ∈ T then Θ else ϑ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          split_ifs with h
          · exact hin _ h
          · exact hout _ (one_le_tcodim hq i) h
      _ = ∑ i : ZMod (nfree q n), (ϑ + if tcodim q n i ∈ T then Θ - ϑ else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> ring
      _ = ϑ * nfree q n + (Θ - ϑ) * U.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
            ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          ring
  have hmain := (numM_le_sum_min (n := n) hq).1
  have hΘϑ : 0 ≤ Θ - ϑ := by linarith
  calc (numM q n : ℚ)
      ≤ (chr q : ℚ) ^ a q n * (ϑ * nfree q n + (Θ - ϑ) * U.card) :=
        hmain.trans (mul_le_mul_of_nonneg_left hsum hpa.le)
    _ ≤ (chr q : ℚ) ^ a q n * (ϑ * nfree q n + (Θ - ϑ) * Nat.gcd (nfree q n) (q ^ ℓ - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hpa.le
        have := mul_le_mul_of_nonneg_left hU hΘϑ
        linarith
    _ = ϑ * n + (Θ - ϑ) * (chr q : ℚ) ^ a q n * (Nat.gcd (nfree q n) (q ^ ℓ - 1) : ℚ) := by
        rw [← pa_mul_nfree' (q := q) (n := n)]; ring



/-! ### Proposition 6.5

`fa`, `RaStar` are `Msmall.faX`, `Msmall.RaStarX` (`Sec6FaBound.lean`, `Sec6Comp.lean`) with
`p = charOf q`. The bounds for `f_a(o)` and `R*_a(o)` are those of the proof of Proposition 6.5 in
the paper (finite computations in `Sec6Runs.lean`, tail bounds with `κ_3`, `κ_4` in
`Sec6FaBound.lean`), and Proposition 6.3 (`numM_le_of_T`) is applied with the same `T`, `ϑ`, `Θ`:

* `q = 4`: `n` even: `T = ∅`, `ϑ = Θ = 3/4`; `n` odd: `T = {1}`, `ϑ = 2/3`, `Θ = 1`
  (`f_0(o) ≤ 2/3` by hand, `fa_four_zero_le`);
* `q = 3`: `3 ∣ n`: `T = ∅`, `ϑ = Θ = 0.5983`; `3 ∤ n`: `T = {1,2,4,8}`, `ϑ = 0.6`, `Θ = 1`;
* `q = 2`: the table of the proof of Proposition 6.5 (c):
  `a = 0`: `T = {1,2,3,6}`, `ϑ = 0.4`, `Θ = 1`; `a = 1`: `T = {1,2,6}`, `ϑ = 0.375`, `Θ = 3/4`;
  `a = 2`: `T = {4}`, `ϑ = 0.375`, `Θ = 7/16`; `a ≥ 3`: `T = ∅`, `ϑ = 0.35`.
-/

lemma fa_eq_faX (q a o : ℕ) : fa q a o = Msmall.faX (charOf q) a o := rfl

lemma RaStar_eq_RaStarX (q a o : ℕ) : RaStar q a o = Msmall.RaStarX (charOf q) q a o := rfl

/-- **Proposition 6.5 (a)**: `q = 4`: `M ≤ 3n/4` for `n` even. -/
theorem numM_le_q4_even (hn : 2 ∣ n) : (numM 4 n : ℚ) ≤ 3 / 4 * n := by
  have hq : IsPrimePow 4 := ⟨2, 2, Nat.prime_two.prime, by norm_num, by norm_num⟩
  have hc : charOf 4 = 2 := by decide
  have ha : 1 ≤ a 4 n := by
    show 1 ≤ n.factorization (charOf 4)
    rw [hc]; exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two (NeZero.ne n) hn
  have h := numM_le_of_T (n := n) hq ∅ (3 / 4) (3 / 4) le_rfl
    (fun o ho _ => by
      rw [fa_eq_faX, hc]
      exact (min_le_right _ _).trans (Msmall.fQ4A1 o ho _ ha))
    (fun o ho => absurd ho (Finset.notMem_empty o))
  simpa using h

/-- **Proposition 6.5 (a)**: `q = 4`: `M ≤ 2n/3 + 1` for `n` odd. -/
theorem numM_le_q4_odd (hn : ¬ 2 ∣ n) : (numM 4 n : ℚ) ≤ 2 / 3 * n + 1 := by
  have hq : IsPrimePow 4 := ⟨2, 2, Nat.prime_two.prime, by norm_num, by norm_num⟩
  have hc : charOf 4 = 2 := by decide
  have ha : a 4 n = 0 := by
    show n.factorization (charOf 4) = 0
    rw [hc]; exact Nat.factorization_eq_zero_of_not_dvd hn
  have h := numM_le_of_T (n := n) hq {1} (2 / 3) 1 (by norm_num)
    (fun o ho hoT => by
      rw [ha]
      have : 1 < o := by simp at hoT; omega
      exact (min_le_right _ _).trans (fa_four_zero_le o this))
    (fun o hoT => by
      simp only [Finset.mem_singleton] at hoT
      subst hoT
      exact (min_le_right _ _).trans ((fa_le_ff _ _ _).trans (ff_le_one 1 le_rfl)))
  have hl : ({1} : Finset ℕ).lcm id = 1 := by simp
  rw [ha, hl] at h
  have hg0 : Nat.gcd (nfree 4 n) (4 ^ 1 - 1) ≤ 4 ^ 1 - 1 := Nat.gcd_le_right _ (by norm_num)
  have hg : (Nat.gcd (nfree 4 n) (4 ^ 1 - 1) : ℚ) ≤ 3 := by exact_mod_cast hg0
  simp only [pow_zero, mul_one] at h
  generalize (Nat.gcd (nfree 4 n) (4 ^ 1 - 1) : ℚ) = g at h hg
  linarith

/-- **Proposition 6.5 (a)**, combined: `q = 4`: `M ≤ 3n/4` for every `n ≥ 12`. -/
theorem numM_le_q4 (hn : 12 ≤ n) : (numM 4 n : ℚ) ≤ 3 / 4 * n := by
  by_cases h2 : 2 ∣ n
  · exact numM_le_q4_even h2
  · have h := numM_le_q4_odd (n := n) h2
    have hn' : (12 : ℚ) ≤ n := by exact_mod_cast hn
    linarith

/-- **Proposition 6.5 (b)**: `q = 3`: `M ≤ 0.5983 n` if `3 ∣ n`. -/
theorem numM_le_q3_div (hn : 3 ∣ n) : (numM 3 n : ℚ) ≤ 5983 / 10000 * n := by
  have hq : IsPrimePow 3 := Nat.prime_three.isPrimePow
  have hc : charOf 3 = 3 := Nat.prime_three.minFac_eq
  have ha : 1 ≤ a 3 n := by
    show 1 ≤ n.factorization (charOf 3)
    rw [hc]; exact Nat.Prime.factorization_pos_of_dvd Nat.prime_three (NeZero.ne n) hn
  have h := numM_le_of_T (n := n) hq ∅ (5983 / 10000) (5983 / 10000) le_rfl
    (fun o ho _ => by
      rw [fa_eq_faX, RaStar_eq_RaStarX, hc]
      rcases le_or_gt o 36 with h1 | h1
      · exact (min_le_left _ _).trans ((Msmall.rsQ3A1 o ho h1 _ ha).trans (by norm_num))
      rcases le_or_gt o 42000 with h2 | h2
      · exact (min_le_right _ _).trans ((Msmall.fQ3A1 o (by omega) h2 _ ha).trans (by norm_num))
      · exact (min_le_right _ _).trans (Msmall.fQ3tail o h2 _))
    (fun o ho => absurd ho (Finset.notMem_empty o))
  simpa using h

/-- **Proposition 6.5 (b)**: `q = 3`: if `3 ∤ n` then `M ≤ 0.6 n + 0.4 gcd(n, 3^8 - 1)`. -/
theorem numM_le_q3_ndiv (hn : ¬ 3 ∣ n) :
    (numM 3 n : ℚ) ≤ 6 / 10 * n + 4 / 10 * (Nat.gcd n (3 ^ 8 - 1) : ℚ) := by
  have hq : IsPrimePow 3 := Nat.prime_three.isPrimePow
  have hc : charOf 3 = 3 := Nat.prime_three.minFac_eq
  have ha : a 3 n = 0 := by
    show n.factorization (charOf 3) = 0
    rw [hc]; exact Nat.factorization_eq_zero_of_not_dvd hn
  have hnf : nfree 3 n = n := by
    show pfree (charOf 3) n = n
    rw [hc]; exact pfree_eq_self Nat.prime_three hn
  have h := numM_le_of_T (n := n) hq {1, 2, 4, 8} (3 / 5) 1 (by norm_num)
    (fun o ho hoT => by
      rw [ha, fa_eq_faX, RaStar_eq_RaStarX, hc]
      rcases le_or_gt o 36 with h1 | h1
      · have hT : ¬ (o = 1 ∨ o = 2 ∨ o = 4 ∨ o = 8) := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hoT
        exact (min_le_left _ _).trans ((Msmall.rsQ3A0 o ho h1 hT).trans (by norm_num))
      rcases le_or_gt o 42000 with h2 | h2
      · exact (min_le_right _ _).trans (Msmall.fQ3A0 o (by omega) h2)
      · exact (min_le_right _ _).trans ((Msmall.fQ3tail o h2 _).trans (by norm_num)))
    (fun o hoT => by
      have : 1 ≤ o := by simp at hoT; omega
      exact (min_le_right _ _).trans ((fa_le_ff _ _ _).trans (ff_le_one o this)))
  have hl : ({1, 2, 4, 8} : Finset ℕ).lcm id = 8 := by decide
  rw [ha, hl, hnf] at h
  simp only [pow_zero, mul_one] at h
  linarith

/-- **Proposition 6.5 (b)**, consequence: `q = 3`, `3 ∤ n`, `n ≥ 131200`: `M ≤ 0.62 n`. -/
theorem numM_le_q3_ndiv_large (hn : ¬ 3 ∣ n) (hn' : 131200 ≤ n) :
    (numM 3 n : ℚ) ≤ 62 / 100 * n := by
  have h := numM_le_q3_ndiv (n := n) hn
  have hg0 : Nat.gcd n (3 ^ 8 - 1) ≤ 3 ^ 8 - 1 := Nat.gcd_le_right _ (by norm_num)
  have hg : (Nat.gcd n (3 ^ 8 - 1) : ℚ) ≤ 6560 := by exact_mod_cast hg0.trans (by norm_num)
  have : (131200 : ℚ) ≤ n := by exact_mod_cast hn'
  generalize (Nat.gcd n (3 ^ 8 - 1) : ℚ) = g at h hg
  linarith

section Q2

variable (hn : 3780 ≤ n)
include hn

/-- **Proposition 6.5 (c)**, `a = 0` (row 1 of the table): `M ≤ 0.4 n + 0.6 n/60 = 0.41 n`. -/
theorem numM_le_q2_a0 (ha : a 2 n = 0) : (numM 2 n : ℚ) ≤ 41 / 100 * n := by
  have hq : IsPrimePow 2 := Nat.prime_two.isPrimePow
  have hc : charOf 2 = 2 := Nat.prime_two.minFac_eq
  have hn' : (3780 : ℚ) ≤ n := by exact_mod_cast hn
  have h := numM_le_of_T (n := n) hq {1, 2, 3, 6} (2 / 5) 1 (by norm_num)
    (fun o ho hoT => by
      rw [ha, fa_eq_faX, RaStar_eq_RaStarX, hc]
      rcases le_or_gt o 60 with h1 | h1
      · have hT : ¬ (o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 6) := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hoT
        exact (min_le_left _ _).trans (Msmall.rsQ2A0 o ho h1 hT)
      rcases le_or_gt o 340000 with h2 | h2
      · exact (min_le_right _ _).trans ((Msmall.fQ2A0 o (by omega) h2).trans (by norm_num))
      · exact (min_le_right _ _).trans ((Msmall.fQ2tail o h2 _).trans (by norm_num)))
    (fun o hoT => by
      have : 1 ≤ o := by simp at hoT; omega
      exact (min_le_right _ _).trans ((fa_le_ff _ _ _).trans (ff_le_one o this)))
  have hl : ({1, 2, 3, 6} : Finset ℕ).lcm id = 6 := by decide
  rw [ha, hl] at h
  -- `gcd(n', 63) ≤ 63 ≤ n/60`
  have hg0 : Nat.gcd (nfree 2 n) (2 ^ 6 - 1) ≤ 2 ^ 6 - 1 := Nat.gcd_le_right _ (by norm_num)
  have hg : (Nat.gcd (nfree 2 n) (2 ^ 6 - 1) : ℚ) ≤ 63 := by exact_mod_cast hg0
  simp only [pow_zero, mul_one] at h
  generalize (Nat.gcd (nfree 2 n) (2 ^ 6 - 1) : ℚ) = g at h hg
  linarith

/-- **Proposition 6.5 (c)**, `a = 1` (row 2): `M ≤ 0.375 n + 0.375 n/30 = 0.3875 n`. -/
theorem numM_le_q2_a1 (ha : a 2 n = 1) : (numM 2 n : ℚ) ≤ 31 / 80 * n := by
  have hq : IsPrimePow 2 := Nat.prime_two.isPrimePow
  have hc : charOf 2 = 2 := Nat.prime_two.minFac_eq
  have hn' : (3780 : ℚ) ≤ n := by exact_mod_cast hn
  have hchr : ((chr 2 : ℕ) : ℚ) = 2 := by
    show ((charOf 2 : ℕ) : ℚ) = 2
    rw [hc]; norm_num
  have h := numM_le_of_T (n := n) hq {1, 2, 6} (3 / 8) (3 / 4) (by norm_num)
    (fun o ho hoT => by
      rw [ha, fa_eq_faX, RaStar_eq_RaStarX, hc]
      have hT : ¬ (o = 1 ∨ o = 2 ∨ o = 6) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hoT
      rcases le_or_gt o 60 with h1 | h1
      · have := Msmall.rsQ2A1 o ho h1
        simp only [hT, ↓reduceIte] at this
        exact (min_le_left _ _).trans this
      by_cases h90 : o = 90
      · subst h90; exact (min_le_left _ _).trans (Msmall.rsQ2_90.trans (by norm_num))
      rcases le_or_gt o 340000 with h2 | h2
      · exact (min_le_right _ _).trans ((Msmall.fQ2A1 o (by omega) h2 1 le_rfl
          (by simp [h90])).trans (by norm_num))
      · exact (min_le_right _ _).trans ((Msmall.fQ2tail o h2 _).trans (by norm_num)))
    (fun o hoT => by
      rw [ha, RaStar_eq_RaStarX, hc]
      have hT : o = 1 ∨ o = 2 ∨ o = 6 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hoT
      have h1 : 1 ≤ o := by omega
      have h2 : o ≤ 60 := by omega
      have := Msmall.rsQ2A1 o h1 h2
      simp only [hT, ↓reduceIte] at this
      exact (min_le_left _ _).trans this)
  have hl : ({1, 2, 6} : Finset ℕ).lcm id = 6 := by decide
  rw [ha, hl, hchr] at h
  -- `2 gcd(n', 63) ≤ 126 ≤ n/30`
  have hg0 : Nat.gcd (nfree 2 n) (2 ^ 6 - 1) ≤ 2 ^ 6 - 1 := Nat.gcd_le_right _ (by norm_num)
  have hg : (Nat.gcd (nfree 2 n) (2 ^ 6 - 1) : ℚ) ≤ 63 := by exact_mod_cast hg0
  simp only [pow_one] at h
  generalize (Nat.gcd (nfree 2 n) (2 ^ 6 - 1) : ℚ) = g at h hg
  linarith

/-- **Proposition 6.5 (c)**, `a = 2` (row 3): `M ≤ 0.375 n + 0.0625 n/63`. -/
theorem numM_le_q2_a2 (ha : a 2 n = 2) : (numM 2 n : ℚ) ≤ (3 / 8 + 1 / 16 / 63) * n := by
  have hq : IsPrimePow 2 := Nat.prime_two.isPrimePow
  have hc : charOf 2 = 2 := Nat.prime_two.minFac_eq
  have hn' : (3780 : ℚ) ≤ n := by exact_mod_cast hn
  have hchr : ((chr 2 : ℕ) : ℚ) = 2 := by
    show ((charOf 2 : ℕ) : ℚ) = 2
    rw [hc]; norm_num
  have h := numM_le_of_T (n := n) hq {4} (3 / 8) (7 / 16) (by norm_num)
    (fun o ho hoT => by
      rw [ha, fa_eq_faX, RaStar_eq_RaStarX, hc]
      have hT : o ≠ 4 := by simpa only [Finset.mem_singleton] using hoT
      rcases le_or_gt o 60 with h1 | h1
      · have := Msmall.rsQ2A2 o ho h1
        simp only [hT, ↓reduceIte] at this
        exact (min_le_left _ _).trans this
      rcases le_or_gt o 340000 with h2 | h2
      · exact (min_le_right _ _).trans ((Msmall.fQ2A2 o (by omega) h2 2 le_rfl).trans
          (by norm_num))
      · exact (min_le_right _ _).trans ((Msmall.fQ2tail o h2 _).trans (by norm_num)))
    (fun o hoT => by
      rw [ha, RaStar_eq_RaStarX, hc]
      simp only [Finset.mem_singleton] at hoT
      subst hoT
      have := Msmall.rsQ2A2 4 (by norm_num) (by norm_num)
      simp only [↓reduceIte] at this
      exact (min_le_left _ _).trans this)
  have hl : ({4} : Finset ℕ).lcm id = 4 := by simp
  rw [ha, hl, hchr] at h
  -- `4 gcd(n', 15) ≤ 60 ≤ n/63`
  have hg0 : Nat.gcd (nfree 2 n) (2 ^ 4 - 1) ≤ 2 ^ 4 - 1 := Nat.gcd_le_right _ (by norm_num)
  have hg : (Nat.gcd (nfree 2 n) (2 ^ 4 - 1) : ℚ) ≤ 15 := by exact_mod_cast hg0
  generalize (Nat.gcd (nfree 2 n) (2 ^ 4 - 1) : ℚ) = g at h hg
  linarith

/-- **Proposition 6.5 (c)**, `a ≥ 3` (row 4): `M ≤ 0.35 n`. -/
theorem numM_le_q2_a3 (ha : 3 ≤ a 2 n) : (numM 2 n : ℚ) ≤ 35 / 100 * n := by
  have hq : IsPrimePow 2 := Nat.prime_two.isPrimePow
  have hc : charOf 2 = 2 := Nat.prime_two.minFac_eq
  have h := numM_le_of_T (n := n) hq ∅ (35 / 100) (35 / 100) le_rfl
    (fun o ho _ => by
      rw [fa_eq_faX, RaStar_eq_RaStarX, hc]
      rcases le_or_gt o 60 with h1 | h1
      · exact (min_le_left _ _).trans ((Msmall.rsQ2A3 o ho h1 _ ha).trans (by norm_num))
      rcases le_or_gt o 340000 with h2 | h2
      · exact (min_le_right _ _).trans ((Msmall.fQ2A3 o (by omega) h2 _ ha).trans (by norm_num))
      · exact (min_le_right _ _).trans ((Msmall.fQ2tail o h2 _).trans (by norm_num)))
    (fun o ho => absurd ho (Finset.notMem_empty o))
  simpa using h

end Q2

/-- **Proposition 6.5 (c)**: `q = 2`: `M ≤ 0.41 n` for every `n ≥ 3780`. -/
theorem numM_le_q2 (hn : 3780 ≤ n) : (numM 2 n : ℚ) ≤ 41 / 100 * n := by
  have hn' : (0 : ℚ) ≤ n := by positivity
  rcases (show a 2 n = 0 ∨ a 2 n = 1 ∨ a 2 n = 2 ∨ 3 ≤ a 2 n by omega) with ha | ha | ha | ha
  · exact numM_le_q2_a0 hn ha
  · have := numM_le_q2_a1 hn ha; linarith
  · have := numM_le_q2_a2 hn ha; linarith
  · have := numM_le_q2_a3 hn ha; linarith

end Model

end MorganMullen
