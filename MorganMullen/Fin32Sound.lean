import MorganMullen.Fin32Comp
import MorganMullen.Sec5Types

/-!
# Proposition 8.4: soundness of the checker

`chkN_sound`: if the Boolean check `chkN q P oF phiF tF n` succeeds (with `oF` returning verified
orders or `0`, `phiF = φ`, `tF ≥ t_k`) then criterion `(*)` holds for `(q, n)` with `W = W(q)`, the
exact `M`, `S` and the bound `omegaBd q n` of Lemma 5.1. `blockOK_sound` transfers this
to the block checks of `Fin32Comp.lean` (run in `Fin32Runs.lean`).
-/

namespace MorganMullen.Fin32

open MorganMullen Finset

/-! ### Divisors -/

lemma mem_sdAux (n : ℕ) : ∀ (i : ℕ) (acc : List ℕ) (x : ℕ),
    x ∈ sdAux n i acc ↔ (1 ≤ x ∧ x ≤ i ∧ n % x = 0) ∨ x ∈ acc
  | 0, acc, x => by simp [sdAux]; omega
  | i + 1, acc, x => by
    rw [sdAux, mem_sdAux n i]
    split_ifs with h
    · simp only [List.mem_cons]
      constructor
      · rintro (⟨h1, h2, h3⟩ | rfl | h4)
        · exact Or.inl ⟨h1, by omega, h3⟩
        · exact Or.inl ⟨by omega, le_refl _, h⟩
        · exact Or.inr h4
      · rintro (⟨h1, h2, h3⟩ | h4)
        · rcases Nat.lt_or_eq_of_le h2 with h2 | h2
          · exact Or.inl ⟨h1, by omega, h3⟩
          · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h4)
    · constructor
      · rintro (⟨h1, h2, h3⟩ | h4)
        · exact Or.inl ⟨h1, by omega, h3⟩
        · exact Or.inr h4
      · rintro (⟨h1, h2, h3⟩ | h4)
        · rcases Nat.lt_or_eq_of_le h2 with h2 | h2
          · exact Or.inl ⟨h1, by omega, h3⟩
          · exact absurd (h2 ▸ h3) h
        · exact Or.inr h4

lemma nodup_sdAux (n : ℕ) : ∀ (i : ℕ) (acc : List ℕ), acc.Nodup → (∀ x ∈ acc, i < x) →
    (sdAux n i acc).Nodup
  | 0, acc, h1, _ => by simpa [sdAux] using h1
  | i + 1, acc, h1, h2 => by
    rw [sdAux]
    apply nodup_sdAux n i
    · split_ifs
      · exact List.nodup_cons.2 ⟨fun hm => by have := h2 _ hm; omega, h1⟩
      · exact h1
    · split_ifs
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · have := h2 x hx; omega
      · intro x hx; have := h2 x hx; omega

lemma mem_smallDivs {n x : ℕ} : x ∈ smallDivs n ↔ 1 ≤ x ∧ x ≤ n.sqrt ∧ n % x = 0 := by
  rw [smallDivs, mem_sdAux]; simp

lemma nodup_smallDivs (n : ℕ) : (smallDivs n).Nodup :=
  nodup_sdAux n _ [] List.nodup_nil (by simp)

lemma mem_divList {n x : ℕ} (hn : 0 < n) : x ∈ divList n ↔ x ∣ n := by
  simp only [divList, List.mem_append, List.mem_map, List.mem_filter, mem_smallDivs, bne_iff_ne,
    ne_eq]
  constructor
  · rintro (⟨-, -, h⟩ | ⟨i, ⟨⟨-, -, h⟩, -⟩, rfl⟩)
    · exact Nat.dvd_of_mod_eq_zero h
    · exact Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h)
  · intro hx
    have hx1 : 1 ≤ x := Nat.pos_of_dvd_of_pos hx hn
    by_cases hs : x ≤ n.sqrt
    · exact Or.inl ⟨hx1, hs, Nat.mod_eq_zero_of_dvd hx⟩
    · right
      obtain ⟨i, hi⟩ := hx
      have hxx : n < x * x := Nat.sqrt_lt.1 (by omega)
      have hi1 : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; omega
        · exact h
      have hix : i < x := by
        by_contra hc
        push Not at hc
        have : x * x ≤ x * i := Nat.mul_le_mul_left x hc
        omega
      have hii : i * i < n := by
        have : i * i < i * x := Nat.mul_lt_mul_of_pos_left hix (by omega)
        rw [hi]; linarith [mul_comm i x]
      refine ⟨i, ⟨⟨hi1, Nat.le_sqrt.2 (by omega), ?_⟩, by omega⟩, ?_⟩
      · rw [hi]; simp
      · rw [hi, Nat.mul_div_cancel _ (by omega)]

lemma nodup_divList {n : ℕ} (hn : 0 < n) : (divList n).Nodup := by
  rw [divList, List.nodup_append]
  refine ⟨nodup_smallDivs n, ?_, ?_⟩
  · apply List.Nodup.map_on _ ((nodup_smallDivs n).filter _)
    intro x hx y hy hxy
    simp only [List.mem_filter, mem_smallDivs] at hx hy
    have h1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hx.1.2.2)
    have h2 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hy.1.2.2)
    have hq : 0 < n / y := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mod_eq_zero hy.1.2.2))
      (by omega)
    rw [hxy] at h1
    exact Nat.eq_of_mul_eq_mul_left hq (by rw [h1, h2])
  · intro a ha b hb hab
    subst hab
    simp only [List.mem_map, List.mem_filter, mem_smallDivs, bne_iff_ne, ne_eq] at ha hb
    obtain ⟨i, ⟨⟨hi1, his, hin⟩, hii⟩, hia⟩ := hb
    obtain ⟨-, has, -⟩ := ha
    have hdvd := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hin)
    have h1 : i * i ≤ n := Nat.le_sqrt.1 his
    have h2 : a * a ≤ n := Nat.le_sqrt.1 has
    rw [hia] at hdvd
    -- a * i = n, i * i < n, a * a ≤ n
    have hlt : i * i < n := lt_of_le_of_ne h1 hii
    have hia' : i < a := by
      by_contra hc; push Not at hc
      have : a * i ≤ i * i := Nat.mul_le_mul_right i hc
      omega
    have : i * a < a * a := Nat.mul_lt_mul_of_pos_right hia' (by omega)
    rw [mul_comm] at this
    omega

/-- `n.divisors` as a list. -/
lemma toFinset_divList {n : ℕ} (hn : 0 < n) : (divList n).toFinset = n.divisors := by
  ext x; simp [mem_divList hn, hn.ne']

lemma sum_divisors_eq {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 0 < n) (f : ℕ → M) :
    ∑ x ∈ n.divisors, f x = ((divList n).map f).sum := by
  rw [← toFinset_divList hn, List.sum_toFinset _ (nodup_divList hn)]

/-- the divisors of `m ∣ n` as a filter of `divList n`. -/
lemma sum_divisors_eq' {M : Type*} [AddCommMonoid M] {n m : ℕ} (hn : 0 < n) (hm : m ∣ n)
    (f : ℕ → M) :
    ∑ x ∈ m.divisors, f x = (((divList n).filter (fun e => m % e = 0)).map f).sum := by
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm hn
  rw [← List.sum_toFinset _ ((nodup_divList hn).filter _)]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, mem_divList hn, decide_eq_true_eq,
    Nat.mem_divisors]
  constructor
  · rintro ⟨h1, -⟩; exact ⟨h1.trans hm, Nat.mod_eq_zero_of_dvd h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨Nat.dvd_of_mod_eq_zero h2, hm0.ne'⟩

/-! ### `p`-free part -/

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

/-! ### Orders -/

lemma verifyOrd_sound {q e o : ℕ} (h : verifyOrd q e o = true) : ordMod q e = o := by
  simp only [verifyOrd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨ho, he⟩, h1⟩, h2⟩ := h
  have key : ∀ k, Cert.powModNat q k e = 1 % e ↔ (q : ZMod e) ^ k = 1 := by
    intro k
    obtain ⟨hlt, hval⟩ := Cert.powModNat_spec q k e he
    rw [← hval]
    constructor
    · intro hk; rw [hk, ZMod.natCast_mod, Nat.cast_one]
    · intro hk
      have : ((Cert.powModNat q k e : ℕ) : ZMod e) = ((1 % e : ℕ) : ZMod e) := by
        rw [hk, ZMod.natCast_mod, Nat.cast_one]
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt (Nat.mod_lt _ he)] at this
      exact this
  unfold ordMod
  apply orderOf_eq_of_pow_and_pow_div_prime ho ((key o).1 h1)
  intro r hr hro hc
  exact h2 r ((Nat.mem_primeFactorsList ho.ne').2 ⟨hr, hro⟩) ((key _).2 hc)

lemma ordChecked_eq {q e : ℕ} (h : ordChecked q e ≠ 0) : ordChecked q e = ordMod q e := by
  unfold ordChecked at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hv
  · exact (verifyOrd_sound hv).symm
  · exact absurd rfl h

/-! ### Tables -/

lemma look_ofFn (f : ℕ → ℕ) (N : ℕ) : look (Array.ofFn (n := N) fun j => f j.1) f = f := by
  funext i
  unfold look
  split_ifs with h
  · simp
  · rfl


/-! ### Sums over the essential types -/

section Ess

variable {q n : ℕ} [NeZero n]

omit [NeZero n] in
lemma sum_essTypes {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ → M) :
    ∑ de ∈ Model.essTypes q n, g de.1 de.2 =
      ∑ d ∈ n.divisors, ∑ e ∈ (Model.nfree q n).divisors,
        if e ∣ Model.bigN q n d ∧ d ∣ ordMod q e then g d e else 0 := by
  classical
  unfold Model.essTypes
  rw [Finset.sum_filter, Finset.sum_product]

lemma essSum_eq (hq : IsPrimePow q) {oF : ℕ → ℕ}
    (hoF0 : ∀ e ∈ (divList n).filter (fun e => remP q.minFac n % e = 0), oF e ≠ 0)
    (hoF : ∀ e, oF e ≠ 0 → oF e = ordMod q e)
    (g G : ℕ → ℕ → ℕ) (hg : ∀ d e, e ∣ Model.nfree q n → oF e = ordMod q e → g d e = G d e) :
    essSum oF q.minFac (remP q.minFac n) (divList n)
        ((divList n).filter (fun e => remP q.minFac n % e = 0)) g =
      ∑ de ∈ Model.essTypes q n, G de.1 de.2 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hp : q.minFac.Prime := Nat.minFac_prime (by have := hq.two_le; omega)
  have hnf : Model.nfree q n = remP q.minFac n := (remP_eq hp n).symm
  rw [sum_essTypes, sum_divisors_eq hn]
  unfold essSum
  congr 1
  apply List.map_congr_left
  intro d hd
  have hd' : d ∣ n := (mem_divList hn).1 hd
  rw [sum_divisors_eq' (m := Model.nfree q n) hn (pfree_dvd _ n), hnf]
  dsimp only
  congr 1
  apply List.map_congr_left
  intro e he
  have he0 := hoF0 e he
  have hoe := hoF e he0
  have he' : e ∣ Model.nfree q n := by
    simp only [List.mem_filter, decide_eq_true_eq] at he
    rw [hnf]; exact Nat.dvd_of_mod_eq_zero he.2
  have hbig : Model.bigN q n d = Model.nfree q n / remP q.minFac d := by
    rw [remP_eq hp]; rfl
  rw [hbig, hg d e he' hoe, ← hoe, hnf]
  simp only [Nat.dvd_iff_mod_eq_zero]

end Ess

/-! ### The bound for `ω` -/

lemma omegaBd_le {q n : ℕ} (hn : 0 < n) {tF : ℕ → ℕ}
    (htF : ∀ k, 2 ≤ k → tk q k ≤ tF k) : omegaBd q n ≤ omegaC q tF (divList n) := by
  unfold omegaBd omegaC
  rw [← sum_divisors_eq hn, Finset.sum_filter]
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro k _
  split_ifs with hk
  · exact htF k hk
  · exact le_rfl

/-! ### The bound for `S` -/

lemma inv_pow_le_U64 {q : ℕ} (hq : 2 ≤ q) (o : ℕ) :
    ((q : ℚ) ^ o)⁻¹ ≤ (U64 q o : ℚ) / 2 ^ 64 := by
  have hqo : (0 : ℚ) < (q : ℚ) ^ o := by positivity
  rw [inv_le_iff_one_le_mul₀ hqo, div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
  unfold U64
  split_ifs with ho
  · have : (2 : ℚ) ^ 64 ≤ 2 ^ o := pow_le_pow_right₀ (by norm_num) ho
    have h2 : (2 : ℚ) ^ o ≤ (q : ℚ) ^ o := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq) o
    simp only [Nat.cast_one, one_mul]
    linarith
  · have hpos : 0 < q ^ o := by positivity
    have : 2 ^ 64 < (2 ^ 64 / q ^ o + 1) * q ^ o := by
      rw [add_mul, one_mul]
      exact Nat.lt_div_mul_add hpos
    exact_mod_cast this.le

lemma sumS_le {q n : ℕ} [NeZero n] (hq : IsPrimePow q) :
    (Model.sumS q n : ℚ) ≤
      ((∑ de ∈ Model.essTypes q n, (if 2 ≤ ordMod q de.2 then
        Model.nu q de.1 de.2 * U64 q (ordMod q de.2) else 0) : ℕ) : ℚ) / 2 ^ 64 := by
  classical
  rw [Model.sumS_eq hq, Finset.sum_filter, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro de _
  split_ifs with h
  · push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (inv_pow_le_U64 hq.two_le _) (by positivity)
  · simp

lemma sumS_nonneg {q n : ℕ} [NeZero n] (hq : IsPrimePow q) : 0 ≤ (Model.sumS q n : ℚ) := by
  classical
  rw [Model.sumS_eq hq]
  apply Finset.sum_nonneg
  intro de _
  positivity

/-! ### Real inequalities -/

lemma div_le_logb {q a b : ℕ} (hb : 0 < b) (h : 2 ^ a ≤ q ^ b) : (a : ℝ) / b ≤ Real.logb 2 q := by
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h'
    · rw [zero_pow hb.ne'] at h; have := Nat.one_le_two_pow (n := a); omega
    · exact h'
  have h1 : ((2 : ℝ) ^ a) ≤ (q : ℝ) ^ b := by exact_mod_cast h
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  linarith

lemma cW_le {W : ℚ} {r s : ℕ} (hs : 0 < s) (hW0 : 0 < W.num) (hW1 : W.num.toNat < W.den)
    (h : W.den ^ s ≤ 2 ^ r * (W.den - W.num.toNat) ^ s) :
    cW (W : ℝ) ≤ (r : ℝ) / s / W ∧ 0 ≤ cW (W : ℝ) := by
  set w1 := W.num.toNat
  set w2 := W.den
  have hw1 : (W.num : ℝ) = (w1 : ℝ) := by
    have : ((w1 : ℤ) : ℝ) = (W.num : ℝ) := by
      rw [show ((w1 : ℤ)) = W.num from Int.toNat_of_nonneg hW0.le]
    rw [← this, Int.cast_natCast]
  have hW : (W : ℝ) = (w1 : ℝ) / w2 := by rw [Rat.cast_def, hw1]
  have hw1pos : (0 : ℝ) < w1 := by
    have : 0 < w1 := by omega
    exact_mod_cast this
  have hw2pos : (0 : ℝ) < w2 := by exact_mod_cast W.den_pos
  have hlt : (w1 : ℝ) < w2 := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by rw [hW]; positivity
  have hx : 1 / (1 - (W : ℝ)) = (w2 : ℝ) / ((w2 - w1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hW1.le, hW]
    field_simp
  have hden : (0 : ℝ) < ((w2 - w1 : ℕ) : ℝ) := by
    have : 0 < w2 - w1 := by omega
    exact_mod_cast this
  have hx1 : 1 ≤ 1 / (1 - (W : ℝ)) := by
    rw [hx, le_div_iff₀ hden, one_mul, Nat.cast_sub hW1.le]; linarith
  have hpow : (1 / (1 - (W : ℝ))) ^ s ≤ (2 : ℝ) ^ r := by
    rw [hx, div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast h
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hpow
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  have hl : Real.logb 2 (1 / (1 - (W : ℝ))) ≤ r / s := by
    rw [le_div_iff₀ (by exact_mod_cast hs)]; linarith
  have hnn : 0 ≤ Real.logb 2 (1 / (1 - (W : ℝ))) := Real.logb_nonneg (by norm_num) hx1
  unfold cW
  exact ⟨div_le_div_of_nonneg_right hl hWpos.le, div_nonneg hnn hWpos.le⟩

/-- `log₂(q^n - 1) ≥ n log₂ q - 1/1000` for `q^n ≥ 2048` (Bernoulli:
`(1 - 1/2048)^1000 ≥ 1 - 1000/2048 ≥ 1/2`). -/
lemma logb_sub_one_ge' {q n : ℕ} (h : 2048 ≤ (q : ℝ) ^ n) :
    (n : ℝ) * Real.logb 2 q - 1 / 1000 ≤ Real.logb 2 ((q : ℝ) ^ n - 1) := by
  have hpos : (0 : ℝ) < (q : ℝ) ^ n := by linarith
  have h1 : (2047 / 2048 : ℝ) * (q : ℝ) ^ n ≤ (q : ℝ) ^ n - 1 := by linarith
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
  rw [Real.logb_mul (by norm_num) hpos.ne', Real.logb_pow] at h2
  have h3 : -1 / 1000 ≤ Real.logb 2 (2047 / 2048 : ℝ) := by
    have hB := one_add_mul_le_pow (a := (-1 / 2048 : ℝ)) (by norm_num) 1000
    have h5 : (1 / 2 : ℝ) ≤ (2047 / 2048) ^ 1000 := by
      have e : (1 : ℝ) + -1 / 2048 = 2047 / 2048 := by norm_num
      rw [e] at hB
      exact le_trans (by norm_num) hB
    have h4 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h5
    rw [Real.logb_pow, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)] at h4
    push_cast at h4
    linarith
  linarith

/-! ### Soundness of the check for one pair -/

theorem chkN_sound {q n : ℕ} [NeZero n] (hq : IsPrimePow q) {P : Par} (hP : parOK q P = true)
    {oF phiF tF : ℕ → ℕ} (hoF : ∀ e, oF e ≠ 0 → oF e = ordMod q e)
    (hphi : ∀ e, phiF e = e.totient) (htF : ∀ k, 2 ≤ k → tk q k ≤ tF k)
    (h : chkN q P oF phiF tF n = true) :
    StarHolds q n (Wq q) ((omegaBd q n : ℝ) + 1) (Model.numM q n) (Model.sumS q n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hq2 := hq.two_le
  simp only [parOK, Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨⟨⟨⟨hb, hab⟩, hs⟩, hW0⟩, hW1⟩, hrs⟩ := hP
  unfold chkN at h
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hE, h3⟩, hfin⟩ := h
  -- `M`
  have hM : Model.numM q n = essSum oF q.minFac (remP q.minFac n) (divList n)
      ((divList n).filter (fun e => remP q.minFac n % e = 0)) (nuC oF phiF) := by
    rw [Model.numM_eq hq]
    symm
    exact essSum_eq hq hE hoF _ _ (fun d e _ hoe => by simp only [nuC, Model.nu, hphi, hoe])
  -- `S`
  have hS : (Model.sumS q n : ℚ) ≤ (essSum oF q.minFac (remP q.minFac n) (divList n)
      ((divList n).filter (fun e => remP q.minFac n % e = 0)) (sTerm q oF phiF) : ℚ) / 2 ^ 64 := by
    rw [essSum_eq hq hE hoF _ (fun d e => if 2 ≤ ordMod q e then
        Model.nu q d e * U64 q (ordMod q e) else 0)
      (fun d e _ hoe => by simp only [sTerm, nuC, Model.nu, hphi, hoe])]
    exact sumS_le hq
  generalize essSum oF q.minFac (remP q.minFac n) (divList n)
      ((divList n).filter (fun e => remP q.minFac n % e = 0)) (nuC oF phiF) = M at hM hfin
  generalize essSum oF q.minFac (remP q.minFac n) (divList n)
      ((divList n).filter (fun e => remP q.minFac n % e = 0)) (sTerm q oF phiF) = S at hS hfin
  have hS0 := sumS_nonneg hq (n := n)
  -- `ω`
  have hΩ : omegaBd q n ≤ omegaC q tF (divList n) := omegaBd_le hn htF
  generalize omegaC q tF (divList n) = Ω at hΩ hfin
  -- the final inequality
  unfold finalIneq at hfin
  rw [decide_eq_true_eq] at hfin
  have hfinR := (Rat.cast_le (K := ℝ)).2 hfin
  push_cast at hfinR
  -- `c(W)`
  obtain ⟨hC, hC0⟩ := cW_le hs hW0 hW1 hrs
  -- `log₂ q`
  have hL := div_le_logb hb hab
  -- `q^n ≥ 2048`
  have h2048 : (2048 : ℝ) ≤ (q : ℝ) ^ n := by
    have h1 : q ^ min n 11 ≤ q ^ n := Nat.pow_le_pow_right (by omega) (min_le_left _ _)
    exact_mod_cast (show 2048 ≤ q ^ n by omega)
  have hlog := logb_sub_one_ge' h2048
  -- assemble
  unfold StarHolds
  have hΩR : ((omegaBd q n : ℕ) : ℝ) ≤ (Ω : ℝ) := by exact_mod_cast hΩ
  have hMR : ((Model.numM q n : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast hM
  have hSR : ((Model.sumS q n : ℚ) : ℝ) ≤ (S : ℝ) / 2 ^ 64 := by
    have := (Rat.cast_le (K := ℝ)).2 hS
    push_cast at this
    exact this
  have hS0R : (0 : ℝ) ≤ ((Model.sumS q n : ℚ) : ℝ) := by exact_mod_cast hS0
  have hCS : cW ((Wq q : ℚ) : ℝ) * ((Model.sumS q n : ℚ) : ℝ) ≤
      (P.r : ℝ) / P.s / ((Wq q : ℚ) : ℝ) * ((S : ℝ) / 2 ^ 64) :=
    mul_le_mul hC hSR hS0R (hC0.trans hC)
  have hnL : (n : ℝ) * P.a / (2 * P.b) ≤ (n : ℝ) / 2 * Real.logb 2 q := by
    have : (n : ℝ) * P.a / (2 * P.b) = (n : ℝ) / 2 * ((P.a : ℝ) / P.b) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hL (by positivity)
  linarith

/-! ### Blocks -/

lemma allFrom_sound {f : ℕ → Bool} : ∀ lo len, allFrom f lo len = true →
    ∀ n, lo ≤ n → n < lo + len → f n = true
  | _, 0, _, n, h1, h2 => by omega
  | lo, len + 1, h, n, h1, h2 => by
    simp only [allFrom, Bool.and_eq_true] at h
    rcases Nat.lt_or_eq_of_le h1 with h1 | rfl
    · exact allFrom_sound (lo + 1) len h.2 n (by omega) (by omega)
    · exact h.1

theorem blockOK_sound {q : ℕ} (hq : IsPrimePow q) {P : Par} {N lo hi : ℕ}
    (h : blockOK q P N lo hi = true) (n : ℕ) [NeZero n] (hlo : lo ≤ n) (hhi : n < hi)
    (hneed : needed q n = true) :
    StarHolds q n (Wq q) ((omegaBd q n : ℝ) + 1) (Model.numM q n) (Model.sumS q n) := by
  unfold blockOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hP, hall⟩ := h
  have h1 := allFrom_sound _ _ hall n hlo (by omega)
  simp only [hneed, Bool.not_true, Bool.false_or] at h1
  rw [ordTbl, look_ofFn, phiTbl, look_ofFn, tTbl, look_ofFn] at h1
  exact chkN_sound hq hP (fun e he => ordChecked_eq he) (fun e => totientFast_eq e)
    (fun k hk => tk_le_tUpper hq.two_le hk) h1

/-! ### The ranges -/

lemma not_isPrimePow_of_dvd {n a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (han : a ∣ n) (hbn : b ∣ n) : ¬ IsPrimePow n := by
  intro h
  obtain ⟨p, k, hp, -, rfl⟩ := (isPrimePow_nat_iff n).1 h
  have h1 := (Nat.prime_dvd_prime_iff_eq ha hp).1 (ha.dvd_of_dvd_pow han)
  have h2 := (Nat.prime_dvd_prime_iff_eq hb hp).1 (hb.dvd_of_dvd_pow hbn)
  exact hab (h1.trans h2.symm)

lemma inAnalyticB_iff (q n : ℕ) : inAnalyticB q n = true ↔ InAnalyticRange q n := by
  simp only [inAnalyticB, InAnalyticRange, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne, ne_eq, Nat.dvd_iff_mod_eq_zero, or_assoc, and_assoc]

lemma needed_of {q n : ℕ} (hqn : q < n) (hA : ¬ InAnalyticRange q n) (hC : (q, n) ∉ certPairs) :
    needed q n = true := by
  simp only [needed, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, inAnalyticB_iff]
  refine ⟨⟨hqn, hA⟩, ?_⟩
  simpa using hC

end MorganMullen.Fin32
