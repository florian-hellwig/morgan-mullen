import MorganMullen.ExactComp
import MorganMullen.Sec6NumberOfConditions

/-!
# Exact maximal weights: soundness of the check

`chk_sound`: if `Chk q n n' oF lab W` holds (`q` prime), then every component of the essential
conditions for `(q, n)` without a condition of codimension `1` has weight at most `W`.

* `lab_fibre`: the label `lab` is constant on the fibre of every essential condition;
* `lab_sameComp`: hence (via Lemma 3.3 (a), `sameComp_iff_qChain`) on every component;
* `weight_filter_eq`: the weight of the essential conditions of codimension `≥ 2` whose fibres
  satisfy a fibre-invariant predicate `L` is a sum over the levels `d` and the targets
  `x = d' k`, `k < N`, each target contributing `d/(o q^o)` (an essential condition with
  codimension `o` has `o/d` targets).
-/

set_option linter.unusedSectionVars false

namespace MorganMullen.Exact

open Finset Model

/-! ### Arithmetic helpers -/

lemma rp_eq {p : ℕ} (hp : p.Prime) (n : ℕ) : rp p n = pfree p n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [rp]
  split_ifs with h
  · have hd : p ∣ n := Nat.dvd_of_mod_eq_zero h.2.2
    rw [ih _ (Nat.div_lt_self h.2.1 h.1)]
    conv_rhs => rw [← Nat.mul_div_cancel' hd]
    rw [show p * (n / p) = p ^ 1 * (n / p) by rw [pow_one], pfree_pow_mul hp]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pfree_zero]
    · exact (pfree_eq_self hp fun hd => h ⟨hp.one_lt, hn, Nat.mod_eq_zero_of_dvd hd⟩).symm

lemma ordMod_eq_of_ordOK {q e o : ℕ} (h : OrdOK q e o) : ordMod q e = o := by
  obtain ⟨ho, h1, h2⟩ := h
  have key : ∀ k, (q : ZMod e) ^ k = 1 ↔ q ^ k % e = 1 % e := by
    intro k
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
  unfold ordMod
  rw [orderOf_eq_iff ho]
  exact ⟨(key o).2 h1, fun k hk hk0 hc => h2 k (mem_range.2 hk) hk0 ((key k).1 hc)⟩

lemma chr_eq_of_prime {q : ℕ} (hq : q.Prime) : chr q = q := hq.minFac_eq

lemma rp_eq_pfree_chr {q : ℕ} (hq : q.Prime) (j : ℕ) : rp q j = pfree (chr q) j := by
  rw [rp_eq hq, chr_eq_of_prime hq]

/-! ### The model side -/

section Model

variable {q n : ℕ} [NeZero n]

lemma dfree_mul_natCast_bigN {d : ℕ} (hd : d ∣ n) (t : ℕ) :
    ((dfree q d : ℕ) : ZMod (nfree q n)) * ((t * bigN q n d : ℕ) : ZMod (nfree q n)) = 0 := by
  rw [← Nat.cast_mul, show dfree q d * (t * bigN q n d) = t * (dfree q d * bigN q n d) by ring,
    dfree_mul_bigN hd, Nat.cast_mul, ZMod.natCast_self, mul_zero]

/-- The size of the orbit of the targets of an essential condition. -/
lemma card_orbit_ess (hq : IsPrimePow q) {d : ℕ} (hd0 : d ≠ 0) {x : ZMod (nfree q n)}
    (hess : d ∣ tcodim q n x) : (orbit q n d x).card = tcodim q n x / d := by
  rw [card_orbit hq, ordMod_pow _ _ hd0]
  exact congrArg _ (Nat.gcd_eq_right hess)

/-- Summing over the conditions `(d, orbit of x)`, `x ∈ X`, is summing over the targets with
weights `1/|orbit|`. -/
lemma sum_image_orbit (hq : IsPrimePow q) (d : ℕ) (X : Finset (ZMod (nfree q n)))
    (hX : ∀ x ∈ X, orbit q n d x ⊆ X) (F : Cond q n → ℚ) :
    ∑ C ∈ X.image (fun x => ((d, orbit q n d x) : Cond q n)), F C =
      ∑ x ∈ X, F (d, orbit q n d x) / ((orbit q n d x).card : ℚ) := by
  classical
  apply Finset.sum_image'
  intro x hx
  have hset : {y ∈ X | ((d, orbit q n d y) : Cond q n) = (d, orbit q n d x)} = orbit q n d x := by
    ext y
    simp only [Finset.mem_filter, Prod.mk.injEq, true_and]
    constructor
    · rintro ⟨-, hy⟩; rw [← hy]; exact mem_orbit_self d y
    · intro hy; exact ⟨hX x hx hy, orbit_eq_of_mem hq hy⟩
  rw [hset, Finset.sum_congr rfl (g := fun _ => F (d, orbit q n d x) / ((orbit q n d x).card : ℚ))]
  · rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((orbit q n d x).card : ℚ) ≠ 0 := by
      have : 0 < (orbit q n d x).card := Finset.card_pos.mpr ⟨x, mem_orbit_self d x⟩
      exact_mod_cast this.ne'
    field_simp
  · intro y hy
    rw [orbit_eq_of_mem hq hy]

/-- The targets of level `d` are the `d' k`, `k < N`, without repetition. -/
lemma exists_eq_dfree_mul {d : ℕ} (hd : d ∣ n) {x : ZMod (nfree q n)}
    (hx : ((bigN q n d : ℕ) : ZMod (nfree q n)) * x = 0) :
    ∃ k < bigN q n d, ((dfree q d * k : ℕ) : ZMod (nfree q n)) = x := by
  obtain ⟨i, hi⟩ := exists_dfree_mul_eq hd hx
  have hNpos : 0 < bigN q n d := bigN_pos hd
  refine ⟨i.val % bigN q n d, Nat.mod_lt _ hNpos, ?_⟩
  rw [← hi]
  have e : dfree q d * i.val = dfree q d * (i.val % bigN q n d) +
      (i.val / bigN q n d) * (dfree q d * bigN q n d) := by
    conv_lhs => rw [← Nat.mod_add_div i.val (bigN q n d)]
    ring
  rw [dfree_mul_bigN hd] at e
  have : ((dfree q d * i.val : ℕ) : ZMod (nfree q n)) = ((dfree q d * (i.val % bigN q n d) : ℕ) :
      ZMod (nfree q n)) := by
    rw [e, Nat.cast_add, Nat.cast_mul (i.val / _), ZMod.natCast_self, mul_zero, add_zero]
  rw [← this, Nat.cast_mul, ZMod.natCast_zmod_val]

lemma dfree_mul_injOn {d : ℕ} (hd : d ∣ n) :
    Set.InjOn (fun k : ℕ => ((dfree q d * k : ℕ) : ZMod (nfree q n))) (Set.Iio (bigN q n d)) := by
  intro k hk k' hk' h
  simp only [Set.mem_Iio] at hk hk'
  have hdN := dfree_mul_bigN (q := q) hd
  have hdpos : 0 < dfree q d := dfree_pos (ne_zero_of_dvd_ne_zero (NeZero.ne n) hd)
  have h1 : dfree q d * k < nfree q n := by
    rw [← hdN]; exact Nat.mul_lt_mul_of_pos_left hk hdpos
  have h2 : dfree q d * k' < nfree q n := by
    rw [← hdN]; exact Nat.mul_lt_mul_of_pos_left hk' hdpos
  simp only at h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h
  exact Nat.eq_of_mul_eq_mul_left hdpos h

/-- The weight of the essential conditions of codimension `≥ 2` whose fibre satisfies a predicate
`L` that is constant on fibres, as a sum over levels and targets. -/
theorem weight_filter_eq (hq : IsPrimePow q) (L : ZMod (nfree q n) → Prop) [DecidablePred L]
    (hL : ∀ C ∈ essConds q n, ∀ i ∈ fibre q n C, ∀ i' ∈ fibre q n C, L i → L i') :
    weight q n ((essConds q n).filter fun C => 2 ≤ codim q n C ∧ ∃ i ∈ fibre q n C, L i) =
      ∑ d ∈ n.divisors, ∑ k ∈ range (bigN q n d),
        if d ∣ tcodim q n ((dfree q d * k : ℕ) : ZMod (nfree q n)) ∧
            2 ≤ tcodim q n ((dfree q d * k : ℕ) : ZMod (nfree q n)) ∧
            L (k : ZMod (nfree q n)) then
          wt q d (tcodim q n ((dfree q d * k : ℕ) : ZMod (nfree q n))) else 0 := by
  classical
  set S := (essConds q n).filter fun C => 2 ≤ codim q n C ∧ ∃ i ∈ fibre q n C, L i with hSdef
  unfold weight
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := n.divisors)]
  swap
  · intro C hC
    obtain ⟨d, hd, x, -, -, rfl⟩ := (mem_essConds_iff hq).mp (Finset.mem_filter.mp hC).1
    exact hd
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  set X : Finset (ZMod (nfree q n)) := univ.filter fun x =>
    ((bigN q n d : ℕ) : ZMod (nfree q n)) * x = 0 ∧ d ∣ tcodim q n x ∧ 2 ≤ tcodim q n x ∧
      ∃ i ∈ fibre q n (d, orbit q n d x), L i with hXdef
  have hS : S.filter (fun C => C.1 = d) = X.image fun x => ((d, orbit q n d x) : Cond q n) := by
    ext C
    simp only [hSdef, hXdef, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hC, h2, hL⟩, rfl⟩
      obtain ⟨d', hd', x, hx, hess, rfl⟩ := (mem_essConds_iff hq).mp hC
      rw [codim_orbit hq] at h2
      exact ⟨x, ⟨hx, hess, h2, hL⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hess, h2, hL⟩, rfl⟩
      refine ⟨⟨(mem_essConds_iff hq).mpr ⟨d, hd, x, hx, hess, rfl⟩, ?_, hL⟩, rfl⟩
      rw [codim_orbit hq]; exact h2
  have htc : ∀ x y : ZMod (nfree q n), y ∈ orbit q n d x → tcodim q n y = tcodim q n x := by
    intro x y hy
    rw [← codim_orbit hq d y, ← codim_orbit hq d x, orbit_eq_of_mem hq hy]
  have hclosed : ∀ x ∈ X, orbit q n d x ⊆ X := by
    intro x hx y hy
    simp only [hXdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    have hoy := orbit_eq_of_mem hq hy
    refine ⟨?_, by rw [htc x y hy]; exact hx2, by rw [htc x y hy]; exact hx3, by rw [hoy]; exact hx4⟩
    obtain ⟨j, rfl⟩ := (mem_orbit_iff hq).mp hy
    rw [mul_left_comm, hx1, mul_zero]
  rw [hS, sum_image_orbit hq d X hclosed]
  -- the summands
  have hterm : ∀ x ∈ X, ((q : ℚ) ^ codim q n (d, orbit q n d x))⁻¹ /
      ((orbit q n d x).card : ℚ) = wt q d (tcodim q n x) := by
    intro x hx
    simp only [hXdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨-, hess, h2, -⟩ := hx
    rw [codim_orbit hq, card_orbit_ess hq hd0 hess, Nat.cast_div hess (by exact_mod_cast hd0)]
    unfold wt
    have ho : (tcodim q n x : ℚ) ≠ 0 := by
      have : 0 < tcodim q n x := by omega
      exact_mod_cast this.ne'
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    have hq0 : ((q : ℚ) ^ tcodim q n x) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne_zero)
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  -- reindex the targets by `k < N`
  have himg : X = ((range (bigN q n d)).filter fun k =>
      d ∣ tcodim q n ((dfree q d * k : ℕ) : ZMod (nfree q n)) ∧
        2 ≤ tcodim q n ((dfree q d * k : ℕ) : ZMod (nfree q n)) ∧ L (k : ZMod (nfree q n))).image
      fun k => ((dfree q d * k : ℕ) : ZMod (nfree q n)) := by
    ext x
    simp only [hXdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨hx1, hx2, hx3, i, hi, hLi⟩
      obtain ⟨k, hk, rfl⟩ := exists_eq_dfree_mul hdn hx1
      refine ⟨k, ⟨hk, hx2, hx3, ?_⟩, rfl⟩
      have hC : ((d, orbit q n d ((dfree q d * k : ℕ) : ZMod (nfree q n))) : Cond q n) ∈
          essConds q n := (mem_essConds_iff hq).mpr ⟨d, hd, _, hx1, hx2, rfl⟩
      refine hL _ hC i hi _ ?_ hLi
      rw [mem_fibre]
      simp only
      rw [← Nat.cast_mul]
      exact mem_orbit_self d _
    · rintro ⟨k, ⟨hk, hk2, hk3, hk4⟩, rfl⟩
      refine ⟨?_, hk2, hk3, (k : ZMod (nfree q n)), ?_, hk4⟩
      · rw [← Nat.cast_mul, show bigN q n d * (dfree q d * k) = k * (dfree q d * bigN q n d) by ring,
          dfree_mul_bigN hdn, Nat.cast_mul, ZMod.natCast_self, mul_zero]
      · rw [mem_fibre]
        simp only
        rw [← Nat.cast_mul]
        exact mem_orbit_self d _
  rw [himg, Finset.sum_image]
  intro k hk k' hk' hkk
  exact dfree_mul_injOn hdn (Set.mem_Iio.mpr (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))
    (Set.mem_Iio.mpr (Finset.mem_range.mp (Finset.mem_filter.mp hk').1)) hkk

end Model

/-! ### Soundness -/

section Sound

variable {q n : ℕ} [NeZero n]

lemma tcodim_natCast {oF : ℕ → ℕ} (hoF : ∀ e ∈ (nfree q n).divisors, OrdOK q e (oF e)) (a : ℕ) :
    tcodim q n (a : ZMod (nfree q n)) = oF (ordAdd (nfree q n) a) := by
  have hm : nfree q n ≠ 0 := NeZero.ne _
  unfold tcodim ordAdd
  rw [ZMod.addOrderOf_coe a hm]
  refine ordMod_eq_of_ordOK (hoF _ ?_)
  exact Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _), hm⟩

lemma natCast_mul_val (a : ℕ) (i : ZMod (nfree q n)) :
    (a : ZMod (nfree q n)) * i = ((a * i.val : ℕ) : ZMod (nfree q n)) := by
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]

lemma lab_qmul {lab : ℕ → ℕ} (h2 : ∀ i ∈ range (nfree q n), lab (q * i % nfree q n) = lab i)
    (i : ZMod (nfree q n)) : lab ((q : ZMod (nfree q n)) * i).val = lab i.val := by
  rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  exact h2 _ (mem_range.2 (ZMod.val_lt i))

lemma lab_qpow {lab : ℕ → ℕ} (h2 : ∀ i ∈ range (nfree q n), lab (q * i % nfree q n) = lab i)
    (j : ℕ) (i : ZMod (nfree q n)) : lab ((q : ZMod (nfree q n)) ^ j * i).val = lab i.val := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', mul_assoc, lab_qmul h2, ih]

lemma lab_shift (hq : q.Prime) {oF lab : ℕ → ℕ}
    (h1 : ∀ e ∈ (nfree q n).divisors, OrdOK q e (oF e))
    (h3 : ∀ d ∈ n.divisors, ∀ i ∈ range (nfree q n), d ∣ oF (ordAdd (nfree q n) (rp q d * i)) →
      lab ((i + nfree q n / rp q d) % nfree q n) = lab i)
    {d : ℕ} (hd : d ∈ n.divisors) (i : ZMod (nfree q n))
    (hess : d ∣ tcodim q n ((dfree q d : ZMod (nfree q n)) * i)) (t : ℕ) :
    lab (i + ((t * bigN q n d : ℕ) : ZMod (nfree q n))).val = lab i.val := by
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← ih]
    set i₁ := i + ((t * bigN q n d : ℕ) : ZMod (nfree q n))
    have he : ((dfree q d : ℕ) : ZMod (nfree q n)) * i₁ = (dfree q d : ZMod (nfree q n)) * i := by
      rw [mul_add, dfree_mul_natCast_bigN hdn, add_zero]
    have hess₁ : d ∣ oF (ordAdd (nfree q n) (rp q d * i₁.val)) := by
      rw [← tcodim_natCast h1, ← natCast_mul_val, rp_eq_pfree_chr hq]
      change d ∣ tcodim q n (((dfree q d : ℕ) : ZMod (nfree q n)) * i₁)
      rw [he]; exact hess
    have key := h3 d hd i₁.val (mem_range.2 (ZMod.val_lt _)) hess₁
    rw [rp_eq_pfree_chr hq] at key
    change lab ((i₁.val + bigN q n d) % nfree q n) = lab i₁.val at key
    rw [← key, show i + (((t + 1) * bigN q n d : ℕ) : ZMod (nfree q n)) =
      i₁ + ((bigN q n d : ℕ) : ZMod (nfree q n)) by
        simp only [i₁]; push_cast; ring]
    rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

lemma lab_fibre (hq : q.Prime) {oF lab : ℕ → ℕ}
    (h1 : ∀ e ∈ (nfree q n).divisors, OrdOK q e (oF e))
    (h2 : ∀ i ∈ range (nfree q n), lab (q * i % nfree q n) = lab i)
    (h3 : ∀ d ∈ n.divisors, ∀ i ∈ range (nfree q n), d ∣ oF (ordAdd (nfree q n) (rp q d * i)) →
      lab ((i + nfree q n / rp q d) % nfree q n) = lab i)
    {C : Cond q n} (hC : C ∈ essConds q n) {i i' : ZMod (nfree q n)} (hi : i ∈ fibre q n C)
    (hi' : i' ∈ fibre q n C) : lab i'.val = lab i.val := by
  have hq' := hq.isPrimePow
  obtain ⟨d, hd, x, hx, hess, rfl⟩ := (mem_essConds_iff hq').mp hC
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  rw [mem_fibre] at hi hi'
  simp only at hi hi'
  have horb : orbit q n d (((dfree q d : ℕ) : ZMod (nfree q n)) * i) = orbit q n d x :=
    orbit_eq_of_mem hq' hi
  rw [← horb] at hi'
  obtain ⟨j, hj⟩ := (mem_orbit_iff hq').mp hi'
  set i'' := (q : ZMod (nfree q n)) ^ (d * j) * i
  have he : ((dfree q d : ℕ) : ZMod (nfree q n)) * i' = ((dfree q d : ℕ) : ZMod (nfree q n)) * i'' := by
    rw [hj]; simp only [i'']; rw [pow_mul]; ring
  have hess'' : d ∣ tcodim q n (((dfree q d : ℕ) : ZMod (nfree q n)) * i'') := by
    have : ((dfree q d : ℕ) : ZMod (nfree q n)) * i'' =
        (q : ZMod (nfree q n)) ^ (d * j) * (((dfree q d : ℕ) : ZMod (nfree q n)) * i) := by
      simp only [i'']; ring
    rw [this, tcodim_qpow_mul hq', ← codim_orbit hq' d, horb, codim_orbit hq']
    exact hess
  have hmem : i' ∈ (univ.filter fun i' : ZMod (nfree q n) =>
      ((dfree q d : ℕ) : ZMod _) * i' = ((dfree q d : ℕ) : ZMod _) * i'') := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact he
  rw [fibre_coset hdn i''] at hmem
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hmem
  rw [lab_shift hq h1 h3 hd i'' hess'' t]
  exact lab_qpow h2 _ i

lemma lab_sameComp (hq : q.Prime) {oF lab : ℕ → ℕ}
    (h1 : ∀ e ∈ (nfree q n).divisors, OrdOK q e (oF e))
    (h2 : ∀ i ∈ range (nfree q n), lab (q * i % nfree q n) = lab i)
    (h3 : ∀ d ∈ n.divisors, ∀ i ∈ range (nfree q n), d ∣ oF (ordAdd (nfree q n) (rp q d * i)) →
      lab ((i + nfree q n / rp q d) % nfree q n) = lab i)
    {C C' : Cond q n} (h : SameComp q n (essConds q n) C C') (ℓ : ℕ) :
    (∃ i ∈ fibre q n C, lab i.val = ℓ) ↔ (∃ i ∈ fibre q n C', lab i.val = ℓ) := by
  rw [sameComp_iff_qChain hq.isPrimePow] at h
  induction h with
  | rel a b hab =>
    obtain ⟨ha, hb, i, hi, i', hi', j, rfl⟩ := hab
    constructor
    · rintro ⟨i₁, hi₁, rfl⟩
      exact ⟨_, hi', by rw [lab_qpow h2, lab_fibre hq h1 h2 h3 ha hi₁ hi]⟩
    · rintro ⟨i₂, hi₂, rfl⟩
      exact ⟨i, hi, by rw [← lab_qpow h2 j i, lab_fibre hq h1 h2 h3 hb hi' hi₂]⟩
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem chk_sound (hq : q.Prime) {oF lab : ℕ → ℕ} {W : ℚ} (h : Chk q n (rp q n) oF lab W)
    {K : Finset (Cond q n)} (hK : K ∈ components q n (essConds q n))
    (hK2 : ∀ C ∈ K, 2 ≤ codim q n C) : weight q n K ≤ W := by
  classical
  have hq' := hq.isPrimePow
  rw [rp_eq_pfree_chr hq n] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  change ∀ e ∈ (nfree q n).divisors, OrdOK q e (oF e) at h1
  change ∀ i ∈ range (nfree q n), lab (q * i % nfree q n) = lab i at h2
  change ∀ d ∈ n.divisors, ∀ i ∈ range (nfree q n), d ∣ oF (ordAdd (nfree q n) (rp q d * i)) →
      lab ((i + nfree q n / rp q d) % nfree q n) = lab i at h3
  change ∀ ℓ ∈ (range (nfree q n)).image lab, wsum q n (nfree q n) oF lab ℓ ≤ W at h4
  obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hK
  -- a point of the fibre of `C₀` and its label
  obtain ⟨d₀, hd₀, x₀, hx₀, -, hC₀eq⟩ := (mem_essConds_iff hq').mp hC₀
  obtain ⟨i₀, hi₀⟩ := exists_dfree_mul_eq (Nat.dvd_of_mem_divisors hd₀) hx₀
  have hi₀f : i₀ ∈ fibre q n C₀ := by
    rw [mem_fibre, hC₀eq]; simp only; rw [hi₀]; exact mem_orbit_self d₀ x₀
  set ℓ := lab i₀.val
  have hsub : component q n (essConds q n) C₀ ⊆
      (essConds q n).filter fun C => 2 ≤ codim q n C ∧ ∃ i ∈ fibre q n C, lab i.val = ℓ := by
    intro C hC
    obtain ⟨hCe, hsame⟩ := Finset.mem_filter.mp hC
    exact Finset.mem_filter.mpr ⟨hCe, hK2 C hC,
      (lab_sameComp hq h1 h2 h3 hsame ℓ).mp ⟨i₀, hi₀f, rfl⟩⟩
  have hL : ∀ C ∈ essConds q n, ∀ i ∈ fibre q n C, ∀ i' ∈ fibre q n C,
      lab i.val = ℓ → lab i'.val = ℓ := by
    intro C hC i hi i' hi' hli
    rw [lab_fibre hq h1 h2 h3 hC hi hi']; exact hli
  calc weight q n (component q n (essConds q n) C₀)
      ≤ weight q n ((essConds q n).filter
          fun C => 2 ≤ codim q n C ∧ ∃ i ∈ fibre q n C, lab i.val = ℓ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = wsum q n (nfree q n) oF lab ℓ := by
        rw [weight_filter_eq hq' (fun i => lab i.val = ℓ) hL]
        unfold wsum
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [rp_eq_pfree_chr hq d]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k < nfree q n :=
          (Finset.mem_range.mp hk).trans_le (Nat.div_le_self _ _)
        rw [tcodim_natCast h1, ZMod.val_cast_of_lt hk']
        rfl
    _ ≤ W := h4 ℓ (Finset.mem_image.2 ⟨i₀.val, Finset.mem_range.2 (ZMod.val_lt _), rfl⟩)

end Sound

end MorganMullen.Exact
