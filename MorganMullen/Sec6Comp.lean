import MorganMullen.Sec6FaBound

/-!
# Proposition 6.5, computational part: verified checkers

* `oOK c o`: the Boolean check `f_a(o) ≤ u/w` for the values of `a` of a class `c`
  (one fixed `a`, or all `a ≥ a₀`; for `a ≥ v_p(o)` the function decreases in `a`, so it suffices
  to check `a ≤ max(a₀, v_p(o)) + 1`), up to a list of exceptions `(o, a)`; `range_bound` gives
  `f_a(o) ≤ u/w` on a range of `o` (beyond the range, the tail bounds `faX_le_of_kappa3/4` of
  `Sec6FaBound.lean` are used).
* `rsOK p q a o ϑ fac`: the Boolean check `R*_a(o) ≤ ϑ` (`RaStarX`, the local maximum of
  Section 6 with `p` as a parameter): `fac` is a factorisation of `q^o - 1` into primes (checked),
  all divisors `k` are enumerated, the orders `ord_k(q)`, `ord_{k/gcd(k,d')}(q)` are computed and
  verified, and `R_a(k) ≤ ϑ` is checked for the `k` with `ord_k(q) = o`.

The computations themselves are run in `Sec6Runs.lean`.
-/

namespace MorganMullen.Msmall

open MorganMullen Finset

/-! ### Divisors by trial division (as in `Fin32Comp.lean`) -/

/-- `sdAux n i acc`: the divisors `j ∈ [1, i]` of `n` (ascending), prepended to `acc`. -/
def sdAux (n : ℕ) : ℕ → List ℕ → List ℕ
  | 0, acc => acc
  | i + 1, acc => sdAux n i (if n % (i + 1) = 0 then (i + 1) :: acc else acc)

/-- The divisors `≤ √n` of `n`. -/
def smallDivs (n : ℕ) : List ℕ := sdAux n n.sqrt []

/-- All divisors of `n` (`n > 0`), without repetition. -/
def divList (n : ℕ) : List ℕ :=
  let s := smallDivs n
  s ++ (s.filter (fun i => i * i != n)).map (n / ·)

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
    have hlt : i * i < n := lt_of_le_of_ne h1 hii
    have hia' : i < a := by
      by_contra hc; push Not at hc
      have : a * i ≤ i * i := Nat.mul_le_mul_right i hc
      omega
    have : i * a < a * a := Nat.mul_lt_mul_of_pos_right hia' (by omega)
    rw [mul_comm] at this
    omega

lemma toFinset_divList {n : ℕ} (hn : 0 < n) : (divList n).toFinset = n.divisors := by
  ext x; simp [mem_divList hn, hn.ne']

lemma sum_divisors_eq {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 0 < n) (f : ℕ → M) :
    ∑ x ∈ n.divisors, f x = ((divList n).map f).sum := by
  rw [← toFinset_divList hn, List.sum_toFinset _ (nodup_divList hn)]

/-! ### `p`-adic valuation and `p`-free part -/

/-- `v_p(n)` (`0` for `n = 0`). -/
def vpc (p n : ℕ) : ℕ :=
  if _h : 1 < p ∧ 0 < n ∧ n % p = 0 then vpc p (n / p) + 1 else 0
termination_by n
decreasing_by exact Nat.div_lt_self _h.2.1 _h.1

lemma vpc_eq {p : ℕ} (hp : p.Prime) (n : ℕ) : vpc p n = n.factorization p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [vpc]
  split_ifs with h
  · have hd : p ∣ n := Nat.dvd_of_mod_eq_zero h.2.2
    rw [ih _ (Nat.div_lt_self h.2.1 h.1)]
    have hn0 : n / p ≠ 0 := by
      intro h0
      have := Nat.div_mul_cancel hd
      rw [h0, zero_mul] at this; omega
    conv_rhs => rw [← Nat.div_mul_cancel hd]
    rw [Nat.factorization_mul hn0 hp.ne_zero, Finsupp.add_apply, hp.factorization_self]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.factorization_eq_zero_of_not_dvd fun hd =>
        h ⟨hp.one_lt, hn, Nat.mod_eq_zero_of_dvd hd⟩).symm

/-- `n` with all factors `p` removed. -/
def remP (p n : ℕ) : ℕ :=
  if _h : 1 < p ∧ 0 < n ∧ n % p = 0 then remP p (n / p) else n
termination_by n
decreasing_by exact Nat.div_lt_self _h.2.1 _h.1

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

/-! ### The check `f_a(o) ≤ u/w` -/

/-- computable `SN p a o = o p^a f_a(o)`. -/
def SNc (p a o : ℕ) : ℕ :=
  ((divList o).map fun d => if vpc p d ≤ a then p ^ vpc p d * min d (o / d) else 0).sum

lemma SNc_eq {p : ℕ} (hp : p.Prime) (a : ℕ) {o : ℕ} (ho : 0 < o) : SNc p a o = SN p a o := by
  unfold SNc SN
  rw [sum_divisors_eq ho]
  simp only [vpc_eq hp]

/-- `w · o p^a f_a(o) ≤ u · o p^a`. -/
def faOK (p a u w o : ℕ) : Bool := decide (w * SNc p a o ≤ u * (o * p ^ a))

lemma faOK_sound {p a u w o : ℕ} (hp : p.Prime) (ho : 0 < o) (hw : 0 < w)
    (h : faOK p a u w o = true) : faX p a o ≤ (u : ℚ) / w := by
  unfold faOK at h
  rw [decide_eq_true_eq, SNc_eq hp a ho] at h
  rw [faX_eq_SN hp.pos a ho]
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have ho' : (0 : ℚ) < o := by exact_mod_cast ho
  have hw' : (0 : ℚ) < w := by exact_mod_cast hw
  rw [div_le_div_iff₀ (by positivity) hw']
  have : ((w * SN p a o : ℕ) : ℚ) ≤ ((u * (o * p ^ a) : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at this
  linarith

/-- A class of checks: `p`, the values `a` (`a = a₀`, or all `a ≥ a₀` if `inf`), the bound
`u/w`, and the exceptions `(o, a)`. -/
structure FCls where
  p : ℕ
  a0 : ℕ
  inf : Bool
  u : ℕ
  w : ℕ
  exc : List (ℕ × ℕ)

/-- the values of `a` of a class. -/
def FCls.InA (c : FCls) (a : ℕ) : Prop := (c.inf = true ∧ c.a0 ≤ a) ∨ (c.inf = false ∧ a = c.a0)

/-- The check for one `o`. -/
def oOK (c : FCls) (o : ℕ) : Bool :=
  if c.inf then
    !(c.exc.contains (o, max c.a0 (vpc c.p o) + 1)) &&
      (List.range' c.a0 (max c.a0 (vpc c.p o) + 2 - c.a0)).all
        (fun a => c.exc.contains (o, a) || faOK c.p a c.u c.w o)
  else c.exc.contains (o, c.a0) || faOK c.p c.a0 c.u c.w o

lemma oOK_sound (c : FCls) (hp : c.p.Prime) (hw : 0 < c.w) {o : ℕ} (ho : 0 < o)
    (h : oOK c o = true) {a : ℕ} (ha : c.InA a) (hexc : (o, a) ∉ c.exc) :
    faX c.p a o ≤ (c.u : ℚ) / c.w := by
  unfold oOK at h
  rcases ha with ⟨hinf, ha⟩ | ⟨hinf, rfl⟩
  · simp only [hinf, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
      Bool.or_eq_true, List.contains_iff_mem] at h
    obtain ⟨hA, hall⟩ := h
    set A := max c.a0 (vpc c.p o) + 1 with hAdef
    have hAmem : A ∈ List.range' c.a0 (max c.a0 (vpc c.p o) + 2 - c.a0) := by
      rw [List.mem_range'_1]; omega
    have hAexc : (o, A) ∉ c.exc := by
      intro hm; simp [hm] at hA
    have hokA : faOK c.p A c.u c.w o = true := by
      rcases hall A hAmem with h1 | h1
      · exact absurd h1 hAexc
      · exact h1
    rcases le_or_gt a A with haA | haA
    · have hmem : a ∈ List.range' c.a0 (max c.a0 (vpc c.p o) + 2 - c.a0) := by
        rw [List.mem_range'_1]; omega
      rcases hall a hmem with h1 | h1
      · exact absurd h1 hexc
      · exact faOK_sound hp ho hw h1
    · have hb : o.factorization c.p ≤ A := by rw [← vpc_eq hp]; omega
      exact (faX_anti hp.pos ho.ne' hb a haA.le).trans (faOK_sound hp ho hw hokA)
  · simp only [hinf, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, List.contains_iff_mem] at h
    rcases h with h1 | h1
    · exact absurd h1 hexc
    · exact faOK_sound hp ho hw h1

/-- `∀ n ∈ [lo, lo + len), f n`. -/
def allFrom (f : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, len + 1 => f lo && allFrom f (lo + 1) len

lemma allFrom_sound {f : ℕ → Bool} : ∀ {lo len : ℕ}, allFrom f lo len = true →
    ∀ x, lo ≤ x → x < lo + len → f x = true
  | _, 0, _, x, h1, h2 => by omega
  | lo, len + 1, h, x, h1, h2 => by
    simp only [allFrom, Bool.and_eq_true] at h
    rcases Nat.lt_or_eq_of_le h1 with h1 | rfl
    · exact allFrom_sound h.2 x h1 (by omega)
    · exact h.1

/-! ### Several classes at once, with the divisors of `o` computed only once -/

/-- `SNc` with a given list `ds` of the divisors of `o`. -/
def SNd (p a o : ℕ) (ds : List ℕ) : ℕ :=
  (ds.map fun d => if vpc p d ≤ a then p ^ vpc p d * min d (o / d) else 0).sum

/-- `faOK` with a given list of divisors. -/
def faOKd (p a u w o : ℕ) (ds : List ℕ) : Bool := decide (w * SNd p a o ds ≤ u * (o * p ^ a))

/-- `oOK` with a given list of divisors. -/
def oOKd (c : FCls) (o : ℕ) (ds : List ℕ) : Bool :=
  if c.inf then
    !(c.exc.contains (o, max c.a0 (vpc c.p o) + 1)) &&
      (List.range' c.a0 (max c.a0 (vpc c.p o) + 2 - c.a0)).all
        (fun a => c.exc.contains (o, a) || faOKd c.p a c.u c.w o ds)
  else c.exc.contains (o, c.a0) || faOKd c.p c.a0 c.u c.w o ds

lemma oOKd_divList (c : FCls) (o : ℕ) : oOKd c o (divList o) = oOK c o := rfl

/-- The checks of all classes of `cs` at `o` (the divisors of `o` are computed once). -/
def oOKs (cs : List FCls) (o : ℕ) : Bool :=
  let ds := divList o
  cs.all fun c => oOKd c o ds

lemma oOKs_sound {cs : List FCls} {o : ℕ} (h : oOKs cs o = true) {c : FCls} (hc : c ∈ cs) :
    oOK c o = true := by
  unfold oOKs at h
  rw [List.all_eq_true] at h
  rw [← oOKd_divList]
  exact h c hc

/-- **Bound on a range** `[lo, lo + len)` for a class `c` of `cs`. -/
theorem range_bound (cs : List FCls) {c : FCls} (hc : c ∈ cs) (hp : c.p.Prime) (hw : 0 < c.w)
    {lo len : ℕ} (hchk : allFrom (oOKs cs) lo len = true) :
    ∀ o, 0 < o → lo ≤ o → o < lo + len → ∀ a, c.InA a → (o, a) ∉ c.exc →
      faX c.p a o ≤ (c.u : ℚ) / c.w :=
  fun o ho h1 h2 _ ha hexc =>
    oOK_sound c hp hw ho (oOKs_sound (allFrom_sound hchk o h1 h2) hc) ha hexc

/-! ### The local maxima `R*_a(o)` -/

open Classical in
/-- `R_a(k)` with `p` as a parameter (`Ra q a k = RaX (charOf q) q a k`). -/
noncomputable def RaX (p q a k : ℕ) : ℚ :=
  ∑ d ∈ (ordMod q k).divisors.filter (fun d => d.factorization p ≤ a ∧
      d ∣ ordMod q (k / Nat.gcd k (pfree p d))),
    (p : ℚ) ^ d.factorization p / (p : ℚ) ^ a / ordMod q (k / Nat.gcd k (pfree p d))

open Classical in
/-- `R*_a(o)` with `p` as a parameter. -/
noncomputable def RaStarX (p q a o : ℕ) : ℚ :=
  ((q ^ o - 1).divisors.filter fun k => ordMod q k = o).fold max 0 (RaX p q a)

/-- `e = k / gcd(k, d')`. -/
def eD (p k d : ℕ) : ℕ := k / Nat.gcd k (remP p d)

/-- Verification of `ord_e(q) = t`. -/
def verOrd (q e t : ℕ) : Bool :=
  decide (0 < t) && decide (0 < e) && q ^ t % e == 1 % e &&
    t.primeFactorsList.all (fun r => q ^ (t / r) % e != 1 % e)

/-- Candidate for `ord_e(q)` (`e ∣ q^o - 1`): the least divisor `t` of `o` with `q^t ≡ 1`. -/
def ordCand (q o e : ℕ) : ℕ := ((divList o).filter (fun t => q ^ t % e == 1 % e)).foldl min o

/-- computable `R_a(k)` for `ord_k(q) = o`. -/
def RaC (p q a o k : ℕ) : ℚ :=
  ((divList o).map fun d =>
    if vpc p d ≤ a ∧ ordCand q o (eD p k d) % d = 0 then
      (p : ℚ) ^ vpc p d / (p : ℚ) ^ a / (ordCand q o (eD p k d) : ℚ) else 0).sum

/-- The check for one divisor `k` of `q^o - 1`. -/
def kOK (p q a o : ℕ) (ϑ : ℚ) (k : ℕ) : Bool :=
  verOrd q k (ordCand q o k) && (ordCand q o k != o ||
    ((divList o).all (fun d => verOrd q (eD p k d) (ordCand q o (eD p k d))) &&
      decide (RaC p q a o k ≤ ϑ)))

/-- The divisors of `∏ p_i^{e_i}`. -/
def divsF : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | pe :: rest => (List.range (pe.2 + 1)).flatMap (fun j => (divsF rest).map (fun d => pe.1 ^ j * d))

/-- `fac` is a factorisation of `N` into primes. -/
def facOK (fac : List (ℕ × ℕ)) (N : ℕ) : Bool :=
  fac.all (fun pe => decide (2 ≤ pe.1) && pe.1.minFac == pe.1) &&
    (fac.map (fun pe => pe.1 ^ pe.2)).prod == N

/-- The check `R*_a(o) ≤ ϑ`. -/
def rsOK (p q a o : ℕ) (ϑ : ℚ) (fac : List (ℕ × ℕ)) : Bool :=
  decide (0 ≤ ϑ) && decide (0 < o) && facOK fac (q ^ o - 1) && (divsF fac).all (kOK p q a o ϑ)

lemma powmod_iff (q e k : ℕ) : q ^ k % e = 1 % e ↔ (q : ZMod e) ^ k = 1 := by
  have := ZMod.natCast_eq_natCast_iff' (q ^ k) 1 e
  simp only [Nat.cast_pow, Nat.cast_one] at this
  exact this.symm

lemma verOrd_sound {q e t : ℕ} (h : verOrd q e t = true) : ordMod q e = t := by
  simp only [verOrd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨ht, he⟩, h1⟩, h2⟩ := h
  unfold ordMod
  apply orderOf_eq_of_pow_and_pow_div_prime ht ((powmod_iff q e t).1 h1)
  intro r hr hrt hc
  exact h2 r ((Nat.mem_primeFactorsList ht.ne').2 ⟨hr, hrt⟩) ((powmod_iff q e _).2 hc)

lemma mem_divsF : ∀ (fac : List (ℕ × ℕ)), (∀ pe ∈ fac, pe.1.Prime) →
    ∀ k, k ∈ divsF fac ↔ k ∣ (fac.map (fun pe => pe.1 ^ pe.2)).prod
  | [], _, k => by simp [divsF]
  | pe :: rest, hpr, k => by
    have hp : pe.1.Prime := hpr pe (List.mem_cons_self ..)
    have ih := mem_divsF rest (fun x hx => hpr x (List.mem_cons_of_mem _ hx))
    simp only [divsF, List.mem_flatMap, List.mem_range, List.mem_map, List.map_cons,
      List.prod_cons]
    rw [dvd_mul]
    constructor
    · rintro ⟨j, hj, d, hd, rfl⟩
      exact ⟨pe.1 ^ j, d, pow_dvd_pow _ (by omega), (ih d).1 hd, rfl⟩
    · rintro ⟨y, z, hy, hz, rfl⟩
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).1 hy
      exact ⟨j, by omega, z, (ih z).2 hz, rfl⟩

lemma ordMod_dvd_of_dvd {q k o : ℕ} (hk : k ∣ q ^ o - 1) (hq : 1 ≤ q ^ o) : ordMod q k ∣ o := by
  rw [ordMod_dvd_iff_modEq]
  exact (Nat.modEq_iff_dvd' hq).2 hk |>.symm

lemma RaX_eq_RaC {p q a o k : ℕ} (hp : p.Prime) (hko : ordMod q k = o) (ho : 0 < o)
    (hver : ∀ d ∈ divList o, verOrd q (eD p k d) (ordCand q o (eD p k d)) = true) :
    RaX p q a k = RaC p q a o k := by
  unfold RaX RaC
  rw [hko, Finset.sum_filter, sum_divisors_eq ho]
  congr 1
  refine List.map_congr_left fun d hd => ?_
  have hord : ordMod q (k / Nat.gcd k (pfree p d)) = ordCand q o (eD p k d) := by
    have he : eD p k d = k / Nat.gcd k (pfree p d) := by rw [eD, remP_eq hp]
    rw [← he]
    exact verOrd_sound (hver d hd)
  rw [hord, vpc_eq hp]
  by_cases hc : d.factorization p ≤ a ∧ d ∣ ordCand q o (eD p k d)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨hc.1, Nat.mod_eq_zero_of_dvd hc.2⟩)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc),
      ite_eq_right_of_eq_false _ _ (eq_false (fun h => hc ⟨h.1, Nat.dvd_of_mod_eq_zero h.2⟩))]

theorem rsOK_sound {p q a o : ℕ} {ϑ : ℚ} {fac : List (ℕ × ℕ)} (hp : p.Prime)
    (h : rsOK p q a o ϑ fac = true) : RaStarX p q a o ≤ ϑ := by
  simp only [rsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hϑ, ho⟩, hfac⟩, hall⟩ := h
  simp only [facOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hfac
  obtain ⟨hpr, hprod⟩ := hfac
  have hpr' : ∀ pe ∈ fac, pe.1.Prime := fun pe hpe =>
    Nat.prime_def_minFac.2 ⟨(hpr pe hpe).1, (hpr pe hpe).2⟩
  unfold RaStarX
  rw [Finset.fold_max_le]
  refine ⟨hϑ, fun k hk => ?_⟩
  obtain ⟨hkd, hko⟩ := Finset.mem_filter.mp hk
  have hkdvd : k ∣ q ^ o - 1 := Nat.dvd_of_mem_divisors hkd
  have hkmem : k ∈ divsF fac := (mem_divsF fac hpr' k).2 (hprod ▸ hkdvd)
  have hkOK := hall k hkmem
  simp only [kOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
    decide_eq_true_eq] at hkOK
  obtain ⟨hv, hrest⟩ := hkOK
  have hcand := verOrd_sound hv
  rcases hrest with hne | ⟨hver, hle⟩
  · exact absurd (hcand.symm.trans hko) hne
  · rw [RaX_eq_RaC hp hko ho hver]
    exact hle

/-! ### `R*_a(o)` for several `a` at once, and monotonicity in `a` -/

/-- The checks `R*_a(o) ≤ ϑ` for all `(a, ϑ) ∈ as` (the factorisation is checked once). -/
def rsOKs (p q o : ℕ) (as : List (ℕ × ℚ)) (fac : List (ℕ × ℕ)) : Bool :=
  decide (0 < o) && facOK fac (q ^ o - 1) &&
    as.all fun aϑ => decide (0 ≤ aϑ.2) && (divsF fac).all (kOK p q aϑ.1 o aϑ.2)

theorem rsOKs_sound {p q o : ℕ} {as : List (ℕ × ℚ)} {fac : List (ℕ × ℕ)} (hp : p.Prime)
    (h : rsOKs p q o as fac = true) {a : ℕ} {ϑ : ℚ} (hmem : (a, ϑ) ∈ as) :
    RaStarX p q a o ≤ ϑ := by
  simp only [rsOKs, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨ho, hfac⟩, hall⟩ := h
  have h1 := hall (a, ϑ) hmem
  apply rsOK_sound hp
  simp only [rsOK, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨h1.1, ho⟩, hfac⟩, by simpa using h1.2⟩

lemma RaX_nonneg (p q a k : ℕ) : 0 ≤ RaX p q a k := by
  classical
  unfold RaX
  exact Finset.sum_nonneg fun d _ => by positivity

/-- For `a ≥ v_p(ord_k(q))`: `R_{a+1}(k) = R_a(k)/p`. -/
lemma RaX_succ {p q k : ℕ} (a : ℕ) (hk : ordMod q k ≠ 0)
    (ha : (ordMod q k).factorization p ≤ a) : RaX p q (a + 1) k = RaX p q a k / p := by
  classical
  have hall : ∀ b, a ≤ b → ∀ d ∈ (ordMod q k).divisors, d.factorization p ≤ b := by
    intro b hb d hd
    exact ((Nat.factorization_le_iff_dvd (Nat.pos_of_mem_divisors hd).ne' hk).mpr
      (Nat.dvd_of_mem_divisors hd) p).trans (ha.trans hb)
  unfold RaX
  rw [Finset.sum_div]
  have hfilt : ∀ b, a ≤ b → (ordMod q k).divisors.filter (fun d => d.factorization p ≤ b ∧
      d ∣ ordMod q (k / Nat.gcd k (pfree p d))) =
      (ordMod q k).divisors.filter (fun d => d ∣ ordMod q (k / Nat.gcd k (pfree p d))) := by
    intro b hb
    apply Finset.filter_congr
    intro d hd
    exact ⟨fun h => h.2, fun h => ⟨hall b hb d hd, h⟩⟩
  rw [hfilt a le_rfl, hfilt (a + 1) (Nat.le_succ a)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pow_succ]
  ring

/-- `R*_a(o)` decreases in `a` for `a ≥ v_p(o)`. -/
lemma RaStarX_anti {p q o : ℕ} (hp : 0 < p) (ho : o ≠ 0) {A : ℕ} (hA : o.factorization p ≤ A) :
    ∀ a, A ≤ a → RaStarX p q a o ≤ RaStarX p q A o := by
  classical
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => exact le_rfl
  | succ b hb ih =>
    refine le_trans ?_ ih
    unfold RaStarX
    rw [Finset.fold_max_le]
    refine ⟨(Finset.le_fold_max _).2 (Or.inl le_rfl), fun k hk => ?_⟩
    have hko := (Finset.mem_filter.mp hk).2
    have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
    rw [RaX_succ b (by rw [hko]; exact ho) (by rw [hko]; exact hA.trans hb)]
    refine (Finset.le_fold_max _).2 (Or.inr ⟨k, hk, ?_⟩)
    exact div_le_self (RaX_nonneg p q b k) hp1

end MorganMullen.Msmall
