import MorganMullen.CertDefs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.CharP.Algebra

/-!
# Certificate checker: soundness (Proposition 8.5)

* Packed vectors (`dig`, `mkVec`, `Good`) and the Kronecker-substitution multiplication `mulMod`
  modulo `f`, with `ev : ℕ → R` mapping a packed vector to `∑ dig_i θ^i`
  (`mulMod_spec`, `mulSpec_mulMod`).
* Generic powering (`powMod_spec`, `orbit_spec`, `powDigits_spec`), Pratt certificates
  (`prattOK_sound`), and the order criterion (`orderOf_eq_of_check`).
* Normality via spanning families (`spanD`, `checkD_sound`), finite rings with an element of order
  `|R| - 1` (`pow_surj_of_orderOf`, `isField_of_pow_surj`), transport along ring isomorphisms.
* The model `𝔽_p[x]/(f)` (`Mdl`) and the soundness of the record check (`checkRec_sound`).
-/

namespace MorganMullen.Cert

open Finset

/-! ### Digits and packed vectors -/

lemma dig_eq (k A i : ℕ) : dig k A i = A / (2 ^ k) ^ i % 2 ^ k := by
  unfold dig
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, pow_mul]

lemma dig_lt (k A i : ℕ) : dig k A i < 2 ^ k := by
  rw [dig_eq]; exact Nat.mod_lt _ (by positivity)

lemma dig_zero (k i : ℕ) : dig k 0 i = 0 := by simp [dig_eq]

/-- base-`b` expansion. -/
lemma expand_base (b : ℕ) (hb : 0 < b) :
    ∀ (L x : ℕ), x < b ^ L → x = ∑ i ∈ range L, x / b ^ i % b * b ^ i
  | 0, x, hx => by simp at hx; simp [hx]
  | L + 1, x, hx => by
    have h1 : x / b < b ^ L := by
      rw [Nat.div_lt_iff_lt_mul hb]; rwa [← pow_succ]
    have ih := expand_base b hb L (x / b) h1
    rw [Finset.sum_range_succ']
    have e : ∀ i ∈ range L, x / b ^ (i + 1) % b * b ^ (i + 1) = b * (x / b / b ^ i % b * b ^ i) := by
      intro i _
      rw [pow_succ', ← Nat.div_div_eq_div_mul]; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← ih]
    simp only [pow_zero, Nat.div_one, mul_one]
    exact (Nat.div_add_mod x b).symm

lemma expand (k L A : ℕ) (h : A < (2 ^ k) ^ L) : A = ∑ i ∈ range L, dig k A i * (2 ^ k) ^ i := by
  simp_rw [dig_eq]; exact expand_base _ (by positivity) L A h

lemma sum_digits_lt (k : ℕ) : ∀ (L : ℕ) (e : ℕ → ℕ), (∀ i < L, e i < 2 ^ k) →
    ∑ i ∈ range L, e i * (2 ^ k) ^ i < (2 ^ k) ^ L
  | 0, e, _ => by simp
  | L + 1, e, he => by
    rw [Finset.sum_range_succ]
    have ih := sum_digits_lt k L e (fun i hi => he i (by omega))
    have h1 := he L (by omega)
    have hB : 0 < (2 : ℕ) ^ k := by positivity
    calc ∑ i ∈ range L, e i * (2 ^ k) ^ i + e L * (2 ^ k) ^ L
        < (2 ^ k) ^ L + e L * (2 ^ k) ^ L := by omega
      _ = (e L + 1) * (2 ^ k) ^ L := by ring
      _ ≤ 2 ^ k * (2 ^ k) ^ L := Nat.mul_le_mul_right _ h1
      _ = (2 ^ k) ^ (L + 1) := by ring

lemma dig_sum (k : ℕ) : ∀ (L : ℕ) (e : ℕ → ℕ), (∀ i < L, e i < 2 ^ k) → ∀ j,
    dig k (∑ i ∈ range L, e i * (2 ^ k) ^ i) j = if j < L then e j else 0
  | 0, e, _, j => by simp [dig_zero]
  | L + 1, e, he, j => by
    have hB : 0 < (2 : ℕ) ^ k := by positivity
    have ih := dig_sum k L (fun i => e (i + 1)) (fun i hi => he (i + 1) (by omega))
    have hsplit : ∑ i ∈ range (L + 1), e i * (2 ^ k) ^ i
        = e 0 + 2 ^ k * ∑ i ∈ range L, e (i + 1) * (2 ^ k) ^ i := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, mul_one, pow_succ]
      rw [add_comm]; congr 1
      apply Finset.sum_congr rfl; intro i _; ring
    have h0 := he 0 (by omega)
    rw [hsplit]
    rcases j with _ | j
    · simp only [dig_eq, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
      simp
    · have := ih j
      rw [dig_eq] at this ⊢
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt h0, zero_add, this]
      simp

/-- `Good A`: `A` encodes a reduced vector of length `N`. -/
def Good (p N k A : ℕ) : Prop := A < (2 ^ k) ^ N ∧ ∀ i < N, dig k A i < p

lemma foldl_add_sum (n : ℕ) (g : ℕ → ℕ) (x : ℕ) :
    (List.range n).foldl (fun acc j => acc + g j) x = x + ∑ j ∈ range n, g j := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp [add_assoc]

lemma mkVec_eq (p N k : ℕ) (e : ℕ → ℕ) :
    mkVec p N k e = ∑ i ∈ range N, e i % p * (2 ^ k) ^ i := by
  unfold mkVec
  rw [foldl_add_sum (g := fun i => (e i % p) <<< (k * i)), zero_add]
  apply Finset.sum_congr rfl; intro i _
  rw [Nat.shiftLeft_eq, pow_mul]

section
variable {p N k : ℕ} (hp : 0 < p) (hpk : p ≤ 2 ^ k)
include hp hpk

lemma dig_mkVec (e : ℕ → ℕ) {i : ℕ} (hi : i < N) : dig k (mkVec p N k e) i = e i % p := by
  rw [mkVec_eq, dig_sum k N _ (fun j _ => lt_of_lt_of_le (Nat.mod_lt _ hp) hpk), ite_eq_left hi]

lemma good_mkVec (e : ℕ → ℕ) : Good p N k (mkVec p N k e) := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [mkVec_eq]; exact sum_digits_lt k N _ (fun j _ => lt_of_lt_of_le (Nat.mod_lt _ hp) hpk)
  · rw [dig_mkVec hp hpk e hi]; exact Nat.mod_lt _ hp
end

/-- digits of a (non-overflowing) linear combination. -/
lemma dig_lincomb {N k : ℕ} {ι : Type*} (s : Finset ι) (a V : ι → ℕ) (X : ℕ)
    (hX : X < (2 ^ k) ^ N) (hV : ∀ j ∈ s, V j < (2 ^ k) ^ N)
    (hb : ∀ i < N, dig k X i + ∑ j ∈ s, a j * dig k (V j) i < 2 ^ k) {i : ℕ} (hi : i < N) :
    dig k (X + ∑ j ∈ s, a j * V j) i = dig k X i + ∑ j ∈ s, a j * dig k (V j) i := by
  have key : X + ∑ j ∈ s, a j * V j
      = ∑ i ∈ range N, (dig k X i + ∑ j ∈ s, a j * dig k (V j) i) * (2 ^ k) ^ i := by
    have h1 : ∑ j ∈ s, a j * V j = ∑ j ∈ s, a j * ∑ i ∈ range N, dig k (V j) i * (2 ^ k) ^ i :=
      Finset.sum_congr rfl fun j hj => by rw [← expand k N (V j) (hV j hj)]
    rw [h1]; conv_lhs => rw [expand k N X hX]
    simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := s)]
    congr 1; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  rw [key, dig_sum k N _ hb, ite_eq_left hi]

lemma lt_of_good {p N k A : ℕ} (h : Good p N k A) : A < (2 ^ k) ^ N := h.1

/-! ### Convolution -/

lemma conv_sum {S : Type*} [CommSemiring S] (N : ℕ) (a b : ℕ → S) (z : S) :
    ∑ m ∈ range (2 * N), (∑ i ∈ range N, ∑ j ∈ range N, if i + j = m then a i * b j else 0) * z ^ m
      = (∑ i ∈ range N, a i * z ^ i) * (∑ j ∈ range N, b j * z ^ j) := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  rw [Finset.mem_range] at hi hj
  rw [ite_eq_left (Finset.mem_range.2 (by omega)), pow_add]; ring

lemma conv_le {p N : ℕ} (a b : ℕ → ℕ) (ha : ∀ i < N, a i < p) (hb : ∀ j < N, b j < p) (m : ℕ) :
    (∑ i ∈ range N, ∑ j ∈ range N, if i + j = m then a i * b j else 0) ≤ N * N * (p * p) := by
  calc (∑ i ∈ range N, ∑ j ∈ range N, if i + j = m then a i * b j else 0)
      ≤ ∑ i ∈ range N, ∑ j ∈ range N, p * p := by
        apply Finset.sum_le_sum; intro i hi; apply Finset.sum_le_sum; intro j hj
        rw [Finset.mem_range] at hi hj
        split_ifs
        · exact Nat.mul_le_mul (ha i hi).le (hb j hj).le
        · exact Nat.zero_le _
    _ = N * N * (p * p) := by simp [Finset.sum_const, Finset.card_range]; ring



lemma bound_aux {N p k : ℕ} (hB : 2 * N ^ 3 * p ^ 3 < 2 ^ k) :
    N * N * (p * p) + N * (N * N * (p * p) * p) < 2 ^ k := by
  have e1 : N * N * (p * p) + N * (N * N * (p * p) * p) = (N * p) ^ 2 + (N * p) ^ 3 := by ring
  have e3 : 2 * N ^ 3 * p ^ 3 = 2 * (N * p) ^ 3 := by ring
  rw [e1]; rw [e3] at hB
  rcases Nat.eq_zero_or_pos (N * p) with h | h
  · rw [h]; simp
  · have : (N * p) ^ 2 ≤ (N * p) ^ 3 := Nat.pow_le_pow_right h (by norm_num)
    omega

section Ring
variable {R : Type*} [CommRing R]

/-- the element of `R` encoded by a packed vector. -/
def ev (N k : ℕ) (θ : R) (A : ℕ) : R := ∑ i ∈ range N, (dig k A i : R) * θ ^ i

lemma natCast_mod_eq {p : ℕ} (hp : (p : R) = 0) (x : ℕ) : ((x % p : ℕ) : R) = x := by
  conv_rhs => rw [← Nat.mod_add_div x p]
  push_cast; rw [hp]; ring

section Packed
variable {p N k : ℕ} (hp0 : 0 < p) (hpk : p ≤ 2 ^ k) (hp : (p : R) = 0) (θ : R)
include hp0 hpk hp

lemma ev_mkVec (e : ℕ → ℕ) : ev N k θ (mkVec p N k e) = ∑ i ∈ range N, (e i : R) * θ ^ i := by
  unfold ev; apply sum_congr rfl; intro i hi
  rw [dig_mkVec hp0 hpk e (mem_range.1 hi), natCast_mod_eq hp]

lemma ev_unitV {j : ℕ} (hj : j < N) : ev N k θ (unitV p N k j) = θ ^ j := by
  unfold unitV
  rw [ev_mkVec hp0 hpk hp]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (range N) j, ite_eq_left (mem_range.2 hj)]

lemma ev_mulX (hN : 0 < N) (F : ℕ) (hθ : θ ^ N = -∑ i ∈ range N, (dig k F i : R) * θ ^ i) (T : ℕ) :
    ev N k θ (mulX p N k F T) = θ * ev N k θ T := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  unfold mulX
  simp only [Nat.add_sub_cancel]
  rw [ev_mkVec hp0 hpk hp]
  set d := dig k T N' with hd
  have hs : (((p - d % p : ℕ)) : R) = -(d : R) := by
    rw [Nat.cast_sub (Nat.mod_lt _ hp0).le, hp, natCast_mod_eq hp]; ring
  push_cast
  rw [hs]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have h1 : ∑ i ∈ range (N' + 1), (if i = 0 then (0 : R) else (dig k T (i - 1) : R)) * θ ^ i
      = ∑ i ∈ range N', (dig k T i : R) * θ ^ (i + 1) := by
    rw [Finset.sum_range_succ']; simp
  have h2 : θ * ev (N' + 1) k θ T = ∑ i ∈ range N', (dig k T i : R) * θ ^ (i + 1) + d * θ ^ (N' + 1) := by
    unfold ev; rw [Finset.mul_sum, Finset.sum_range_succ]
    congr 1
    · apply sum_congr rfl; intro i _; ring
    · rw [hd]; ring
  rw [h1, h2, hθ]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

theorem mulMod_spec (hB : 2 * N ^ 3 * p ^ 3 < 2 ^ k) (T : Array ℕ)
    (hT : ∀ j < N, Good p N k (T.getD j 0) ∧ ev N k θ (T.getD j 0) = θ ^ (N + j))
    {A A' : ℕ} (hA : Good p N k A) (hA' : Good p N k A') :
    Good p N k (mulMod p N k T A A') ∧ ev N k θ (mulMod p N k T A A') = ev N k θ A * ev N k θ A' := by
  refine ⟨good_mkVec hp0 hpk _, ?_⟩
  have hBpos : 0 < (2 : ℕ) ^ k := by positivity
  set c : ℕ → ℕ := fun m =>
    ∑ i ∈ range N, ∑ j ∈ range N, if i + j = m then dig k A i * dig k A' j else 0 with hcdef
  have hb2 := bound_aux hB
  have hcle : ∀ m, c m ≤ N * N * (p * p) := conv_le _ _ hA.2 hA'.2
  have hc : ∀ m, c m < 2 ^ k := fun m => lt_of_le_of_lt (hcle m) (by omega)
  have hC : A * A' = ∑ m ∈ range (2 * N), c m * (2 ^ k) ^ m := by
    conv_lhs => rw [expand k N A hA.1, expand k N A' hA'.1]
    exact (conv_sum N _ _ _).symm
  have hdC : ∀ m < 2 * N, dig k (A * A') m = c m := fun m hm => by
    rw [hC, dig_sum k _ c (fun i _ => hc i), ite_eq_left hm]
  have hlow : A * A' &&& (2 ^ (k * N) - 1) = A * A' % (2 ^ k) ^ N := by
    rw [Nat.and_two_pow_sub_one_eq_mod, pow_mul]
  have hlowlt : A * A' % (2 ^ k) ^ N < (2 ^ k) ^ N := Nat.mod_lt _ (by positivity)
  have hdlow : ∀ i < N, dig k (A * A' % (2 ^ k) ^ N) i = dig k (A * A') i := by
    intro i hi
    rw [dig_eq, dig_eq]
    obtain ⟨t, ht⟩ : ∃ t, N = i + (t + 1) := ⟨N - i - 1, by omega⟩
    rw [ht, pow_add, Nat.mod_mul_right_div_self, pow_succ, Nat.mod_mod_of_dvd _ (dvd_mul_left _ _)]
  have hTg : ∀ j ∈ range N, T.getD j 0 < (2 ^ k) ^ N := fun j hj => (hT j (mem_range.1 hj)).1.1
  have hbnd : ∀ i < N, dig k (A * A' % (2 ^ k) ^ N) i +
      ∑ j ∈ range N, dig k (A * A') (N + j) * dig k (T.getD j 0) i < 2 ^ k := by
    intro i hi
    rw [hdlow i hi, hdC i (by omega)]
    have : ∑ j ∈ range N, dig k (A * A') (N + j) * dig k (T.getD j 0) i
        ≤ ∑ j ∈ range N, N * N * (p * p) * p := by
      apply Finset.sum_le_sum; intro j hj
      rw [hdC (N + j) (by rw [mem_range] at hj; omega)]
      exact Nat.mul_le_mul (hcle _) ((hT j (mem_range.1 hj)).1.2 i hi).le
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    have := hcle i
    omega
  have hS : (List.range N).foldl (fun acc j => acc + dig k (A * A') (N + j) * T.getD j 0)
      (A * A' &&& (2 ^ (k * N) - 1))
      = A * A' % (2 ^ k) ^ N + ∑ j ∈ range N, dig k (A * A') (N + j) * T.getD j 0 := by
    rw [foldl_add_sum, hlow]
  unfold mulMod
  simp only
  rw [hS, ev_mkVec hp0 hpk hp]
  have hdS : ∀ i ∈ range N, ((dig k (A * A' % (2 ^ k) ^ N +
      ∑ j ∈ range N, dig k (A * A') (N + j) * T.getD j 0) i : ℕ) : R)
      = (c i : R) + ∑ j ∈ range N, (c (N + j) : R) * (dig k (T.getD j 0) i : R) := by
    intro i hi
    rw [mem_range] at hi
    rw [dig_lincomb (range N) _ _ _ hlowlt hTg hbnd hi, hdlow i hi, hdC i (by omega)]
    push_cast
    apply congrArg; apply sum_congr rfl; intro j hj
    rw [hdC (N + j) (by rw [mem_range] at hj; omega)]
  rw [sum_congr rfl (fun i hi => by rw [hdS i hi])]
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hTe : ∀ j ∈ range N, ∑ i ∈ range N, (c (N + j) : R) * (dig k (T.getD j 0) i : R) * θ ^ i
      = (c (N + j) : R) * θ ^ (N + j) := by
    intro j hj
    rw [← (hT j (mem_range.1 hj)).2]; unfold ev; rw [Finset.mul_sum]
    apply sum_congr rfl; intro i _; ring
  rw [sum_congr rfl hTe, ← Finset.sum_range_add (fun m => (c m : R) * θ ^ m), ← two_mul]
  have hcast : ∀ m, (c m : R) = ∑ i ∈ range N, ∑ j ∈ range N,
      if i + j = m then (dig k A i : R) * (dig k A' j : R) else 0 := by
    intro m; simp only [hcdef]; push_cast; rfl
  simp_rw [hcast]
  exact conv_sum N _ _ θ

end Packed

/-! ### Generic powering -/

/-- multiplicativity of an operation `mul` on `Good` elements. -/
structure MulSpec (G : ℕ → Prop) (e : ℕ → R) (mul : ℕ → ℕ → ℕ) (one : ℕ) : Prop where
  good_one : G one
  ev_one : e one = 1
  good_mul : ∀ {x y}, G x → G y → G (mul x y)
  ev_mul : ∀ {x y}, G x → G y → e (mul x y) = e x * e y


section Spec
variable {G : ℕ → Prop} {e : ℕ → R} {mul : ℕ → ℕ → ℕ} {one : ℕ}

theorem powMod_spec (hs : MulSpec G e mul one) :
    ∀ (n b : ℕ), G b → G (powMod mul one b n) ∧ e (powMod mul one b n) = e b ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b hb
  rw [powMod]
  by_cases h0 : n = 0
  · subst h0; simp [hs.good_one, hs.ev_one]
  by_cases h1 : n = 1
  · subst h1; simp [hb]
  simp only [h0, h1, dite_false]
  obtain ⟨g, hg⟩ := ih (n / 2) (by omega) b hb
  have gg := hs.good_mul g g
  have egg := hs.ev_mul g g
  split_ifs with h2
  · refine ⟨hs.good_mul gg hb, ?_⟩
    rw [hs.ev_mul gg hb, egg, hg, ← pow_add, ← pow_succ]
    congr 1; omega
  · refine ⟨gg, ?_⟩
    rw [egg, hg, ← pow_add]
    congr 1; omega

lemma iterL_getElem? {α : Type} (f : α → α) :
    ∀ (n : ℕ) (a : α) (i : ℕ), i < n → (iterL f a n)[i]? = some (f^[i] a)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, 0, _ => by simp [iterL]
  | n + 1, a, i + 1, h => by
    simp only [iterL, List.getElem?_cons_succ]
    rw [iterL_getElem? f n (f a) i (by omega), Function.iterate_succ_apply]

lemma iterL_getD {α : Type} (f : α → α) (n : ℕ) (a d : α) {i : ℕ} (hi : i < n) :
    (iterL f a n).toArray.getD i d = f^[i] a := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, iterL_getElem? f n a i hi]; rfl

/-- the orbit `P[i] = b^(m^i)`. -/
theorem orbit_spec (hs : MulSpec G e mul one) (m n b : ℕ) (hb : G b) {i : ℕ} (hi : i < n) :
    G ((iterL (fun u => powMod mul one u m) b n).toArray.getD i 0) ∧
      e ((iterL (fun u => powMod mul one u m) b n).toArray.getD i 0) = e b ^ (m ^ i) := by
  rw [iterL_getD _ _ _ _ hi]
  clear hi
  induction i with
  | zero => simp [hb]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := powMod_spec hs m _ ih.1
    exact ⟨h1, by rw [h2, ih.2, ← pow_mul, pow_succ]⟩

theorem iterMul_spec (hs : MulSpec G e mul one) (n c : ℕ) (hc : G c) {i : ℕ} (hi : i < n) :
    G ((iterL (fun b => mul b c) one n).toArray.getD i 0) ∧
      e ((iterL (fun b => mul b c) one n).toArray.getD i 0) = e c ^ i := by
  rw [iterL_getD _ _ _ _ hi]
  clear hi
  induction i with
  | zero => simp [hs.good_one, hs.ev_one]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨hs.good_mul ih.1 hc, by rw [hs.ev_mul ih.1 hc, ih.2, pow_succ]⟩

theorem powDigits_spec (hs : MulSpec G e mul one) (m N : ℕ) (hm : 0 < m) (P : Array ℕ) (x : R)
    (hP : ∀ i < N, G (P.getD i 0) ∧ e (P.getD i 0) = x ^ (m ^ i)) {E : ℕ} (hE : E < m ^ N) :
    G (powDigits mul one m N P E) ∧ e (powDigits mul one m N P E) = x ^ E := by
  have key : ∀ n ≤ N, G ((List.range n).foldl (fun acc i =>
      if E / m ^ i % m = 0 then acc else mul acc (powMod mul one (P.getD i 0) (E / m ^ i % m))) one) ∧
      e ((List.range n).foldl (fun acc i =>
      if E / m ^ i % m = 0 then acc else mul acc (powMod mul one (P.getD i 0) (E / m ^ i % m))) one)
        = x ^ (∑ i ∈ range n, E / m ^ i % m * m ^ i) := by
    intro n hn
    induction n with
    | zero => simp [hs.good_one, hs.ev_one]
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ]
      obtain ⟨hp1, hp2⟩ := hP n (by omega)
      split_ifs with hz
      · rw [hz, zero_mul, add_zero]; exact ⟨ih1, ih2⟩
      · obtain ⟨q1, q2⟩ := powMod_spec hs (E / m ^ n % m) _ hp1
        refine ⟨hs.good_mul ih1 q1, ?_⟩
        rw [hs.ev_mul ih1 q1, ih2, q2, hp2, ← pow_mul, ← pow_add, mul_comm (m ^ n)]
  have := key N le_rfl
  rw [← expand_base m hm N E hE] at this
  exact this
end Spec


section Packed2
variable {p N k : ℕ} (hp0 : 0 < p) (hpk : p ≤ 2 ^ k) (hp : (p : R) = 0) (θ : R)
include hp0 hpk hp

theorem table_spec (hN : 0 < N) (F : ℕ) (hθ : θ ^ N = -∑ i ∈ range N, (dig k F i : R) * θ ^ i)
    {j : ℕ} (hj : j < N) :
    Good p N k ((table p N k F).getD j 0) ∧ ev N k θ ((table p N k F).getD j 0) = θ ^ (N + j) := by
  unfold table
  rw [iterL_getD _ _ _ _ hj]
  clear hj
  induction j with
  | zero =>
    refine ⟨good_mkVec hp0 hpk _, ?_⟩
    simp only [Function.iterate_zero, id]
    rw [ev_mulX hp0 hpk hp θ hN F hθ, ev_unitV hp0 hpk hp θ (by omega), ← pow_succ']
    congr 1; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨good_mkVec hp0 hpk _, ?_⟩
    rw [ev_mulX hp0 hpk hp θ hN F hθ, ih.2, ← pow_succ']
    congr 1

theorem mulSpec_mulMod (hN : 0 < N) (hB : 2 * N ^ 3 * p ^ 3 < 2 ^ k) (F : ℕ)
    (hθ : θ ^ N = -∑ i ∈ range N, (dig k F i : R) * θ ^ i) :
    MulSpec (Good p N k) (ev N k θ) (mulMod p N k (table p N k F)) (oneV p N k) where
  good_one := good_mkVec hp0 hpk _
  ev_one := by rw [oneV, ev_unitV hp0 hpk hp θ hN, pow_zero]
  good_mul hx hy := (mulMod_spec hp0 hpk hp θ hB _ (fun j hj => table_spec hp0 hpk hp θ hN F hθ hj) hx hy).1
  ev_mul hx hy := (mulMod_spec hp0 hpk hp θ hB _ (fun j hj => table_spec hp0 hpk hp θ hN F hθ hj) hx hy).2

omit hp0 hpk hp in
lemma unitV_eq (hp2 : 2 ≤ p) {j : ℕ} (hj : j < N) : unitV p N k j = 2 ^ (k * j) := by
  unfold unitV
  rw [mkVec_eq, pow_mul]
  have : ∀ i ∈ range N, (if i = j then 1 else 0) % p * (2 ^ k) ^ i = if j = i then (2 ^ k) ^ i else 0 := by
    intro i _
    split_ifs with h1 h2 h2
    · rw [Nat.one_mod_eq_one.2 (by omega), one_mul]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  rw [sum_congr rfl this, Finset.sum_ite_eq, ite_eq_left (mem_range.2 hj)]

lemma ev_two_pow (hp2 : 2 ≤ p) {j : ℕ} (hj : j < N) : ev N k θ (2 ^ (k * j)) = θ ^ j := by
  rw [← unitV_eq hp2 hj, ev_unitV hp0 hpk hp θ hj]

theorem lc_spec (hB : 2 * N ^ 3 * p ^ 3 < 2 ^ k) (h : ℕ) (V : Array ℕ)
    (hV : ∀ col < N, Good p N k (V.getD col 0)) :
    ev N k θ (mkVec p N k (dig k (lc p N k h V)))
      = ∑ col ∈ range N, ((dig k h col % p : ℕ) : R) * ev N k θ (V.getD col 0) := by
  have hb2 := bound_aux hB
  unfold lc
  rw [foldl_add_sum, ev_mkVec hp0 hpk hp]
  have hVlt : ∀ j ∈ range N, V.getD j 0 < (2 ^ k) ^ N := fun j hj => (hV j (mem_range.1 hj)).1
  have hbnd : ∀ i < N, dig k 0 i + ∑ col ∈ range N, (dig k h col % p) * dig k (V.getD col 0) i
      < 2 ^ k := by
    intro i hi
    rw [dig_zero, zero_add]
    have : ∑ col ∈ range N, (dig k h col % p) * dig k (V.getD col 0) i ≤ ∑ col ∈ range N, p * p :=
      Finset.sum_le_sum fun col hc =>
        Nat.mul_le_mul (Nat.mod_lt _ hp0).le ((hV col (mem_range.1 hc)).2 i hi).le
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    have h3 : N * (p * p) ≤ N * N * (p * p) := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simp
      · exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left N h0)
    omega
  have hdig : ∀ i ∈ range N, ((dig k (0 + ∑ col ∈ range N, (dig k h col % p) * V.getD col 0) i : ℕ) : R)
      = ∑ col ∈ range N, ((dig k h col % p : ℕ) : R) * (dig k (V.getD col 0) i : R) := by
    intro i hi
    rw [dig_lincomb (range N) _ _ 0 (by positivity) hVlt hbnd (mem_range.1 hi), dig_zero, zero_add]
    push_cast; rfl
  rw [sum_congr rfl (fun i hi => by rw [hdig i hi])]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro col _
  unfold ev; rw [Finset.mul_sum]
  apply sum_congr rfl; intro i _; ring

end Packed2


/-! ### Modular exponentiation, factor removal, Pratt certificates -/

section Primes

lemma mulSpec_zmod (m : ℕ) (hm : 0 < m) :
    MulSpec (fun x => x < m) (fun x : ℕ => (x : ZMod m)) (fun x y => x * y % m) (1 % m) where
  good_one := Nat.mod_lt _ hm
  ev_one := by simp
  good_mul _ _ := Nat.mod_lt _ hm
  ev_mul _ _ := by simp

lemma powModNat_spec (a e m : ℕ) (hm : 0 < m) :
    powModNat a e m < m ∧ (powModNat a e m : ZMod m) = (a : ZMod m) ^ e := by
  have := powMod_spec (mulSpec_zmod m hm) e (a % m) (Nat.mod_lt _ hm)
  simpa [powModNat] using this

lemma divOut_dvd {q : ℕ} (hq : q.Prime) (f : ℕ) :
    ∀ (fuel m : ℕ), q ∣ m → q ∣ divOut m f fuel ∨ q ∣ f
  | 0, m, h => Or.inl (by simpa [divOut] using h)
  | fuel + 1, m, h => by
    unfold divOut
    split_ifs with hc
    · have hm : m = f * (m / f) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.2.2)).symm
      rw [hm] at h
      rcases (Nat.Prime.dvd_mul hq).1 h with h1 | h1
      · exact Or.inr h1
      · exact divOut_dvd hq f fuel _ h1
    · exact Or.inl h

lemma removeFactors_dvd {q : ℕ} (hq : q.Prime) :
    ∀ (fs : List ℕ) (m : ℕ), q ∣ m → q ∣ removeFactors m fs ∨ ∃ f ∈ fs, q ∣ f
  | [], m, h => Or.inl h
  | f :: fs, m, h => by
    simp only [removeFactors]
    rcases divOut_dvd hq f m m h with h1 | h1
    · rcases removeFactors_dvd hq fs _ h1 with h2 | ⟨g, hg, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨g, List.mem_cons_of_mem _ hg, h2⟩
    · exact Or.inr ⟨f, List.mem_cons_self, h1⟩

lemma mem_of_removeFactors {fs : List ℕ} {m : ℕ} (hfs : ∀ f ∈ fs, f.Prime) (h : removeFactors m fs = 1)
    {q : ℕ} (hq : q.Prime) (hqm : q ∣ m) : q ∈ fs := by
  rcases removeFactors_dvd hq fs m hqm with h1 | ⟨f, hf, h1⟩
  · rw [h] at h1; exact absurd (Nat.le_of_dvd one_pos h1) (by have := hq.two_le; omega)
  · rwa [(Nat.prime_dvd_prime_iff_eq hq (hfs f hf)).1 h1]

lemma entryOK_sound {known : List ℕ} (hk : ∀ x ∈ known, x.Prime) {e : ℕ × ℕ × List ℕ}
    (h : entryOK known e = true) : e.1.Prime := by
  obtain ⟨p, a, fs⟩ := e
  simp only [entryOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hp2, ha⟩, hfs⟩, hrem⟩ := h
  have hp0 : 0 < p := by omega
  apply lucas_primality p (a : ZMod p)
  · obtain ⟨_, h2⟩ := powModNat_spec a (p - 1) p hp0
    rw [← h2, ha, Nat.cast_one]
  · intro q hq hqd
    have hqf : q ∈ fs := mem_of_removeFactors (fun f hf => hk f (hfs f hf).1) hrem hq hqd
    obtain ⟨_, hne⟩ := hfs q hqf
    obtain ⟨h1, h2⟩ := powModNat_spec a ((p - 1) / q) p hp0
    rw [← h2]
    intro hc
    apply hne
    have : (powModNat a ((p - 1) / q) p : ZMod p) = ((1 : ℕ) : ZMod p) := by rw [hc, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)] at this
    exact this

theorem prattOK_sound : ∀ (l : List (ℕ × ℕ × List ℕ)) (known : List ℕ), (∀ x ∈ known, x.Prime) →
    prattOK known l = true → ∀ e ∈ l, e.1.Prime
  | [], _, _, _ => by simp
  | e :: rest, known, hk, h => by
    simp only [prattOK, Bool.and_eq_true] at h
    have he := entryOK_sound hk h.1
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact he
    · exact prattOK_sound rest (e.1 :: known) (fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact he
        · exact hk y hy) h.2 x hx

theorem orderOf_eq_of_check {M' : Type*} [Monoid M'] (x : M') (M : ℕ) (hM : 0 < M)
    (primes : List ℕ) (hpr : ∀ l ∈ primes, l.Prime) (hx : x ^ M = 1)
    (hne : ∀ l ∈ primes, x ^ (M / l) ≠ 1) (hrem : removeFactors M primes = 1) : orderOf x = M :=
  orderOf_eq_of_pow_and_pow_div_prime hM hx fun q hq hqM =>
    hne q (mem_of_removeFactors hpr hrem hq hqM)

end Primes


/-! ### Normality: from a spanning family to coordinates fixed by `x ↦ x^(p^rd)` -/

/-- `w` is normal over every "`𝔽_{q^d}`" (`d ∣ n`), expressed intrinsically. -/
def SpanProp (S : Type*) [CommRing S] (q n : ℕ) (w : S) : Prop :=
  ∀ d, d ∣ n → ∀ y : S, ∃ c : Fin (n / d) → S, (∀ t, c t ^ q ^ d = c t) ∧
    y = ∑ t, c t * w ^ (q ^ (d * t))

theorem spanD (p : ℕ) [Fact p.Prime] [CharP R p] (N rd m : ℕ) (hN : N = rd * m)
    (θ β : R) (u : ℕ → R) (hβ : β ^ p ^ rd = β)
    (hspan : ∀ y : R, ∃ e : ℕ → ℕ, y = ∑ i ∈ range N, (e i : R) * θ ^ i)
    (h : ℕ → ℕ → ℕ)
    (hrep : ∀ kk < N, θ ^ kk = ∑ col ∈ range N, (h kk col : R) * (β ^ (col % rd) * u (col / rd)))
    (y : R) : ∃ c : Fin m → R, (∀ t, c t ^ p ^ rd = c t) ∧ y = ∑ t, c t * u t := by
  obtain ⟨e, rfl⟩ := hspan y
  have : ExpChar R p := ExpChar.prime (Fact.out)
  set a : ℕ → ℕ := fun col => ∑ kk ∈ range N, e kk * h kk col with ha
  set c' : ℕ → R := fun t => ∑ col ∈ range N,
    if col / rd = t then (a col : R) * β ^ (col % rd) else 0 with hc'
  refine ⟨fun t => c' t, fun t => ?_, ?_⟩
  · have hφ : ∀ x : R, x ^ p ^ rd = iterateFrobenius R p rd x := fun x => (iterateFrobenius_def ..).symm
    rw [hφ]
    simp only [hc', map_sum]
    apply sum_congr rfl; intro col _
    split_ifs
    · rw [map_mul, map_pow, map_natCast, ← hφ, hβ]
    · exact map_zero _
  · rw [Fin.sum_univ_eq_sum_range (fun t => c' t * u t) m]
    have h1 : ∑ kk ∈ range N, (e kk : R) * θ ^ kk
        = ∑ col ∈ range N, (a col : R) * (β ^ (col % rd) * u (col / rd)) := by
      rw [sum_congr rfl (fun kk hk => by rw [hrep kk (mem_range.1 hk)])]
      simp_rw [Finset.mul_sum, ha]
      rw [Finset.sum_comm]
      apply sum_congr rfl; intro col _
      push_cast; rw [Finset.sum_mul]
      apply sum_congr rfl; intro kk _; ring
    rw [h1]
    simp only [hc', Finset.sum_mul]
    rw [Finset.sum_comm]
    apply sum_congr rfl; intro col hcol
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, ite_eq_left]
    · ring
    · rw [mem_range] at hcol ⊢
      subst hN
      rcases Nat.eq_zero_or_pos rd with h0 | h0
      · subst h0; simp at hcol
      · exact (Nat.div_lt_iff_lt_mul h0).2 (by rw [mul_comm]; exact hcol)

/-! ### Finite rings with an element of order `|R| - 1` -/

theorem pow_surj_of_orderOf [Fintype R] [Nontrivial R] (w : R)
    (hw : orderOf w = Fintype.card R - 1) : ∀ x : R, x ≠ 0 → ∃ k : ℕ, w ^ k = x := by
  classical
  have hc : 1 < Fintype.card R := Fintype.one_lt_card_iff_nontrivial.2 inferInstance
  set m := Fintype.card R - 1 with hm
  have hm0 : m ≠ 0 := by omega
  have hw1 : w ^ m = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hu : IsUnit w := IsUnit.of_pow_eq_one hw1 hm0
  set S := (range m).image (fun k => w ^ k) with hS
  have hcard : S.card = m := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have := pow_injOn_Iio_orderOf (x := w)
    rw [hw] at this
    exact this (by simpa using ha) (by simpa using hb) hab
  have hsub : S ⊆ univ.erase 0 := by
    intro x hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact Finset.mem_erase.2 ⟨(hu.pow k).ne_zero, Finset.mem_univ _⟩
  have heq : S = univ.erase 0 := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard])
  intro x hx
  have : x ∈ S := by rw [heq]; exact Finset.mem_erase.2 ⟨hx, Finset.mem_univ _⟩
  rw [hS, Finset.mem_image] at this
  obtain ⟨k, _, hk⟩ := this
  exact ⟨k, hk⟩

theorem isField_of_pow_surj [Nontrivial R] (w : R) (hw : IsUnit w)
    (h : ∀ x : R, x ≠ 0 → ∃ k : ℕ, w ^ k = x) : IsField R where
  exists_pair_ne := exists_pair_ne R
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    obtain ⟨k, rfl⟩ := h x hx
    obtain ⟨u, hu⟩ := hw.pow k
    rw [← hu]
    exact ⟨↑u⁻¹, u.mul_inv⟩

/-- transport along a ring isomorphism. -/
theorem transport {S E : Type*} [CommRing S] [CommRing E] (e : S ≃+* E) (q n : ℕ) (w : S)
    (hprim : w ≠ 0 ∧ ∀ x : S, x ≠ 0 → ∃ k : ℕ, w ^ k = x) (hspan : SpanProp S q n w) :
    (e w ≠ 0 ∧ ∀ x : E, x ≠ 0 → ∃ k : ℕ, e w ^ k = x) ∧ SpanProp E q n (e w) := by
  refine ⟨⟨fun h => hprim.1 (e.injective (by rw [h, map_zero])), fun x hx => ?_⟩, ?_⟩
  · obtain ⟨k, hk⟩ := hprim.2 (e.symm x) (fun h => hx (by simpa using congrArg e h))
    exact ⟨k, by rw [← map_pow, hk, RingEquiv.apply_symm_apply]⟩
  · intro d hd y
    obtain ⟨c, hc, hy⟩ := hspan d hd (e.symm y)
    refine ⟨fun t => e (c t), fun t => by rw [← map_pow, hc], ?_⟩
    rw [← e.apply_symm_apply y, hy, map_sum]
    simp [map_mul, map_pow]


/-! ### Soundness of the normality check for one divisor -/

lemma getD_ofFn {N : ℕ} (f : Fin N → ℕ) {i : ℕ} (hi : i < N) : (Array.ofFn f).getD i 0 = f ⟨i, hi⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hi]; rfl

theorem checkD_sound {p N k : ℕ} (hp0 : 0 < p) (hpk : p ≤ 2 ^ k) (hp : (p : R) = 0) (hp2 : 2 ≤ p)
    [Fact p.Prime] [CharP R p] (θ : R) (T : Array ℕ)
    (hs : MulSpec (Good p N k) (ev N k θ) (mulMod p N k T) (oneV p N k))
    (hB : 2 * N ^ 3 * p ^ 3 < 2 ^ k)
    (hspan : ∀ y : R, ∃ e : ℕ → ℕ, y = ∑ i ∈ range N, (e i : R) * θ ^ i)
    {r n d : ℕ} (hr : 0 < r) (hN : N = r * n) (hd : d ∣ n) (hd0 : 0 < d)
    (P : Array ℕ) (w : R) (hP : ∀ i < N, Good p N k (P.getD i 0) ∧ ev N k θ (P.getD i 0) = w ^ (p ^ i))
    (h : checkD p r n N k T P d = true) (y : R) :
    ∃ c : Fin (n / d) → R, (∀ t, c t ^ (p ^ r) ^ d = c t) ∧ y = ∑ t, c t * w ^ ((p ^ r) ^ (d * t)) := by
  unfold checkD at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hβ, hall⟩ := h
  set rd := r * d with hrd
  set u : ℕ → ℕ := fun t => P.getD (r * (d * t)) 0 with hu
  set Bd := goodify p N k ((List.range (n / d)).foldl (fun acc t => mulMod p N k T acc (u t))
    (oneV p N k)) with hBd
  have hBdg : Good p N k Bd := good_mkVec hp0 hpk _
  set β := ev N k θ Bd with hβdef
  have hββ : β ^ p ^ rd = β := by
    have := (powMod_spec hs (p ^ rd) Bd hBdg).2
    rw [hβ] at this; exact this.symm
  have hnd : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  have hNrd : N = rd * (n / d) := by rw [hN, hrd, mul_assoc, ← hnd]
  have hu_spec : ∀ t < n / d, Good p N k (u t) ∧ ev N k θ (u t) = w ^ ((p ^ r) ^ (d * t)) := by
    intro t ht
    have hlt : r * (d * t) < N := by
      rw [hNrd, hrd, mul_assoc]
      apply Nat.mul_lt_mul_of_pos_left _ hr
      exact Nat.mul_lt_mul_of_pos_left ht hd0
    obtain ⟨g1, g2⟩ := hP _ hlt
    exact ⟨g1, by rw [g2, ← pow_mul, ← mul_assoc, pow_mul]⟩
  have hrd0 : 0 < rd := Nat.mul_pos hr hd0
  have hBP := fun j (hj : j < rd) => iterMul_spec hs rd Bd hBdg hj
  have hcol : ∀ col < N, col / rd < n / d := fun col hc =>
    (Nat.div_lt_iff_lt_mul hrd0).2 (by rw [mul_comm, ← hNrd]; exact hc)
  set V := Array.ofFn (n := N) (fun col : Fin N => if col.val % rd = 0 then u (col.val / rd)
    else mulMod p N k T ((iterL (fun b => mulMod p N k T b Bd) (oneV p N k) rd).toArray.getD
      (col.val % rd) 0) (u (col.val / rd))) with hV
  have hVs : ∀ col < N, Good p N k (V.getD col 0) ∧
      ev N k θ (V.getD col 0) = β ^ (col % rd) * w ^ ((p ^ r) ^ (d * (col / rd))) := by
    intro col hc
    rw [hV, getD_ofFn _ hc]
    obtain ⟨u1, u2⟩ := hu_spec _ (hcol col hc)
    simp only
    split_ifs with hz
    · exact ⟨u1, by rw [u2, hz, pow_zero, one_mul]⟩
    · obtain ⟨b1, b2⟩ := hBP (col % rd) (Nat.mod_lt _ hrd0)
      exact ⟨hs.good_mul b1 u1, by rw [hs.ev_mul b1 u1, b2, u2]⟩
  have hrep : ∀ kk < N, θ ^ kk = ∑ col ∈ range N,
      ((dig k ((gauss p N k V).getD kk 0) col % p : ℕ) : R) *
        (β ^ (col % rd) * w ^ ((p ^ r) ^ (d * (col / rd)))) := by
    intro kk hk
    have e1 := congrArg (ev N k θ) (hall kk hk)
    rw [lc_spec hp0 hpk hp θ hB _ V (fun col hc => (hVs col hc).1),
      ev_two_pow hp0 hpk hp θ hp2 hk] at e1
    rw [← e1]
    apply sum_congr rfl; intro col hc
    rw [(hVs col (mem_range.1 hc)).2]
  obtain ⟨c, hc1, hc2⟩ := spanD p N rd (n / d) hNrd θ β (fun t => w ^ ((p ^ r) ^ (d * t))) hββ hspan
    _ hrep y
  refine ⟨c, fun t => by rw [← pow_mul, ← hrd]; exact hc1 t, hc2⟩


end Ring

/-! ### The model `𝔽_p[x]/(f)` -/

section Model
open Polynomial

variable (p N k F : ℕ)

/-- `f = x^N + ∑_{i<N} f_i x^i` with `f_i = dig k F i`. -/
noncomputable def fpoly : (ZMod p)[X] :=
  X ^ N + ∑ i : Fin N, C ((dig k F i : ℕ) : ZMod p) * X ^ (i : ℕ)

variable [hpF : Fact p.Prime]

omit hpF in
lemma fpoly_monic : (fpoly p N k F).Monic := monic_X_pow_add (degree_sum_fin_lt _)

lemma fpoly_natDegree : (fpoly p N k F).natDegree = N := by
  unfold fpoly
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]; exact degree_sum_fin_lt _

lemma eval₂_fpoly {S : Type*} [CommRing S] (g : ZMod p →+* S) (x : S) :
    (fpoly p N k F).eval₂ g x = x ^ N + ∑ i ∈ range N, (dig k F i : S) * x ^ i := by
  unfold fpoly
  rw [eval₂_add, eval₂_X_pow, eval₂_finsetSum]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => (dig k F i : S) * x ^ i) N]
  apply sum_congr rfl; intro i _
  rw [eval₂_mul, eval₂_C, eval₂_X_pow, map_natCast]

/-- the model ring. -/
abbrev Mdl := AdjoinRoot (fpoly p N k F)

lemma mdl_p : ((p : ℕ) : Mdl p N k F) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) (Mdl p N k F)), ZMod.natCast_self, map_zero]

lemma mdl_root : (AdjoinRoot.root (fpoly p N k F)) ^ N =
    -∑ i ∈ range N, (dig k F i : Mdl p N k F) * (AdjoinRoot.root (fpoly p N k F)) ^ i := by
  have h := AdjoinRoot.eval₂_root (fpoly p N k F)
  rw [eval₂_fpoly] at h
  exact eq_neg_of_add_eq_zero_left h

/-- the power basis. -/
noncomputable abbrev pbM := AdjoinRoot.powerBasis' (fpoly_monic p N k F)

lemma pbM_dim : (pbM p N k F).dim = N := by
  rw [AdjoinRoot.powerBasis'_dim, fpoly_natDegree]

omit hpF in
lemma pbM_basis (i : Fin (pbM p N k F).dim) :
    (pbM p N k F).basis i = (AdjoinRoot.root (fpoly p N k F)) ^ (i : ℕ) := by
  rw [PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen]

lemma mdl_span (y : Mdl p N k F) : ∃ e : ℕ → ℕ,
    y = ∑ i ∈ range N, (e i : Mdl p N k F) * (AdjoinRoot.root (fpoly p N k F)) ^ i := by
  classical
  set pb := pbM p N k F
  refine ⟨fun i => if h : i < pb.dim then (pb.basis.repr y ⟨i, h⟩).val else 0, ?_⟩
  conv_lhs => rw [← pb.basis.sum_repr y]
  have hr : range N = range pb.dim := by rw [pbM_dim]
  rw [hr, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl; intro i _
  simp only [Fin.is_lt, dite_true, Fin.eta]
  rw [pbM_basis, Algebra.smul_def, ← map_natCast (algebraMap (ZMod p) (Mdl p N k F)),
    ZMod.natCast_zmod_val]

lemma mdl_ev_inj {A A' : ℕ} (hA : Good p N k A) (hA' : Good p N k A')
    (h : ev N k (AdjoinRoot.root (fpoly p N k F)) A = ev N k (AdjoinRoot.root (fpoly p N k F)) A') :
    A = A' := by
  set pb := pbM p N k F
  set g : Fin pb.dim → ZMod p := fun i => ((dig k A i : ℕ) : ZMod p) - ((dig k A' i : ℕ) : ZMod p)
  have hsum : ∑ i, g i • pb.basis i = 0 := by
    have : ∑ i, g i • pb.basis i = ev N k (AdjoinRoot.root (fpoly p N k F)) A -
        ev N k (AdjoinRoot.root (fpoly p N k F)) A' := by
      unfold ev
      have hr : range N = range pb.dim := by rw [pbM_dim]
      rw [← Finset.sum_sub_distrib, hr,
        ← Fin.sum_univ_eq_sum_range (fun i => (dig k A i : Mdl p N k F) *
          (AdjoinRoot.root (fpoly p N k F)) ^ i - (dig k A' i : Mdl p N k F) *
          (AdjoinRoot.root (fpoly p N k F)) ^ i)]
      apply sum_congr rfl; intro i _
      rw [pbM_basis, Algebra.smul_def, map_sub, map_natCast, map_natCast]; ring
    rw [this, h, sub_self]
  have hg := Fintype.linearIndependent_iff.1 pb.basis.linearIndependent g hsum
  have hd : ∀ i < N, dig k A i = dig k A' i := by
    intro i hi
    have := hg ⟨i, by rw [pbM_dim]; exact hi⟩
    simp only [g, sub_eq_zero] at this
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hA.2 i hi),
      Nat.mod_eq_of_lt (hA'.2 i hi)] at this
    exact this
  rw [expand k N A hA.1, expand k N A' hA'.1]
  exact sum_congr rfl fun i hi => by rw [hd i (mem_range.1 hi)]

noncomputable instance : Fintype (Mdl p N k F) :=
  haveI : Module.Finite (ZMod p) (Mdl p N k F) := (pbM p N k F).finite
  haveI : Finite (Mdl p N k F) := Module.finite_of_finite (ZMod p)
  Fintype.ofFinite _

lemma card_mdl : Fintype.card (Mdl p N k F) = p ^ N := by
  rw [Module.card_fintype (pbM p N k F).basis, ZMod.card, Fintype.card_fin, pbM_dim]

end Model

/-! ### Soundness of the record check -/

theorem checkRec_sound (known : List ℕ) (hk : ∀ x ∈ known, x.Prime) (c : CertRec)
    (hc : checkRec known c = true) (E : Type*) [Field E] [Fintype E]
    (hE : Fintype.card E = c.p ^ (c.r * c.n)) :
    ∃ w : E, (w ≠ 0 ∧ ∀ x : E, x ≠ 0 → ∃ k : ℕ, w ^ k = x) ∧ SpanProp E (c.p ^ c.r) c.n w := by
  unfold checkRec at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hpk, hr⟩, hn⟩, hM⟩, hprimes⟩, hrem⟩, hdiv⟩ := hc
  set p := c.p with hpdef
  set N := c.r * c.n with hNdef
  set k := kOf p N with hkdef
  set F := fromBase p N k c.fdat with hFdef
  set W := fromBase p N k c.wdat with hWdef
  have hpp : p.Prime := hk p hpk
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : 2 ≤ p := hpp.two_le
  have hp0 : 0 < p := by omega
  have hN : 0 < N := Nat.mul_pos hr hn
  have hB : 2 * N ^ 3 * p ^ 3 < 2 ^ k := Nat.lt_log2_self
  have hpk' : p ≤ 2 ^ k := by
    have : p ≤ 2 * N ^ 3 * p ^ 3 := by
      calc p = 1 * 1 * p := by ring
        _ ≤ 2 * N ^ 3 * p ^ 2 * p := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul (by
            calc 1 ≤ 2 := by norm_num
              _ ≤ 2 * N ^ 3 := Nat.le_mul_of_pos_right _ (by positivity))
          exact Nat.one_le_pow _ _ hp0
        _ = 2 * N ^ 3 * p ^ 3 := by ring
    omega
  set R := Mdl p N k F
  set θ : R := AdjoinRoot.root (fpoly p N k F)
  have hpR : ((p : ℕ) : R) = 0 := mdl_p p N k F
  have hθ := mdl_root p N k F
  have hs := mulSpec_mulMod hp0 hpk' hpR θ hN hB F hθ
  have hWg : Good p N k W := good_mkVec hp0 hpk' _
  set w : R := ev N k θ W with hwdef
  have hP := fun i (hi : i < N) => orbit_spec hs p N W hWg hi
  have hpw := fun (e : ℕ) (he : e < p ^ N) =>
    powDigits_spec hs p N hp0 _ w hP he
  set M := p ^ N - 1 with hMdef
  have hpN : 1 < p ^ N := Nat.one_lt_pow (by omega) (by omega)
  have hMlt : M < p ^ N := by omega
  have hM0 : 0 < M := by omega
  have hone := hs.good_one
  -- order
  have hwM : w ^ M = 1 := by
    rw [← (hpw M hMlt).2, hM, hs.ev_one]
  rw [List.all_eq_true] at hprimes
  have hprimes' : ∀ l ∈ c.primes, l.Prime ∧ w ^ (M / l) ≠ 1 := by
    intro l hl
    have := hprimes l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
    refine ⟨hk l this.1, fun h1 => this.2 ?_⟩
    have hlt : M / l < p ^ N := lt_of_le_of_lt (Nat.div_le_self _ _) hMlt
    apply mdl_ev_inj p N k F (hpw _ hlt).1 hone
    rw [(hpw _ hlt).2, h1, hs.ev_one]
  have hord : orderOf w = M := orderOf_eq_of_check w M hM0 c.primes (fun l hl => (hprimes' l hl).1)
    hwM (fun l hl => (hprimes' l hl).2) hrem
  -- field structure
  have hcard : Fintype.card R = p ^ N := card_mdl p N k F
  have : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hpN)
  have hsurj := pow_surj_of_orderOf w (by rw [hord, hcard])
  have hunit : IsUnit w := IsUnit.of_pow_eq_one hwM (by omega)
  have hfield : IsField R := isField_of_pow_surj w hunit hsurj
  have : CharP R p := charP_of_injective_algebraMap (algebraMap (ZMod p) R).injective p
  -- normality
  have hspanR : SpanProp R (p ^ c.r) c.n w := by
    intro d hd y
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    have := List.all_eq_true.1 hdiv d (List.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hn hd)))
    rw [ite_eq_left ⟨by omega, Nat.mod_eq_zero_of_dvd hd⟩] at this
    exact checkD_sound hp0 hpk' hpR hp2 θ _ hs hB (mdl_span p N k F) hr hNdef hd hd0 _ w
      (fun i hi => hP i hi) this y
  -- transport
  let _ : Field R := hfield.toField
  have e : R ≃+* E := FiniteField.ringEquivOfCardEq (K := R) (K' := E) (by rw [hcard, hE])
  exact ⟨e w, transport e (p ^ c.r) c.n w ⟨hunit.ne_zero, hsurj⟩ hspanR⟩



end MorganMullen.Cert
