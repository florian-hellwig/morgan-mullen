import MorganMullen.ModelBasic

/-!
# Section 3 (combinatorial part): Lemma 3.3 on the structure of components

* (a) `component_supp_qOrbit_prod`: the support of a component is a union of sets `O × ℤ/p^a`
  over `q`-orbits `O`; `sameComp_iff_qChain`: components can be read off from the `q`-orbits of
  the `η`'s;
* (b) `fibre_coset`: a single fibre is a coset of `μ_{d'}`;
* (c) `codim_one_singleton`, `codim_ge_two_component`: codimension-one conditions are singleton
  components, and other components contain no codimension-one condition;
* `components_partition`: the components partition the set of conditions.
-/

set_option linter.unusedSectionVars false

namespace MorganMullen
namespace Model
open Finset

variable {q n : ℕ} [NeZero n]

lemma mem_fibre {C : Cond q n} {i : ZMod (nfree q n)} :
    i ∈ fibre q n C ↔ ((dfree q C.1 : ℕ) : ZMod (nfree q n)) * i ∈ C.2 := by
  simp [fibre]

lemma zero_mem_resSet (d : ℕ) : (0 : ZMod (pa q n)) ∈ resSet q n d := by
  simp [resSet]

lemma dfree_one : dfree q 1 = 1 := pfree_one _

lemma one_dvd_codim (C : Cond q n) : IsEssential q n (1, C.2) := one_dvd _

/-- The level-one condition through `i`. -/
def lev1 (i : ZMod (nfree q n)) : Cond q n := (1, orbit q n 1 i)

lemma lev1_mem_essConds (i : ZMod (nfree q n)) : lev1 i ∈ essConds q n := by
  classical
  simp only [essConds, Finset.mem_filter]
  refine ⟨mem_conds.mpr ⟨1, by simp [NeZero.ne n], i, ?_, rfl⟩, one_dvd _⟩
  rw [mem_targets]
  have : bigN q n 1 = nfree q n := by simp [bigN, dfree_one]
  rw [this]
  simp

lemma mem_fibre_lev1 (hq : IsPrimePow q) (i : ZMod (nfree q n)) (j : ℕ) :
    (q : ZMod (nfree q n)) ^ j * i ∈ fibre q n (lev1 i) := by
  rw [mem_fibre]
  simp only [lev1, dfree_one, Nat.cast_one, one_mul]
  exact (mem_orbit_iff hq).mpr ⟨j, by rw [pow_one]⟩

lemma adj_of_mem_fibre {C C' : Cond q n} {i : ZMod (nfree q n)} (h : i ∈ fibre q n C)
    (h' : i ∈ fibre q n C') : Adj q n C C' := by
  refine ⟨(i, 0), ?_, (i, 0), ?_, 0, by simp, by simp⟩
  · exact Finset.mem_product.mpr ⟨h, zero_mem_resSet _⟩
  · exact Finset.mem_product.mpr ⟨h', zero_mem_resSet _⟩

/-- **Lemma 3.3 (a)**. -/
theorem sameComp_iff_qChain (hq : IsPrimePow q) {C C' : Cond q n} :
    SameComp q n (essConds q n) C C' ↔
      Relation.EqvGen (fun C C' => C ∈ essConds q n ∧ C' ∈ essConds q n ∧
        ∃ i ∈ fibre q n C, ∃ i' ∈ fibre q n C', QRel q n i i') C C' := by
  constructor
  · intro h
    refine Relation.EqvGen.mono ?_ _ _ h
    rintro a b ⟨ha, hb, π, hπ, π', hπ', j, h1, -⟩
    exact ⟨ha, hb, π.1, (Finset.mem_product.mp hπ).1, π'.1, (Finset.mem_product.mp hπ').1, j, h1⟩
  · intro h
    induction h with
    | rel a b hab =>
      obtain ⟨ha, hb, i, hi, i', hi', j, rfl⟩ := hab
      have hL := lev1_mem_essConds (q := q) (n := n) i
      have h1 : SameComp q n (essConds q n) a (lev1 i) :=
        Relation.EqvGen.rel _ _ ⟨ha, hL, adj_of_mem_fibre hi (by simpa using mem_fibre_lev1 hq i 0)⟩
      have h2 : SameComp q n (essConds q n) b (lev1 i) :=
        Relation.EqvGen.rel _ _ ⟨hb, hL, adj_of_mem_fibre hi' (mem_fibre_lev1 hq i j)⟩
      exact h1.trans _ _ _ h2.symm
    | refl a => exact Relation.EqvGen.refl a
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2


/-- At level `1` every residue `u ∈ ℤ/p^a` occurs. -/
lemma mem_resSet_one (u : ZMod (pa q n)) : u ∈ resSet q n 1 := by
  simp [resSet, dval]

/-- The pairs of the level-one condition through `i` are `O × ℤ/p^a`, `O` the `q`-orbit of `i`:
every `(q^j i, u)` is a pair of it. -/
lemma mem_pairs_lev1 (hq : IsPrimePow q) (i : ZMod (nfree q n)) (j : ℕ) (u : ZMod (pa q n)) :
    ((q : ZMod (nfree q n)) ^ j * i, u) ∈ pairs q n (lev1 i) :=
  Finset.mem_product.mpr ⟨mem_fibre_lev1 hq i j, mem_resSet_one u⟩

/-- **Lemma 3.3 (a)**, last sentence: the support of a component `𝒞` of `ℰ` is a union of sets
`O × ℤ/p^a` over `q`-orbits `O ⊆ μ_{n'}`. A pair `(η, u) = (ζ^i, u)` is written `(i, u)`; the
support of `𝒞` is the union of the pair orbits meeting the pairs of its members. If `(i, u)` lies
in the pair orbit of a pair `π` of some `C ∈ 𝒞`, then for every `j` and every `u' ∈ ℤ/p^a` the
pair `(q^j i, u')`, i.e. `(η^{q^j}, u')`, is a pair of some `C' ∈ 𝒞` (the level-one condition
through `π.1`, which is adjacent to `C`), so it lies in the support of `𝒞`. -/
theorem component_supp_qOrbit_prod (hq : IsPrimePow q) {𝒞 : Finset (Cond q n)}
    (h𝒞 : 𝒞 ∈ components q n (essConds q n)) {C : Cond q n} (hC : C ∈ 𝒞)
    {π : ZMod (nfree q n) × ZMod (pa q n)} (hπ : π ∈ pairs q n C) {i : ZMod (nfree q n)}
    {u : ZMod (pa q n)} (hiu : PairRel q n π (i, u)) (j : ℕ) (u' : ZMod (pa q n)) :
    ∃ C' ∈ 𝒞, ((q : ZMod (nfree q n)) ^ j * i, u') ∈ pairs q n C' := by
  classical
  obtain ⟨C₀, -, rfl⟩ := Finset.mem_image.mp h𝒞
  obtain ⟨hCe, hC₀C⟩ := Finset.mem_filter.mp hC
  obtain ⟨k, hk, -⟩ := hiu
  have hL := lev1_mem_essConds (q := q) (n := n) π.1
  have hadj : Adj q n C (lev1 π.1) :=
    adj_of_mem_fibre (Finset.mem_product.mp hπ).1 (by simpa using mem_fibre_lev1 hq π.1 0)
  refine ⟨lev1 π.1, Finset.mem_filter.mpr ⟨hL, hC₀C.trans _ _ _ (Relation.EqvGen.rel _ _
    ⟨hCe, hL, hadj⟩)⟩, ?_⟩
  have e : (q : ZMod (nfree q n)) ^ j * (i, u).1 = (q : ZMod (nfree q n)) ^ (j + k) * π.1 := by
    rw [hk, ← mul_assoc, ← pow_add]
  simp only at e
  rw [e]
  exact mem_pairs_lev1 hq π.1 (j + k) u'


lemma natCast_mul_eq_nsmul {m : ℕ} (k : ℕ) (x : ZMod m) : (k : ZMod m) * x = k • x := by
  rw [nsmul_eq_mul]

lemma qpow_mul_eq_self_iff (hq : IsPrimePow q) (o : ℕ) (x : ZMod (nfree q n)) :
    (q : ZMod (nfree q n)) ^ o * x = x ↔ ordMod q (addOrderOf x) ∣ o := by
  rw [ordMod_dvd_iff_modEq]
  have h1 : 1 ≤ q ^ o := Nat.one_le_pow _ _ hq.pos
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' h1, addOrderOf_dvd_iff_nsmul_eq_zero, ← natCast_mul_eq_nsmul,
    Nat.cast_sub h1, sub_mul, Nat.cast_one, one_mul, Nat.cast_pow, sub_eq_zero]

lemma orbit_eq_singleton (hq : IsPrimePow q) {d : ℕ} {x : ZMod (nfree q n)}
    (h : ordMod q (addOrderOf x) ∣ d) : orbit q n d x = {x} := by
  ext y
  rw [mem_orbit_iff hq, Finset.mem_singleton]
  constructor
  · rintro ⟨j, rfl⟩
    rw [← pow_mul]
    exact (qpow_mul_eq_self_iff hq _ x).mpr (h.mul_right j)
  · rintro rfl; exact ⟨0, by simp⟩

lemma addOrderOf_pos' (x : ZMod (nfree q n)) : 0 < addOrderOf x :=
  addOrderOf_pos x

lemma addOrderOf_dvd_nfree (x : ZMod (nfree q n)) : addOrderOf x ∣ nfree q n := by
  have := addOrderOf_dvd_card (x := x)
  rwa [ZMod.card] at this

lemma one_le_tcodim (hq : IsPrimePow q) (x : ZMod (nfree q n)) : 1 ≤ tcodim q n x :=
  ordMod_pos (coprime_q_of_dvd_nfree hq (NeZero.ne n) (addOrderOf_dvd_nfree x))
    (addOrderOf_pos' x).ne'

theorem one_le_codim (hq : IsPrimePow q) {C : Cond q n} (hC : C ∈ conds q n) :
    1 ≤ codim q n C := by
  obtain ⟨d, -, x, -, rfl⟩ := mem_conds.mp hC
  rw [codim_orbit hq]
  exact one_le_tcodim hq x

lemma essConds_subset : essConds q n ⊆ conds q n := by
  classical
  intro C hC; exact (Finset.mem_filter.mp hC).1

lemma mem_essConds {C : Cond q n} : C ∈ essConds q n ↔ C ∈ conds q n ∧ C.1 ∣ codim q n C := by
  classical
  simp [essConds, IsEssential]

lemma addOrderOf_mul_dvd {m : ℕ} (k : ℕ) (x : ZMod m) : addOrderOf ((k : ZMod m) * x) ∣ addOrderOf x := by
  rw [natCast_mul_eq_nsmul]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by rw [smul_comm, addOrderOf_nsmul_eq_zero, smul_zero])

/-- A codimension-one essential condition is `(1, {x})` with `q x = x`. -/
lemma codim_one_struct (hq : IsPrimePow q) {C : Cond q n} (hC : C ∈ essConds q n)
    (h1 : codim q n C = 1) :
    ∃ x, C = (1, {x}) ∧ ordMod q (addOrderOf x) = 1 := by
  obtain ⟨hC', hess⟩ := mem_essConds.mp hC
  obtain ⟨d, -, x, -, rfl⟩ := mem_conds.mp hC'
  rw [codim_orbit hq] at h1 hess
  have hd : d = 1 := Nat.dvd_one.mp (h1 ▸ hess)
  subst hd
  refine ⟨x, ?_, h1⟩
  have h1' : ordMod q (addOrderOf x) = 1 := h1
  rw [orbit_eq_singleton hq (by rw [h1'])]

lemma codim_one_of_fibre (hq : IsPrimePow q) {x : ZMod (nfree q n)}
    (hx : ordMod q (addOrderOf x) = 1) {C' : Cond q n} (hC' : C' ∈ essConds q n)
    (hmem : x ∈ fibre q n C') : C' = (1, {x}) := by
  obtain ⟨hC'c, hess⟩ := mem_essConds.mp hC'
  obtain ⟨d, -, y, -, rfl⟩ := mem_conds.mp hC'c
  rw [mem_fibre] at hmem
  have hco := (codim_eq_of_mem hq hC'c hmem).1
  have hdvd : addOrderOf (((dfree q d : ℕ) : ZMod _) * x) ∣ addOrderOf x := addOrderOf_mul_dvd _ x
  have hord : tcodim q n (((dfree q d : ℕ) : ZMod _) * x) = 1 := by
    unfold tcodim
    have := ordMod_dvd_ordMod (q := q) hdvd
    rw [hx] at this
    exact Nat.dvd_one.mp this
  rw [hco, hord] at hess
  have hd : d = 1 := Nat.dvd_one.mp hess
  subst hd
  simp only [dfree_one, Nat.cast_one, one_mul] at hmem
  rw [← orbit_eq_of_mem hq hmem, orbit_eq_singleton hq (by rw [hx])]

/-- **Lemma 3.3 (c)**. -/
theorem codim_one_singleton (hq : IsPrimePow q) {C : Cond q n} (hC : C ∈ essConds q n)
    (h1 : codim q n C = 1) :
    C.1 = 1 ∧ component q n (essConds q n) C = {C} := by
  classical
  obtain ⟨x, rfl, hx⟩ := codim_one_struct hq hC h1
  refine ⟨rfl, ?_⟩
  have hxf : x ∈ fibre q n ((1, {x}) : Cond q n) := by
    rw [mem_fibre]; simp [dfree_one]
  have key : ∀ a b, SameComp q n (essConds q n) a b → (a = (1, {x}) ↔ b = (1, {x})) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      obtain ⟨ha, hb, π, hπ, π', hπ', j, h1, -⟩ := hab
      have hπ1 := (Finset.mem_product.mp hπ).1
      have hπ'1 := (Finset.mem_product.mp hπ').1
      have hqx : (q : ZMod (nfree q n)) ^ j * x = x := (qpow_mul_eq_self_iff hq j x).mpr (hx ▸ one_dvd _)
      constructor
      · rintro rfl
        have : π.1 = x := by
          rw [mem_fibre] at hπ1; simpa [dfree_one] using hπ1
        rw [this, hqx] at h1
        exact codim_one_of_fibre hq hx hb (h1 ▸ hπ'1)
      · rintro rfl
        have : π'.1 = x := by
          rw [mem_fibre] at hπ'1; simpa [dfree_one] using hπ'1
        -- x = q^j π.1, so π.1 = x
        have hpx : π.1 = x := by
          have hu : IsUnit ((q : ZMod (nfree q n)) ^ j) := ((qUnit (n := n) hq) ^ j).isUnit.map
            (MonoidHom.id _) |> fun h => by simpa using ((qUnit (n := n) hq) ^ j).isUnit
          have e1 : (q : ZMod (nfree q n)) ^ j * π.1 = (q : ZMod (nfree q n)) ^ j * x := by
            rw [← h1, this, hqx]
          exact hu.mul_left_cancel e1
        exact codim_one_of_fibre hq hx ha (hpx ▸ hπ1)
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  ext C'
  simp only [component, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩; exact ((key _ _ h).mp rfl)
  · rintro rfl; exact ⟨hC, Relation.EqvGen.refl _⟩

theorem components_partition (ℰ : Finset (Cond q n)) :
    (∀ K ∈ components q n ℰ, K ⊆ ℰ) ∧
    (∀ C ∈ ℰ, ∃! K, K ∈ components q n ℰ ∧ C ∈ K) := by
  classical
  refine ⟨fun K hK => ?_, fun C hC => ⟨component q n ℰ C, ⟨Finset.mem_image_of_mem _ hC, ?_⟩, ?_⟩⟩
  · obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hK
    exact Finset.filter_subset _ _
  · exact Finset.mem_filter.mpr ⟨hC, Relation.EqvGen.refl _⟩
  · rintro K ⟨hK, hCK⟩
    obtain ⟨C0, -, rfl⟩ := Finset.mem_image.mp hK
    have h0 : SameComp q n ℰ C0 C := (Finset.mem_filter.mp hCK).2
    ext C'
    simp only [component, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h0.symm.trans _ _ _ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h0.trans _ _ _ h2⟩

theorem codim_ge_two_component (hq : IsPrimePow q) {C : Cond q n} (hC : C ∈ essConds q n)
    (h2 : 2 ≤ codim q n C) : ∀ C' ∈ component q n (essConds q n) C, 2 ≤ codim q n C' := by
  classical
  intro C' hC'
  obtain ⟨hC'e, hsame⟩ := Finset.mem_filter.mp hC'
  by_contra hlt
  have h1 : codim q n C' = 1 := by
    have := one_le_codim hq (essConds_subset hC'e); omega
  have := (codim_one_singleton hq hC'e h1).2
  have hmem : C ∈ component q n (essConds q n) C' :=
    Finset.mem_filter.mpr ⟨hC, hsame.symm⟩
  rw [this, Finset.mem_singleton] at hmem
  subst hmem
  omega


/-- **Lemma 3.3 (b)**. -/
theorem fibre_coset {d : ℕ} (hd : d ∣ n) (i : ZMod (nfree q n)) :
    (univ.filter fun i' : ZMod (nfree q n) =>
        ((dfree q d : ℕ) : ZMod _) * i' = ((dfree q d : ℕ) : ZMod _) * i) =
      (range (dfree q d)).image fun t => i + ((t * bigN q n d : ℕ) : ZMod (nfree q n)) := by
  have hdN := dfree_mul_bigN (q := q) hd
  have hdpos : 0 < dfree q d := dfree_pos (ne_zero_of_dvd_ne_zero (NeZero.ne n) hd)
  ext i'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
  constructor
  · intro h
    set y := i' - i with hy
    have h0 : ((dfree q d : ℕ) : ZMod (nfree q n)) * y = 0 := by rw [hy, mul_sub, h, sub_self]
    have h0' : ((dfree q d * y.val : ℕ) : ZMod (nfree q n)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    obtain ⟨c, hc⟩ := h0'
    have hc' : dfree q d * y.val = dfree q d * (bigN q n d * c) := by
      rw [← mul_assoc, hdN]; exact hc
    have hyv : y.val = bigN q n d * c := Nat.eq_of_mul_eq_mul_left hdpos hc'
    refine ⟨c, ?_, ?_⟩
    · have hlt : y.val < nfree q n := ZMod.val_lt y
      rw [hyv, ← hdN, mul_comm (dfree q d)] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    · have : ((c * bigN q n d : ℕ) : ZMod (nfree q n)) = y := by
        rw [mul_comm, ← hyv, ZMod.natCast_zmod_val]
      rw [this, hy, add_sub_cancel]
  · rintro ⟨t, -, rfl⟩
    have : ((dfree q d : ℕ) : ZMod (nfree q n)) * ((t * bigN q n d : ℕ) : ZMod (nfree q n)) = 0 := by
      rw [← Nat.cast_mul, mul_left_comm, hdN, Nat.cast_mul, ZMod.natCast_self, mul_zero]
    rw [mul_add, this, add_zero]

end Model
end MorganMullen
