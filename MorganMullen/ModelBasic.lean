import MorganMullen.Model

/-!
# Basic facts about the combinatorial model
-/

namespace MorganMullen
namespace Model
open Finset

variable {q n : ℕ}

lemma chr_prime (hq : IsPrimePow q) : (chr q).Prime :=
  Nat.minFac_prime hq.ne_one

lemma chr_pow_eq (hq : IsPrimePow q) : chr q ^ q.factorization (chr q) = q :=
  hq.minFac_pow_factorization_eq

lemma one_le_factorization_chr (hq : IsPrimePow q) : 1 ≤ q.factorization (chr q) := by
  have := chr_pow_eq hq
  by_contra h
  push Not at h
  have h0 : q.factorization (chr q) = 0 := by omega
  rw [h0, pow_zero] at this
  exact hq.ne_one this.symm

lemma two_le_q (hq : IsPrimePow q) : 2 ≤ q := hq.two_le

variable (q n)

lemma pa_mul_nfree : pa q n * nfree q n = n := pow_mul_pfree _ _

lemma nfree_dvd : nfree q n ∣ n := pfree_dvd _ _

lemma pa_dvd : pa q n ∣ n := Dvd.intro _ (pa_mul_nfree q n)

variable {q n}

lemma coprime_chr_nfree (hq : IsPrimePow q) (hn : n ≠ 0) : Nat.Coprime (chr q) (nfree q n) :=
  coprime_pfree (chr_prime hq) hn

lemma coprime_q_nfree (hq : IsPrimePow q) (hn : n ≠ 0) : Nat.Coprime q (nfree q n) := by
  have := Nat.Coprime.pow_left (q.factorization (chr q)) (coprime_chr_nfree hq hn)
  rwa [chr_pow_eq hq] at this

lemma coprime_q_of_dvd_nfree (hq : IsPrimePow q) (hn : n ≠ 0) {e : ℕ} (he : e ∣ nfree q n) :
    Nat.Coprime q e :=
  Nat.Coprime.coprime_dvd_right he (coprime_q_nfree hq hn)

lemma dfree_dvd_nfree {d : ℕ} (hd : d ∣ n) : dfree q d ∣ nfree q n := pfree_dvd_pfree hd _

lemma bigN_mul_dfree {d : ℕ} (hd : d ∣ n) : bigN q n d * dfree q d = nfree q n :=
  Nat.div_mul_cancel (dfree_dvd_nfree hd)

lemma dfree_mul_bigN {d : ℕ} (hd : d ∣ n) : dfree q d * bigN q n d = nfree q n := by
  rw [mul_comm, bigN_mul_dfree hd]

lemma dfree_pos {d : ℕ} (hd : d ≠ 0) : 0 < dfree q d := pfree_pos _ hd

lemma bigN_pos [NeZero n] {d : ℕ} (hd : d ∣ n) : 0 < bigN q n d := by
  have h := dfree_mul_bigN (q := q) hd
  have : 0 < nfree q n := Nat.pos_of_ne_zero (NeZero.ne _)
  rcases Nat.eq_zero_or_pos (bigN q n d) with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0

section
variable [NeZero n]

/-- `q` as a unit of `ZMod n'`. -/
def qUnit (hq : IsPrimePow q) : (ZMod (nfree q n))ˣ :=
  ZMod.unitOfCoprime q (coprime_q_nfree hq (NeZero.ne n))

@[simp] lemma coe_qUnit (hq : IsPrimePow q) : ((qUnit (n := n) hq : (ZMod (nfree q n))ˣ) : ZMod (nfree q n)) = q :=
  rfl

lemma addOrderOf_unit_mul {m : ℕ} (u : (ZMod m)ˣ) (x : ZMod m) :
    addOrderOf ((u : ZMod m) * x) = addOrderOf x := by
  let f : ZMod m →+ ZMod m := AddMonoidHom.mulLeft (u : ZMod m)
  have hf : Function.Injective f := fun a b h => by
    simpa [f] using congrArg (fun y => (↑u⁻¹ : ZMod m) * y) h
  exact addOrderOf_injective f hf x

lemma addOrderOf_qpow_mul (hq : IsPrimePow q) (k : ℕ) (x : ZMod (nfree q n)) :
    addOrderOf ((q : ZMod (nfree q n)) ^ k * x) = addOrderOf x := by
  have := addOrderOf_unit_mul ((qUnit hq) ^ k) x
  simpa using this

lemma mem_orbit_iff (hq : IsPrimePow q) {d : ℕ} {x y : ZMod (nfree q n)} :
    y ∈ orbit q n d x ↔ ∃ j : ℕ, y = ((q : ZMod (nfree q n)) ^ d) ^ j * x := by
  constructor
  · intro h
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    set u := (qUnit (n := n) hq) ^ d
    have hu : ((u : (ZMod (nfree q n))ˣ) : ZMod (nfree q n)) = (q : ZMod (nfree q n)) ^ d := by
      simp [u]
    have hpos : 0 < orderOf u := orderOf_pos u
    have hle : orderOf u ≤ nfree q n := by
      calc orderOf u ≤ Fintype.card (ZMod (nfree q n))ˣ := orderOf_le_card_univ
        _ ≤ Fintype.card (ZMod (nfree q n)) := Fintype.card_le_of_injective _ Units.val_injective
        _ = nfree q n := ZMod.card _
    refine Finset.mem_image.mpr ⟨j % orderOf u, Finset.mem_range.mpr ?_, ?_⟩
    · exact (Nat.mod_lt _ hpos).trans_le hle
    · rw [← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, pow_mod_orderOf]

lemma mem_orbit_self (d : ℕ) (x : ZMod (nfree q n)) : x ∈ orbit q n d x :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero (NeZero.ne _)), by simp⟩

lemma orbit_eq_of_mem (hq : IsPrimePow q) {d : ℕ} {x y : ZMod (nfree q n)} (hy : y ∈ orbit q n d x) :
    orbit q n d y = orbit q n d x := by
  obtain ⟨j, rfl⟩ := (mem_orbit_iff hq).mp hy
  set u := (qUnit (n := n) hq) ^ d
  have hu : ((u : (ZMod (nfree q n))ˣ) : ZMod (nfree q n)) = (q : ZMod (nfree q n)) ^ d := by
    simp [u]
  ext z
  rw [mem_orbit_iff hq, mem_orbit_iff hq]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i + j, by rw [pow_add, mul_assoc]⟩
  · rintro ⟨i, rfl⟩
    -- z = u^i x = u^(i + (ord - j%ord)) * (u^j x)
    have hpos : 0 < orderOf u := orderOf_pos u
    refine ⟨i + (orderOf u - j % orderOf u), ?_⟩
    rw [← mul_assoc, ← pow_add, ← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    have h1 : j % orderOf u < orderOf u := Nat.mod_lt _ hpos
    have key : (i + (orderOf u - j % orderOf u) + j) % orderOf u = i % orderOf u := by
      have e : i + (orderOf u - j % orderOf u) + j = i + orderOf u * (j / orderOf u + 1) := by
        have := Nat.div_add_mod j (orderOf u)
        rw [Nat.mul_add, mul_one]
        omega
      rw [e, Nat.add_mul_mod_self_left]
    rw [← pow_mod_orderOf u (i + (orderOf u - j % orderOf u) + j), key, pow_mod_orderOf]

lemma tcodim_qpow_mul (hq : IsPrimePow q) (k : ℕ) (x : ZMod (nfree q n)) :
    tcodim q n ((q : ZMod (nfree q n)) ^ k * x) = tcodim q n x := by
  simp only [tcodim, addOrderOf_qpow_mul hq]

lemma codim_orbit (hq : IsPrimePow q) (d : ℕ) (x : ZMod (nfree q n)) :
    codim q n (d, orbit q n d x) = tcodim q n x := by
  unfold codim
  apply le_antisymm
  · refine Finset.sup_le fun y hy => ?_
    obtain ⟨j, rfl⟩ := (mem_orbit_iff hq).mp hy
    rw [← pow_mul, tcodim_qpow_mul hq]
  · exact Finset.le_sup (f := tcodim q n) (mem_orbit_self d x)

lemma tord_orbit (hq : IsPrimePow q) (d : ℕ) (x : ZMod (nfree q n)) :
    tord q n (d, orbit q n d x) = addOrderOf x := by
  unfold tord
  apply le_antisymm
  · refine Finset.sup_le fun y hy => ?_
    obtain ⟨j, rfl⟩ := (mem_orbit_iff hq).mp hy
    rw [← pow_mul, addOrderOf_qpow_mul hq]
  · exact Finset.le_sup (f := addOrderOf) (mem_orbit_self d x)

lemma mem_conds {C : Cond q n} :
    C ∈ conds q n ↔ ∃ d ∈ n.divisors, ∃ x ∈ targets q n d, C = (d, orbit q n d x) := by
  simp only [conds, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨d, hd, x, hx, rfl⟩; exact ⟨d, hd, x, hx, rfl⟩
  · rintro ⟨d, hd, x, hx, rfl⟩; exact ⟨d, hd, x, hx, rfl⟩

lemma mem_targets {d : ℕ} {x : ZMod (nfree q n)} :
    x ∈ targets q n d ↔ ((bigN q n d : ℕ) : ZMod (nfree q n)) * x = 0 := by
  simp [targets]

lemma qpow_mul_mem_targets {d : ℕ} {x : ZMod (nfree q n)} (hx : x ∈ targets q n d) (k : ℕ) :
    (q : ZMod (nfree q n)) ^ k * x ∈ targets q n d := by
  rw [mem_targets] at hx ⊢
  rw [mul_left_comm, hx, mul_zero]

lemma orbit_subset_targets (hq : IsPrimePow q) {d : ℕ} {x : ZMod (nfree q n)}
    (hx : x ∈ targets q n d) : orbit q n d x ⊆ targets q n d := by
  intro y hy
  obtain ⟨j, rfl⟩ := (mem_orbit_iff hq).mp hy
  rw [← pow_mul]
  exact qpow_mul_mem_targets hx _

/-- Characterisation of the codimension and target order of a condition via any target. -/
lemma codim_eq_of_mem (hq : IsPrimePow q) {C : Cond q n} (hC : C ∈ conds q n) {x : ZMod (nfree q n)}
    (hx : x ∈ C.2) : codim q n C = tcodim q n x ∧ tord q n C = addOrderOf x := by
  obtain ⟨d, -, y, -, rfl⟩ := mem_conds.mp hC
  rw [← orbit_eq_of_mem hq hx]
  exact ⟨codim_orbit hq d x, tord_orbit hq d x⟩

end

end Model
end MorganMullen
