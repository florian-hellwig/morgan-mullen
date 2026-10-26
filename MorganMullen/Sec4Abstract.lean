import MorganMullen.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Basic

/-!
# Section 4 in abstract form: Lemma 4.1 and the counting criterion (Theorem 4.2 (a))

This file is independent of Sections 2–3. It proves

* `primitive_charSum_le` (**Lemma 4.1**): for a non-trivial additive character `ψ` of a finite field
  `E` and `b ≠ 0`, `|∑_{w ∈ P} ψ(b w)| ≤ θ (1 + (2^ω - 1) √|E|)`, where `P` is the set of primitive
  elements, `θ = φ(|E|-1)/(|E|-1)` and `ω = ω(|E|-1)` (`twoPowOmega` is `2^ω`)
  (an `ℓ¹`-bound for the expansion of the indicator of `P` in multiplicative characters, which replaces the
  explicit coefficients of Vinogradov's formula, and `|G(χ, ψ)| = √|E|` for Gauss sums);
* `counting_abstract_abs` (**Theorem 4.2 (a)**, abstract form): for any finite family `(V_i)_{i ∈ I}` of
  additive subgroups of `E`, writing `G = {w : w ∉ V_i ∀ i ∈ I}` and `δ = |G|/|E|`,
  `|#(G ∩ P) - θ (|E| - 1) δ| ≤ θ (1 + (2^ω - 1) √|E|) (L - δ)`, `L = ∏_i 2 (1 - |V_i|/|E|)`.

The proof of the counting criterion: write `1_G = ∏_i (1 - 1_{V_i}) = ∑_b c(b) ψ_b` with a primitive
additive character `ψ`; then `c(0) = δ`, `∑_b |c(b)| ≤ L` (the Fourier coefficients of `1_{V}` are
`≥ 0` with sum `1_V(0) = 1`, so `1 - 1_V` has `ℓ¹`-norm `2 (1 - |V|/|E|)`, and `ℓ¹` is
submultiplicative under multiplication of functions), and `#(G ∩ P) = ∑_b c(b) ∑_{w ∈ P} ψ(b w)`.
-/

namespace MorganMullen

open Finset

/-- `θ(N) = φ(N)/N`. -/
noncomputable def thetaFrac (N : ℕ) : ℝ := (Nat.totient N : ℝ) / N

/-- `2^{ω(N)}`. -/
noncomputable def twoPowOmega (N : ℕ) : ℝ := 2 ^ N.primeFactors.card

open Classical in
/-- The set `P ⊆ E^×` of primitive elements. -/
noncomputable def primitives (E : Type*) [Field E] [Fintype E] : Finset E :=
  univ.filter fun w : E => IsPrimitiveElem w

/-!
### Finite Fourier analysis on a finite commutative ring

For a primitive additive character `ψ` of a finite commutative ring `R`, the functions
`x ↦ ψ (c * x)` (`c ∈ R`) are orthogonal. We work with expansions `f x = ∑ c, a c * ψ (c * x)`
and bounds on the `ℓ¹`-norm `∑ c, ‖a c‖` of the coefficients. The abstract estimate
`fourier_count_bound` is used twice: for `R = E` (Theorem 4.2 (a)) and, via a discrete logarithm
`ZMod (|E| - 1) ≃ Eˣ`, for `R = ZMod (|E| - 1)` (Lemma 4.1), where the indicator of the primitive
elements becomes `∏_{p ∣ |E| - 1} (1 - 1_{p ℤ/(|E| - 1) ℤ})` and the Fourier transform on
`ZMod (|E| - 1)` is the expansion in multiplicative characters (only an `ℓ¹`-bound for its coefficients is needed,
not the explicit coefficients of Vinogradov's formula).
-/

section Fourier

variable {R : Type*} [CommRing R] [Fintype R]

/-- `f` has the (additive) Fourier expansion `f x = ∑ c, a c * ψ (c * x)`. -/
def IsFourierExp (ψ : AddChar R ℂ) (f : R → ℂ) (a : R → ℂ) : Prop :=
  ∀ x, f x = ∑ c, a c * ψ (c * x)

lemma sum_addChar_mul_left {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) [DecidableEq R] (c : R) :
    ∑ x : R, ψ (c * x) = if c = 0 then (Fintype.card R : ℂ) else 0 := by
  have h := AddChar.sum_mulShift c hψ
  simp_rw [mul_comm _ c] at h
  rw [h]
  split_ifs <;> simp

lemma sum_addChar_mul_right {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) [DecidableEq R] (y : R) :
    ∑ c : R, ψ (c * y) = if y = 0 then (Fintype.card R : ℂ) else 0 := by
  rw [AddChar.sum_mulShift y hψ]
  split_ifs <;> simp

lemma IsFourierExp.mul {ψ : AddChar R ℂ} {f g a b : R → ℂ} (hf : IsFourierExp ψ f a)
    (hg : IsFourierExp ψ g b) :
    IsFourierExp ψ (fun x => f x * g x) (fun e => ∑ c, a c * b (e - c)) := by
  intro x
  dsimp only
  rw [hf x, hg x, Finset.sum_mul_sum]
  symm
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  symm
  refine Fintype.sum_equiv (Equiv.addLeft c) _ _ fun d => ?_
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, add_mul, AddChar.map_add_eq_mul]
  ring

lemma l1_conv_le (a b : R → ℂ) :
    ∑ e, ‖∑ c, a c * b (e - c)‖ ≤ (∑ c, ‖a c‖) * ∑ d, ‖b d‖ := by
  calc ∑ e, ‖∑ c, a c * b (e - c)‖ ≤ ∑ e, ∑ c, ‖a c‖ * ‖b (e - c)‖ := by
        gcongr with e
        exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    _ = ∑ c, ‖a c‖ * ∑ e, ‖b (e - c)‖ := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ = ∑ c, ‖a c‖ * ∑ d, ‖b d‖ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 1
        exact Fintype.sum_equiv (Equiv.subRight c) _ _ (fun e => rfl)
    _ = _ := by rw [Finset.sum_mul]

lemma IsFourierExp.sum_eq {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) {f a : R → ℂ}
    (h : IsFourierExp ψ f a) : ∑ x, f x = (Fintype.card R : ℂ) * a 0 := by
  classical
  have h' : ∀ x, f x = ∑ c, a c * ψ (c * x) := h
  simp_rw [h']
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_addChar_mul_left hψ]
  simp [mul_comm]

lemma IsFourierExp.sum_mul_weight {ψ : AddChar R ℂ} {f a : R → ℂ} (h : IsFourierExp ψ f a)
    (g : R → ℂ) : ∑ x, f x * g x = ∑ c, a c * ∑ x, ψ (c * x) * g x := by
  have h' : ∀ x, f x = ∑ c, a c * ψ (c * x) := h
  simp_rw [h', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun x _ => ?_
  ring

lemma IsFourierExp.norm_sub_le {ψ : AddChar R ℂ} {f a : R → ℂ} (h : IsFourierExp ψ f a)
    {L B : ℝ} (hL : ∑ c, ‖a c‖ ≤ L) (g : R → ℂ) (hB0 : 0 ≤ B)
    (hB : ∀ c ≠ 0, ‖∑ x, ψ (c * x) * g x‖ ≤ B) :
    ‖∑ x, f x * g x - a 0 * ∑ x, g x‖ ≤ (L - ‖a 0‖) * B := by
  classical
  rw [h.sum_mul_weight g, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  simp only [zero_mul, AddChar.map_zero_eq_one, one_mul, add_sub_cancel_left]
  calc ‖∑ c ∈ univ.erase 0, a c * ∑ x, ψ (c * x) * g x‖
        ≤ ∑ c ∈ univ.erase 0, ‖a c‖ * B := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB c (Finset.ne_of_mem_erase hc)) (norm_nonneg _)
    _ = (∑ c, ‖a c‖ - ‖a 0‖) * B := by
        rw [← Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
        ring
    _ ≤ (L - ‖a 0‖) * B := by gcongr

lemma isFourierExp_one (ψ : AddChar R ℂ) [DecidableEq R] :
    IsFourierExp ψ (fun _ => 1) (fun c => if c = 0 then 1 else 0) := by
  intro x
  simp

lemma exists_isFourierExp_prod (ψ : AddChar R ℂ) {ι : Type*} (I : Finset ι)
    (f : ι → R → ℂ) (L : ι → ℝ)
    (h : ∀ i ∈ I, ∃ a, IsFourierExp ψ (f i) a ∧ ∑ c, ‖a c‖ ≤ L i) :
    ∃ a, IsFourierExp ψ (fun x => ∏ i ∈ I, f i x) a ∧ ∑ c, ‖a c‖ ≤ ∏ i ∈ I, L i := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨fun c => if c = 0 then 1 else 0, ?_, ?_⟩
    · simpa using isFourierExp_one ψ
    · simp [apply_ite (fun z : ℂ => ‖z‖)]
  | insert i s hi ih =>
    obtain ⟨b, hb, hbL⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨a, ha, haL⟩ := h i (Finset.mem_insert_self i s)
    refine ⟨fun e => ∑ c, a c * b (e - c), ?_, ?_⟩
    · have := ha.mul hb
      intro x
      show ∏ j ∈ insert i s, f j x = _
      rw [Finset.prod_insert hi]
      exact this x
    · rw [Finset.prod_insert hi]
      refine (l1_conv_le a b).trans ?_
      have h1 : 0 ≤ ∑ c, ‖a c‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have h2 : 0 ≤ ∑ c, ‖b c‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      exact mul_le_mul haL hbL h2 (h1.trans haL)

end Fourier

section SubgroupIndicator

variable {R : Type*} [CommRing R] [Fintype R]

open Classical in
/-- The (real, nonnegative) Fourier coefficients of the indicator of an additive subgroup. -/
noncomputable def subgroupCoef (ψ : AddChar R ℂ) (V : AddSubgroup R) (c : R) : ℝ :=
  if ∀ v ∈ V, ψ (c * v) = 1 then (Nat.card V : ℝ) / Fintype.card R else 0

lemma subgroupCoef_nonneg (ψ : AddChar R ℂ) (V : AddSubgroup R) (c : R) :
    0 ≤ subgroupCoef ψ V c := by
  unfold subgroupCoef
  split_ifs <;> positivity

lemma subgroupCoef_zero (ψ : AddChar R ℂ) (V : AddSubgroup R) :
    subgroupCoef ψ V 0 = (Nat.card V : ℝ) / Fintype.card R := by
  unfold subgroupCoef
  rw [ite_eq_left]
  intro v _
  simp

open Classical in
lemma sum_subgroup_addChar (ψ : AddChar R ℂ) (V : AddSubgroup R) (c : R) :
    ∑ v : V, ψ (-(c * v)) = if ∀ v ∈ V, ψ (c * v) = 1 then (Nat.card V : ℂ) else 0 := by
  split_ifs with hV
  · have : ∀ v : V, ψ (-(c * v)) = 1 := fun v => by
      rw [AddChar.map_neg_eq_inv, hV v v.2, inv_one]
    simp [this, Nat.card_eq_fintype_card]
  · push Not at hV
    obtain ⟨v0, hv0, hne⟩ := hV
    let χ : AddChar V ℂ := (ψ.mulShift (-c)).compAddMonoidHom V.subtype
    have hχ : χ ≠ 1 := by
      rw [AddChar.ne_one_iff]
      refine ⟨⟨-v0, V.neg_mem hv0⟩, ?_⟩
      simpa [χ] using hne
    have := AddChar.sum_eq_zero_of_ne_one hχ
    rw [← this]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [χ, neg_mul]

open Classical in
lemma isFourierExp_indicator {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) (V : AddSubgroup R) :
    IsFourierExp ψ (fun x => if x ∈ V then 1 else 0) (fun c => (subgroupCoef ψ V c : ℂ)) := by
  intro x
  have hR : (Fintype.card R : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcoef : ∀ c, (subgroupCoef ψ V c : ℂ) =
      (Fintype.card R : ℂ)⁻¹ * ∑ v : V, ψ (-(c * v)) := by
    intro c
    rw [sum_subgroup_addChar]
    unfold subgroupCoef
    split_ifs
    · push_cast
      field_simp
    · simp
  simp_rw [hcoef]
  have hc : ∀ c, ((Fintype.card R : ℂ)⁻¹ * ∑ v : V, ψ (-(c * v))) * ψ (c * x) =
      (Fintype.card R : ℂ)⁻¹ * ∑ v : V, ψ (c * (x - v)) := by
    intro c
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hc, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_addChar_mul_right hψ, sub_eq_zero]
  split_ifs with hx
  · rw [Finset.sum_eq_single ⟨x, hx⟩]
    · simp [hR]
    · intro b _ hb
      rw [ite_eq_right]
      intro h
      apply hb
      ext
      exact h.symm
    · simp
  · rw [Finset.sum_eq_zero]
    · simp
    intro v _
    rw [ite_eq_right]
    intro h
    exact hx (h ▸ v.2)

lemma sum_subgroupCoef {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) (V : AddSubgroup R) :
    ∑ c, subgroupCoef ψ V c = 1 := by
  classical
  have := isFourierExp_indicator hψ V 0
  simp only [V.zero_mem, ite_true, mul_zero, AddChar.map_zero_eq_one, mul_one] at this
  exact_mod_cast this.symm

open Classical in
lemma isFourierExp_one_sub_indicator {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive)
    (V : AddSubgroup R) :
    IsFourierExp ψ (fun x => 1 - if x ∈ V then 1 else 0)
      (fun c => (if c = 0 then 1 else 0) - (subgroupCoef ψ V c : ℂ)) := by
  intro x
  show (1 : ℂ) - (if x ∈ V then 1 else 0) =
    ∑ c, ((if c = 0 then 1 else 0) - (subgroupCoef ψ V c : ℂ)) * ψ (c * x)
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [← isFourierExp_one ψ x, ← isFourierExp_indicator hψ V x]

open Classical in
lemma l1_one_sub_indicator {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) (V : AddSubgroup R) :
    ∑ c, ‖(if c = 0 then (1 : ℂ) else 0) - (subgroupCoef ψ V c : ℂ)‖ =
      2 * (1 - (Nat.card V : ℝ) / Fintype.card R) := by
  have hsum := sum_subgroupCoef hψ V
  have h2 : ∑ c ∈ univ.erase 0, subgroupCoef ψ V c = 1 - subgroupCoef ψ V 0 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    ring
  have h2' : 0 ≤ ∑ c ∈ univ.erase 0, subgroupCoef ψ V c :=
    Finset.sum_nonneg fun c _ => subgroupCoef_nonneg ψ V c
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  have h0 : ‖(if (0 : R) = 0 then (1 : ℂ) else 0) - (subgroupCoef ψ V 0 : ℂ)‖ =
      1 - subgroupCoef ψ V 0 := by
    rw [ite_eq_left rfl, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h1 : ∑ c ∈ univ.erase 0, ‖(if c = 0 then (1 : ℂ) else 0) - (subgroupCoef ψ V c : ℂ)‖ =
      ∑ c ∈ univ.erase 0, subgroupCoef ψ V c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [ite_eq_right (Finset.ne_of_mem_erase hc), zero_sub, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (subgroupCoef_nonneg ψ V c)]
  rw [h0, h1, h2, subgroupCoef_zero]
  ring

open Classical in
lemma exists_isFourierExp_prod_indicator {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) {ι : Type*}
    (I : Finset ι) (V : ι → AddSubgroup R) :
    ∃ a, IsFourierExp ψ (fun x => ∏ i ∈ I, (1 - if x ∈ V i then (1 : ℂ) else 0)) a ∧
      ∑ c, ‖a c‖ ≤ ∏ i ∈ I, 2 * (1 - (Nat.card (V i) : ℝ) / Fintype.card R) :=
  exists_isFourierExp_prod ψ I _ _ fun i _ =>
    ⟨_, isFourierExp_one_sub_indicator hψ (V i), (l1_one_sub_indicator hψ (V i)).le⟩

open Classical in
omit [Fintype R] in
lemma prod_one_sub_indicator {ι : Type*} (I : Finset ι) (V : ι → AddSubgroup R) (x : R) :
    ∏ i ∈ I, (1 - if x ∈ V i then (1 : ℂ) else 0) = if ∀ i ∈ I, x ∉ V i then 1 else 0 := by
  have : ∀ i, (1 - if x ∈ V i then (1 : ℂ) else 0) = if x ∉ V i then 1 else 0 := by
    intro i
    split_ifs <;> simp_all
  simp_rw [this]
  rw [Finset.prod_ite_zero]
  simp

open Classical in
/-- **Abstract counting criterion**: Fourier-analytic estimate for sums of a weight `g` over the
complement of a union of additive subgroups. -/
theorem fourier_count_bound {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) {ι : Type*} (I : Finset ι)
    (V : ι → AddSubgroup R) (g : R → ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ c ≠ 0, ‖∑ x, ψ (c * x) * g x‖ ≤ B) :
    ‖∑ x, (if ∀ i ∈ I, x ∉ V i then g x else 0) -
        (((univ.filter fun x => ∀ i ∈ I, x ∉ V i).card : ℝ) / Fintype.card R : ℝ) *
          ∑ x, g x‖ ≤
      ((∏ i ∈ I, 2 * (1 - (Nat.card (V i) : ℝ) / Fintype.card R)) -
        ((univ.filter fun x => ∀ i ∈ I, x ∉ V i).card : ℝ) / Fintype.card R) * B := by
  obtain ⟨a, ha, haL⟩ := exists_isFourierExp_prod_indicator hψ I V
  have hR : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum := ha.sum_eq hψ
  simp_rw [prod_one_sub_indicator] at hsum
  rw [Finset.sum_boole] at hsum
  have ha0 : a 0 = (((univ.filter fun x => ∀ i ∈ I, x ∉ V i).card : ℝ) /
      Fintype.card R : ℝ) := by
    push_cast
    rw [hsum]
    field_simp
  have hna0 : ‖a 0‖ = ((univ.filter fun x => ∀ i ∈ I, x ∉ V i).card : ℝ) / Fintype.card R := by
    rw [ha0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have key := ha.norm_sub_le haL g hB0 hB
  rw [hna0, ha0] at key
  convert key using 3
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [prod_one_sub_indicator]
  split_ifs <;> simp

end SubgroupIndicator

/-!
### Lemma 4.1: transport to `ZMod (|E| - 1)` via a discrete logarithm
-/

section Lemma12

/-- A primitive additive character of `ZMod m`, `k ↦ exp(2πi k/m)`. -/
noncomputable def zmodPrimChar (m : ℕ) [NeZero m] : AddChar (ZMod m) ℂ :=
  AddChar.zmodChar m (Complex.isPrimitiveRoot_exp m (NeZero.ne m)).pow_eq_one

lemma zmodPrimChar_isPrimitive (m : ℕ) [NeZero m] : (zmodPrimChar m).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root m (Complex.isPrimitiveRoot_exp m (NeZero.ne m))

variable {E : Type*} [Field E] [Fintype E]

omit [Fintype E] in
lemma isPrimitiveElem_iff_isUnit {m : ℕ} [NeZero m] (d : Multiplicative (ZMod m) ≃* Eˣ)
    (k : ZMod m) : IsPrimitiveElem ((d (Multiplicative.ofAdd k) : Eˣ) : E) ↔ IsUnit k := by
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨n, hn⟩ := h ((d (Multiplicative.ofAdd 1) : Eˣ) : E) (Units.ne_zero _)
    rw [← Units.val_pow_eq_pow_val, Units.val_inj, ← map_pow, d.apply_eq_iff_eq,
      ← ofAdd_nsmul] at hn
    have hn' : k * (n : ZMod m) = 1 := by
      rw [mul_comm, ← nsmul_eq_mul]
      exact Multiplicative.ofAdd.injective hn
    exact IsUnit.of_mul_eq_one _ hn'
  · intro hk
    refine ⟨Units.ne_zero _, fun x hx => ?_⟩
    obtain ⟨k0, hk0⟩ := hk.exists_left_inv
    refine ⟨(Multiplicative.toAdd (d.symm (Units.mk0 x hx)) * k0).val, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val,
      mul_assoc, hk0, mul_one]
    simp

open Classical in
lemma sum_eq_add_sum_units (F : E → ℂ) : ∑ x, F x = F 0 + ∑ u : Eˣ, F u := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  congr 1
  rw [Fintype.sum_equiv unitsEquivNeZero (fun u : Eˣ => F u) (fun x => F x.1) (fun u => rfl)]
  exact Finset.sum_subtype (univ.erase 0) (by simp) F

open Classical in
lemma sum_primitives_eq {m : ℕ} [NeZero m] (d : Multiplicative (ZMod m) ≃* Eˣ) (F : E → ℂ) :
    ∑ w ∈ primitives E, F w =
      ∑ k : ZMod m, (if IsUnit k then F (d (Multiplicative.ofAdd k)) else 0) := by
  unfold primitives
  rw [Finset.sum_filter, sum_eq_add_sum_units]
  have h0 : ¬ IsPrimitiveElem (0 : E) := fun h => h.1 rfl
  rw [ite_eq_right h0, zero_add, ← (Multiplicative.ofAdd.trans d.toEquiv).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hiff : IsPrimitiveElem (((Multiplicative.ofAdd.trans d.toEquiv) k : Eˣ) : E) ↔ IsUnit k :=
    isPrimitiveElem_iff_isUnit d k
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl

lemma isUnit_iff_forall_not_mem_zmultiples {m : ℕ} [NeZero m] (k : ZMod m) :
    IsUnit k ↔ ∀ p ∈ m.primeFactors, k ∉ AddSubgroup.zmultiples (p : ZMod m) := by
  constructor
  · intro hk p hp hmem
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    rw [zsmul_eq_mul] at hz
    rw [← hz] at hk
    have hpu : IsUnit (p : ZMod m) := isUnit_of_mul_isUnit_right hk
    exact (ZMod.isUnit_prime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp)).mp hpu
      (Nat.dvd_of_mem_primeFactors hp)
  · intro h
    by_contra hk
    have hk' : ¬ Nat.Coprime k.val m := by
      rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      exact hk
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hk'
    have hpk : p ∣ k.val := hpd.trans (Nat.gcd_dvd_left _ _)
    have hpm : p ∣ m := hpd.trans (Nat.gcd_dvd_right _ _)
    apply h p (Nat.mem_primeFactors.mpr ⟨hp, hpm, NeZero.ne m⟩)
    obtain ⟨t, ht⟩ := hpk
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨(t : ℤ), ?_⟩
    rw [← ZMod.natCast_zmod_val k, ht, zsmul_eq_mul]
    push_cast
    ring

lemma card_zmultiples_div {m : ℕ} [NeZero m] {p : ℕ} (hp : p ∈ m.primeFactors) :
    (Nat.card (AddSubgroup.zmultiples (p : ZMod m)) : ℝ) / Fintype.card (ZMod m) = 1 / p := by
  have hpm := Nat.dvd_of_mem_primeFactors hp
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe p (NeZero.ne m), Nat.gcd_eq_right hpm, ZMod.card]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  rw [Nat.cast_div hpm hp0]
  field_simp

lemma card_filter_isUnit (m : ℕ) [NeZero m] :
    (univ.filter fun k : ZMod m => IsUnit k).card = Nat.totient m := by
  rw [← ZMod.card_units_eq_totient, ← Finset.card_univ,
    ← Finset.card_map ⟨Units.val, Units.val_injective⟩]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  exact Iff.rfl

open Classical in
lemma card_filter_not_mem_zmultiples (m : ℕ) [NeZero m] :
    ((univ.filter fun k : ZMod m =>
      ∀ p ∈ m.primeFactors, k ∉ AddSubgroup.zmultiples (p : ZMod m)).card) = Nat.totient m := by
  rw [← card_filter_isUnit m]
  congr 1
  ext k
  rw [Finset.mem_filter, Finset.mem_filter, isUnit_iff_forall_not_mem_zmultiples]

lemma prod_one_sub_inv_eq (m : ℕ) (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)) = (Nat.totient m : ℝ) / m := by
  have h := Nat.totient_eq_mul_prod_factors m
  have h' : (Nat.totient m : ℝ) = m * ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at this
    simpa [one_div] using this
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [h']
  field_simp

lemma norm_gaussSum_eq {χ : MulChar E ℂ} (hχ : χ ≠ 1) {ψ : AddChar E ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card E) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have h2 := Complex.mul_conj (gaussSum χ ψ)
  rw [starRingEnd_apply, h, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖gaussSum χ ψ‖ ^ 2 = Fintype.card E := by exact_mod_cast h2.symm
  rw [← h3, Real.sqrt_sq (norm_nonneg _)]

/-- The multiplicative character `d (ofAdd k) ↦ e(j k / m)` of `E`. -/
noncomputable def charOfZMod {m : ℕ} [NeZero m] (d : Multiplicative (ZMod m) ≃* Eˣ)
    (j : ZMod m) : MulChar E ℂ :=
  MulChar.ofUnitHom
    (((zmodPrimChar m).mulShift j).toMonoidHom.comp d.symm.toMonoidHom).toHomUnits

omit [Fintype E] in
lemma charOfZMod_apply {m : ℕ} [NeZero m] (d : Multiplicative (ZMod m) ≃* Eˣ) (j k : ZMod m) :
    charOfZMod d j ((d (Multiplicative.ofAdd k) : Eˣ) : E) = zmodPrimChar m (j * k) := by
  rw [charOfZMod, MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
  simp

omit [Fintype E] in
lemma charOfZMod_ne_one {m : ℕ} [NeZero m] (d : Multiplicative (ZMod m) ≃* Eˣ) {j : ZMod m}
    (hj : j ≠ 0) : charOfZMod d j ≠ 1 := by
  intro h
  apply zmodPrimChar_isPrimitive m hj
  ext k
  have := charOfZMod_apply d j k
  rw [h, MulChar.one_apply_coe] at this
  simp [← this]

lemma sum_eq_gaussSum {m : ℕ} [NeZero m] (d : Multiplicative (ZMod m) ≃* Eˣ) (j : ZMod m)
    (ψ : AddChar E ℂ) (b : E) :
    ∑ k : ZMod m, zmodPrimChar m (j * k) * ψ (b * (d (Multiplicative.ofAdd k) : E)) =
      gaussSum (charOfZMod d j) (ψ.mulShift b) := by
  classical
  unfold gaussSum
  rw [sum_eq_add_sum_units (fun x => charOfZMod d j x * ψ.mulShift b x), MulChar.map_zero,
    zero_mul, zero_add,
    ← (Multiplicative.ofAdd.trans d.toEquiv).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  show _ = charOfZMod d j ((d (Multiplicative.ofAdd k) : Eˣ) : E) *
    ψ.mulShift b ((d (Multiplicative.ofAdd k) : Eˣ) : E)
  rw [charOfZMod_apply, AddChar.mulShift_apply]

lemma sum_addChar_units {m : ℕ} [NeZero m] (d : Multiplicative (ZMod m) ≃* Eˣ)
    {ψ : AddChar E ℂ} (hψ : ψ ≠ 1) {b : E} (hb : b ≠ 0) :
    ∑ k : ZMod m, ψ (b * (d (Multiplicative.ofAdd k) : E)) = -1 := by
  classical
  have hψp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have h1 : ∑ x : E, ψ (b * x) = 0 := by
    have := AddChar.sum_eq_zero_of_ne_one (hψp hb)
    simpa using this
  rw [sum_eq_add_sum_units, mul_zero, AddChar.map_zero_eq_one] at h1
  have h2 : ∑ k : ZMod m, ψ (b * (d (Multiplicative.ofAdd k) : E)) = ∑ u : Eˣ, ψ (b * (u : E)) :=
    (Multiplicative.ofAdd.trans d.toEquiv).sum_comp (fun u : Eˣ => ψ (b * (u : E)))
  rw [h2]
  linear_combination h1

end Lemma12

/-- **Lemma 4.1** (from the evaluation of Gauss sums in Mathlib). The paper uses Vinogradov's formula
for the indicator of the primitive elements; here only an `ℓ¹`-bound for the coefficients of that expansion is
proved, by Fourier analysis on `ZMod (|E| - 1)` (see the section header). -/
theorem primitive_charSum_le {E : Type*} [Field E] [Fintype E] (ψ : AddChar E ℂ) (hψ : ψ ≠ 1)
    {b : E} (hb : b ≠ 0) :
    ‖∑ w ∈ primitives E, ψ (b * w)‖ ≤
      thetaFrac (Fintype.card E - 1) *
        (1 + (twoPowOmega (Fintype.card E - 1) - 1) * Real.sqrt (Fintype.card E)) := by
  classical
  have hm : Fintype.card E - 1 = Nat.card Eˣ := by rw [Nat.card_units, Nat.card_eq_fintype_card]
  rw [hm]
  set m := Nat.card Eˣ with hm_def
  have : NeZero m := ⟨Nat.card_pos.ne'⟩
  let d : Multiplicative (ZMod m) ≃* Eˣ := zmodCyclicMulEquiv inferInstance
  have hψp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  rw [sum_primitives_eq d (fun w => ψ (b * w))]
  set g : ZMod m → ℂ := fun k => ψ (b * (d (Multiplicative.ofAdd k) : E)) with hg
  have hB : ∀ j ≠ 0, ‖∑ k, zmodPrimChar m (j * k) * g k‖ ≤ Real.sqrt (Fintype.card E) := by
    intro j hj
    rw [hg, sum_eq_gaussSum d j ψ b,
      norm_gaussSum_eq (charOfZMod_ne_one d hj) (AddChar.IsPrimitive.of_ne_one (hψp hb))]
  have key := fourier_count_bound (zmodPrimChar_isPrimitive m) m.primeFactors
    (fun p => AddSubgroup.zmultiples (p : ZMod m)) g (Real.sqrt_nonneg _) hB
  beta_reduce at key
  have hS : ∑ k : ZMod m, (if ∀ p ∈ m.primeFactors, k ∉ AddSubgroup.zmultiples (p : ZMod m)
      then g k else 0) = ∑ k : ZMod m, (if IsUnit k then ψ (b * (d (Multiplicative.ofAdd k) : E))
      else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hiff := isUnit_iff_forall_not_mem_zmultiples k
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.mpr h1) h2
    · exact absurd (hiff.mp h2) h1
    · rfl
  have hL : ∏ p ∈ m.primeFactors, 2 * (1 - (Nat.card (AddSubgroup.zmultiples (p : ZMod m)) : ℝ) /
      Fintype.card (ZMod m)) = twoPowOmega m * thetaFrac m := by
    rw [Finset.prod_congr rfl fun p hp => by rw [card_zmultiples_div hp]]
    rw [Finset.prod_mul_distrib, Finset.prod_const, prod_one_sub_inv_eq m (NeZero.ne m)]
    simp [twoPowOmega, thetaFrac]
  rw [hS, hL, card_filter_not_mem_zmultiples, sum_addChar_units d hψ hb, ZMod.card] at key
  have hθ : (Nat.totient m : ℝ) / m = thetaFrac m := rfl
  rw [hθ] at key
  have hθ0 : 0 ≤ thetaFrac m := by unfold thetaFrac; positivity
  set S := ∑ k : ZMod m, (if IsUnit k then ψ (b * (d (Multiplicative.ofAdd k) : E)) else 0)
  calc ‖S‖ = ‖(S - ((thetaFrac m : ℝ) : ℂ) * (-1)) + (-((thetaFrac m : ℝ) : ℂ))‖ := by
        congr 1; ring
    _ ≤ ‖S - ((thetaFrac m : ℝ) : ℂ) * (-1)‖ + ‖-((thetaFrac m : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ (twoPowOmega m * thetaFrac m - thetaFrac m) * Real.sqrt (Fintype.card E) +
          thetaFrac m := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0]
        linarith
    _ = thetaFrac m * (1 + (twoPowOmega m - 1) * Real.sqrt (Fintype.card E)) := by ring

lemma exists_addChar_ne_one (E : Type*) [Field E] [Fintype E] : ∃ ψ : AddChar E ℂ, ψ ≠ 1 := by
  have hp : Fact (ringChar E).Prime := ⟨CharP.char_is_prime E (ringChar E)⟩
  have : NeZero (ringChar E) := ⟨hp.out.ne_zero⟩
  let : Algebra (ZMod (ringChar E)) E := ZMod.algebra E (ringChar E)
  refine ⟨(zmodPrimChar (ringChar E)).compAddMonoidHom
    (Algebra.trace (ZMod (ringChar E)) E).toAddMonoidHom, ?_⟩
  obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate E (one_ne_zero (α := E))
  rw [one_mul] at ha
  rw [AddChar.ne_one_iff]
  refine ⟨a, ?_⟩
  rw [AddChar.compAddMonoidHom_apply, Ne,
    AddChar.IsPrimitive.zmod_char_eq_one_iff _ (zmodPrimChar_isPrimitive (ringChar E))]
  exact ha

lemma card_primitives (E : Type*) [Field E] [Fintype E] :
    ((primitives E).card : ℂ) = Nat.totient (Fintype.card E - 1) := by
  classical
  have hm : Fintype.card E - 1 = Nat.card Eˣ := by rw [Nat.card_units, Nat.card_eq_fintype_card]
  rw [hm]
  have : NeZero (Nat.card Eˣ) := ⟨Nat.card_pos.ne'⟩
  let d : Multiplicative (ZMod (Nat.card Eˣ)) ≃* Eˣ := zmodCyclicMulEquiv inferInstance
  have h := sum_primitives_eq d (fun _ => (1 : ℂ))
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h, Finset.sum_boole, card_filter_isUnit]

open Classical in
/-- **Theorem 4.2 (a)**, abstract form: for a finite family `(V_i)_{i ∈ I}` of additive subgroups of `E`,
with `G = {w : w ∉ V_i ∀ i ∈ I}`, `δ = |G|/|E|`, `L = ∏_i 2 (1 - |V_i|/|E|)`, `θ = φ(|E|-1)/(|E|-1)` and
`β = 1 + (2^ω - 1) √|E|`, `ω = ω(|E| - 1)`:
`|#(G ∩ P) - θ (|E| - 1) δ| ≤ θ β (L - δ)`. -/
theorem counting_abstract_abs {E : Type*} [Field E] [Fintype E] {ι : Type*} (I : Finset ι)
    (V : ι → AddSubgroup E) :
    |((univ.filter fun w : E => IsPrimitiveElem w ∧ ∀ i ∈ I, w ∉ V i).card : ℝ) -
        thetaFrac (Fintype.card E - 1) * ((Fintype.card E - 1 : ℝ) *
          (((univ.filter fun w : E => ∀ i ∈ I, w ∉ V i).card : ℝ) / Fintype.card E))| ≤
      thetaFrac (Fintype.card E - 1) *
        (1 + (twoPowOmega (Fintype.card E - 1) - 1) * Real.sqrt (Fintype.card E)) *
          ((∏ i ∈ I, 2 * (1 - (Nat.card (V i) : ℝ) / Fintype.card E)) -
            ((univ.filter fun w : E => ∀ i ∈ I, w ∉ V i).card : ℝ) / Fintype.card E) := by
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one E
  have hψp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  set Q := Fintype.card E with hQ
  set θ := thetaFrac (Q - 1) with hθ
  set W := twoPowOmega (Q - 1) with hW
  set K := 1 + (W - 1) * Real.sqrt Q with hK
  set L := ∏ i ∈ I, 2 * (1 - (Nat.card (V i) : ℝ) / Q) with hL
  set δ := ((univ.filter fun w : E => ∀ i ∈ I, w ∉ V i).card : ℝ) / Q with hδdef
  set N := (univ.filter fun w : E => IsPrimitiveElem w ∧ ∀ i ∈ I, w ∉ V i).card with hN
  let g : E → ℂ := fun x => if IsPrimitiveElem x then 1 else 0
  have hg : ∀ c : E, ∑ x, ψ (c * x) * g x = ∑ w ∈ primitives E, ψ (c * w) := by
    intro c
    unfold primitives
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [g]
    split_ifs <;> simp
  have hθ0 : 0 ≤ θ := by rw [hθ]; unfold thetaFrac; positivity
  have hW1 : 1 ≤ W := by rw [hW]; unfold twoPowOmega; exact one_le_pow₀ (by norm_num)
  have hK1 : 1 ≤ K := by
    have := Real.sqrt_nonneg (Q : ℝ)
    rw [hK]; nlinarith
  have hB : ∀ c ≠ 0, ‖∑ x, ψ (c * x) * g x‖ ≤ θ * K := by
    intro c hc
    rw [hg]
    exact primitive_charSum_le ψ hψ hc
  -- the `ℓ¹`-argument (`fourier_count_bound`) with the bound of Lemma 4.1
  have key := fourier_count_bound hψp I V g (mul_nonneg hθ0 (by linarith)) hB
  have hsum1 : ∑ x, (if ∀ i ∈ I, x ∉ V i then g x else 0) = (N : ℂ) := by
    rw [hN, Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [g]
    split_ifs <;> simp_all
  have hsum2 : ∑ x, g x = (Nat.totient (Q - 1) : ℂ) := by
    rw [← card_primitives E]
    have := hg 0
    simp only [zero_mul, AddChar.map_zero_eq_one, one_mul] at this
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum1, hsum2] at key
  have hreal : (N : ℂ) - ((δ : ℝ) : ℂ) * (Nat.totient (Q - 1) : ℂ) =
      (((N : ℝ) - δ * Nat.totient (Q - 1) : ℝ) : ℂ) := by push_cast; ring
  rw [hreal, Complex.norm_real, Real.norm_eq_abs] at key
  -- `φ(|E| - 1) = θ (|E| - 1)`
  have hQ2 : 2 ≤ Q := Fintype.one_lt_card
  have hQ1 : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hQ1' : ((Q - 1 : ℕ) : ℝ) ≠ 0 := by
    rw [hQ1]
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
    linarith
  have hφ : (Nat.totient (Q - 1) : ℝ) = θ * ((Q : ℝ) - 1) := by
    rw [hθ, thetaFrac, ← hQ1, div_mul_cancel₀ _ hQ1']
  rw [hφ] at key
  calc |(N : ℝ) - θ * (((Q : ℝ) - 1) * δ)| = |(N : ℝ) - δ * (θ * ((Q : ℝ) - 1))| := by
        congr 1; ring
    _ ≤ (L - δ) * (θ * K) := key
    _ = θ * K * (L - δ) := by ring

end MorganMullen
