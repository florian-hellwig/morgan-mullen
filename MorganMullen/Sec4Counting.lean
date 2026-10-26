import MorganMullen.Sec3Product
import MorganMullen.Sec4Abstract

/-!
# Section 4: the counting criterion

* Lemma 4.1 and the counting criterion in abstract form: `Sec4Abstract.lean`.
* Theorem 4.2: the counting criterion for the essential conditions: `lFactor_le` (`L ≤ 2^M (1 - 1/q)^{M_1}`),
  `pcn_sub_main_abs_le` (a), `pcn_ge` and `hasMM_of_counting` (b).
-/

set_option linter.unusedSectionVars false

namespace MorganMullen

open Module Finset

section Setting

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

local notation "q" => Fintype.card F
local notation "n" => Module.finrank F E

open Classical in
/-- `PCN_q(n)`, the number of primitive completely normal elements. -/
noncomputable def pcnCount (F E : Type*) [Field F] [Field E] [Fintype E] [Algebra F E] : ℕ :=
  (univ.filter fun w : E => IsPrimitiveElem w ∧ IsCompletelyNormal F E w).card

/-- `L = ∏_C 2 (1 - q^{-o(C)})`, the product over all essential conditions. -/
noncomputable def lFactor (F E : Type*) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : ℝ :=
  ∏ C ∈ Model.essConds (Fintype.card F) (finrank F E),
    2 * (1 - ((Fintype.card F : ℝ) ^ Model.codim (Fintype.card F) (finrank F E) C)⁻¹)

open Classical in
lemma card_filter_cn_eq {ζ : AlgebraicClosure E} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) :
    (univ.filter fun w : E => ∀ C ∈ Model.essConds q n,
        w ∉ (condKer (F := F) (E := E) ζ C).toAddSubgroup).card = cnCount F E := by
  unfold cnCount
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Submodule.mem_toAddSubgroup]
  exact (isCompletelyNormal_iff_essential hζ w).symm

open Classical in
lemma card_filter_pcn_eq {ζ : AlgebraicClosure E} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) :
    (univ.filter fun w : E => IsPrimitiveElem w ∧ ∀ C ∈ Model.essConds q n,
        w ∉ (condKer (F := F) (E := E) ζ C).toAddSubgroup).card = pcnCount F E := by
  unfold pcnCount
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Submodule.mem_toAddSubgroup]
  rw [isCompletelyNormal_iff_essential hζ w]

lemma prod_eq_lFactor {ζ : AlgebraicClosure E} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) :
    ∏ C ∈ Model.essConds q n,
        2 * (1 - (Nat.card (condKer (F := F) (E := E) ζ C).toAddSubgroup : ℝ) / Fintype.card E) =
      lFactor F E := by
  unfold lFactor
  refine Finset.prod_congr rfl fun C hC => ?_
  obtain ⟨hcard, hle⟩ := card_condKer hζ hC
  have h1 : Nat.card (condKer (F := F) (E := E) ζ C).toAddSubgroup =
      Nat.card (condKer (F := F) (E := E) ζ C) := rfl
  have hE : Fintype.card E = q ^ n := Module.card_eq_pow_finrank
  rw [h1, hcard, hE]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  congr 2
  push_cast
  rw [div_eq_iff (pow_ne_zero _ hq0)]
  have e : (q : ℝ) ^ n = (q : ℝ) ^ Model.codim q n C * (q : ℝ) ^ (n - Model.codim q n C) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]


/-- **Theorem 4.2**, first claim: `L ≤ 2^M (1 - 1/q)^{M_1}`, `M_1` the number of essential conditions of
codimension `1` (every factor of `L` is at most `2`, and those with `o(C) = 1` equal `2 (1 - 1/q)`). -/
lemma lFactor_le :
    lFactor F E ≤ (2 : ℝ) ^ Model.numM q n *
      (1 - 1 / (q : ℝ)) ^ ((Model.essConds q n).filter fun C => Model.codim q n C = 1).card := by
  classical
  have hq2 : 2 ≤ q := (FiniteField.isPrimePow_card F).two_le
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hqpos : (0 : ℝ) < q := by linarith
  set ess := Model.essConds q n
  unfold lFactor
  rw [← Finset.prod_filter_mul_prod_filter_not ess (fun C => Model.codim q n C = 1)]
  have h1 : ∏ C ∈ ess.filter (fun C => Model.codim q n C = 1),
      2 * (1 - ((q : ℝ) ^ Model.codim q n C)⁻¹) =
      (2 * (1 - 1 / (q : ℝ))) ^ (ess.filter fun C => Model.codim q n C = 1).card := by
    rw [Finset.prod_congr rfl (g := fun _ => 2 * (1 - 1 / (q : ℝ))), Finset.prod_const]
    intro C hC
    rw [(Finset.mem_filter.mp hC).2, pow_one, one_div]
  have hfac : ∀ C ∈ ess.filter (fun C => ¬ Model.codim q n C = 1),
      2 * (1 - ((q : ℝ) ^ Model.codim q n C)⁻¹) ≤ 2 := by
    intro C _
    have : 0 ≤ ((q : ℝ) ^ Model.codim q n C)⁻¹ := by positivity
    linarith
  have hfac0 : ∀ C ∈ ess.filter (fun C => ¬ Model.codim q n C = 1),
      0 ≤ 2 * (1 - ((q : ℝ) ^ Model.codim q n C)⁻¹) := by
    intro C _
    have : ((q : ℝ) ^ Model.codim q n C)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    linarith
  have h2 : ∏ C ∈ ess.filter (fun C => ¬ Model.codim q n C = 1),
      2 * (1 - ((q : ℝ) ^ Model.codim q n C)⁻¹) ≤
      (2 : ℝ) ^ (ess.filter fun C => ¬ Model.codim q n C = 1).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ hfac0 hfac
  have hcard : (ess.filter fun C => Model.codim q n C = 1).card +
      (ess.filter fun C => ¬ Model.codim q n C = 1).card = Model.numM q n :=
    Finset.card_filter_add_card_filter_not _
  rw [h1]
  have hA : 0 ≤ (2 * (1 - 1 / (q : ℝ))) ^ (ess.filter fun C => Model.codim q n C = 1).card := by
    have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hqpos]; linarith
    positivity
  calc (2 * (1 - 1 / (q : ℝ))) ^ (ess.filter fun C => Model.codim q n C = 1).card *
        ∏ C ∈ ess.filter (fun C => ¬ Model.codim q n C = 1), 2 * (1 - ((q : ℝ) ^ Model.codim q n C)⁻¹)
      ≤ (2 * (1 - 1 / (q : ℝ))) ^ (ess.filter fun C => Model.codim q n C = 1).card *
        (2 : ℝ) ^ (ess.filter fun C => ¬ Model.codim q n C = 1).card :=
        mul_le_mul_of_nonneg_left h2 hA
    _ = _ := by rw [← hcard, pow_add, mul_pow]; ring

/-- **Theorem 4.2 (a)** (counting criterion): with `θ = φ(q^n - 1)/(q^n - 1)`, `ω = ω(q^n - 1)`,
`β = 1 + (2^ω - 1) q^{n/2}` and `δ_n = CN_q(n)/q^n`,
`|PCN_q(n) - θ (q^n - 1) δ_n| ≤ θ β (L - δ_n)`. -/
theorem pcn_sub_main_abs_le :
    |(pcnCount F E : ℝ) - thetaFrac (Fintype.card E - 1) *
        ((Fintype.card E - 1 : ℝ) * ((cnCount F E : ℝ) / Fintype.card E))| ≤
      thetaFrac (Fintype.card E - 1) *
        (1 + (twoPowOmega (Fintype.card E - 1) - 1) * Real.sqrt (Fintype.card E)) *
          (lFactor F E - (cnCount F E : ℝ) / Fintype.card E) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_zeta (F := F) (E := E)
  have := counting_abstract_abs (Model.essConds q n)
    (fun C => (condKer (F := F) (E := E) ζ C).toAddSubgroup)
  rwa [prod_eq_lFactor hζ, card_filter_pcn_eq hζ, card_filter_cn_eq hζ] at this

/-- **Theorem 4.2 (b)** (counting criterion): if `0 < δ_* ≤ δ_n` then
`PCN_q(n) ≥ θ [(q^n - 1) δ_* - β (L - δ_*)]`, `β = 1 + (2^ω - 1) q^{n/2}`, `ω = ω(q^n - 1)`. As in the
paper, this follows from (a), since `θ [(q^n - 1) δ - β (L - δ)]` increases with `δ`. -/
theorem pcn_ge (δs : ℝ) (h0 : 0 < δs) (hδ : δs ≤ (cnCount F E : ℝ) / Fintype.card E) :
    thetaFrac (Fintype.card E - 1) *
        ((Fintype.card E - 1 : ℝ) * δs -
          (1 + (twoPowOmega (Fintype.card E - 1) - 1) * Real.sqrt (Fintype.card E)) *
            (lFactor F E - δs)) ≤
      (pcnCount F E : ℝ) := by
  -- the positivity hypothesis `h0` is not needed: the bound is monotone in `δs`
  have _ := h0
  have key := (abs_le.mp (pcn_sub_main_abs_le (F := F) (E := E))).1
  set Q := Fintype.card E with hQ
  set θ := thetaFrac (Q - 1) with hθ
  set β := 1 + (twoPowOmega (Q - 1) - 1) * Real.sqrt Q with hβ
  set δ := (cnCount F E : ℝ) / Q with hδdef
  have hθ0 : 0 ≤ θ := by rw [hθ]; unfold thetaFrac; positivity
  have hβ1 : 1 ≤ β := by
    have h1 : 1 ≤ twoPowOmega (Q - 1) := by unfold twoPowOmega; exact one_le_pow₀ (by norm_num)
    have := Real.sqrt_nonneg (Q : ℝ)
    rw [hβ]; nlinarith
  have hQ2 : 2 ≤ Q := Fintype.one_lt_card
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
    linarith
  have hmono : 0 ≤ θ * (((Q : ℝ) - 1) + β) * (δ - δs) :=
    mul_nonneg (mul_nonneg hθ0 (by linarith)) (by linarith)
  linarith

/-- **Theorem 4.2 (b)**, the sufficient condition: if `0 < δ_* ≤ δ_n` and `(q^n - 1) δ_* ≥ 2^ω q^{n/2} L`,
then `(q, n)` has the Morgan–Mullen property. -/
theorem hasMM_of_counting (δs : ℝ) (h0 : 0 < δs) (hδ : δs ≤ (cnCount F E : ℝ) / Fintype.card E)
    (h : twoPowOmega (Fintype.card E - 1) * Real.sqrt (Fintype.card E) * lFactor F E ≤
      (Fintype.card E - 1 : ℝ) * δs) :
    HasMMProperty F E := by
  classical
  have hpcn := pcn_ge δs h0 hδ
  set Q := Fintype.card E with hQdef
  have hQ2 : 2 ≤ Q := Fintype.one_lt_card
  have hQ1 : (1 : ℝ) < Q := by exact_mod_cast hQ2
  have hθ : 0 < thetaFrac (Q - 1) := by
    unfold thetaFrac
    apply div_pos
    · exact_mod_cast Nat.totient_pos.2 (by omega)
    · exact_mod_cast (by omega : 0 < Q - 1)
  have hsq : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.2 hQ1.le
  have hW : 1 ≤ twoPowOmega (Q - 1) := by
    unfold twoPowOmega; exact one_le_pow₀ (by norm_num)
  set W := twoPowOmega (Q - 1)
  set B := 1 + (W - 1) * Real.sqrt Q with hB
  have hBpos : 0 < B := by
    have : 0 ≤ (W - 1) * Real.sqrt Q := mul_nonneg (by linarith) (by linarith)
    linarith
  have hBle : B ≤ W * Real.sqrt Q := by
    rw [hB]; nlinarith
  have hcast : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hbr : 0 < ((Q : ℝ) - 1) * δs - B * (lFactor F E - δs) := by
    have hQδ : 0 < ((Q : ℝ) - 1) * δs := mul_pos (by linarith) h0
    rcases le_or_gt (lFactor F E - δs) 0 with hL | hL
    · have : B * (lFactor F E - δs) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hBpos.le hL
      linarith
    · have h1 : B * (lFactor F E - δs) ≤ W * Real.sqrt Q * (lFactor F E - δs) :=
        mul_le_mul_of_nonneg_right hBle hL.le
      have h2 : W * Real.sqrt Q * (lFactor F E - δs) < W * Real.sqrt Q * lFactor F E := by
        have : 0 < W * Real.sqrt Q := mul_pos (by linarith) (by linarith)
        nlinarith
      linarith
  have hpos : (0 : ℝ) < pcnCount F E := lt_of_lt_of_le (mul_pos hθ hbr) hpcn
  have hpos' : 0 < pcnCount F E := by exact_mod_cast hpos
  unfold pcnCount at hpos'
  obtain ⟨w, hw⟩ := Finset.card_pos.1 hpos'
  rw [Finset.mem_filter] at hw
  exact ⟨w, hw.2.1, hw.2.2⟩


end Setting

end MorganMullen
