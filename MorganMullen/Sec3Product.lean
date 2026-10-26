import MorganMullen.Sec2Lemma5
import MorganMullen.Sec3Components

/-!
# Section 3: components and the product formula

* Theorem 3.2 (product formula): the events `G_i = {C(w) ≠ 0 for all C ∈ 𝒞_i}` attached to the
  components `𝒞_i` are independent (stated in counting form), hence
  `δ_n = ∏ Pr[G_i] ≥ ∏ (1 - w_{𝒞_i})`, `w_𝒞 = ∑_{C ∈ 𝒞} q^{-o(C)}`. In the code a component is a
  `Finset` of conditions, usually called `K`.
* Lemma 3.3 (a), (b), (c) on the structure of components: see `Sec3Components.lean`.
-/

set_option linter.unusedSectionVars false

namespace MorganMullen

open Module Finset

section Indep

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

/-- Mixing two functions along a predicate. -/
def mixP (A : ι → Prop) [DecidablePred A] (t t' : ∀ i, X i) : ∀ i, X i :=
  fun i => if A i then t i else t' i

lemma mixP_mixP (A : ι → Prop) [DecidablePred A] (t t' : ∀ i, X i) :
    mixP A (mixP A t t') (mixP A t' t) = t := by
  funext i; unfold mixP; split_ifs <;> rfl

variable [Fintype ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- Two events depending on complementary sets of coordinates are independent (counting form). -/
lemma card_filter_and_mul_card (A : ι → Prop) [DecidablePred A] (f g : (∀ i, X i) → Prop)
    [DecidablePred f] [DecidablePred g]
    (hf : ∀ t t', (∀ i, A i → t i = t' i) → (f t ↔ f t'))
    (hg : ∀ t t', (∀ i, ¬ A i → t i = t' i) → (g t ↔ g t')) :
    (univ.filter fun t => f t ∧ g t).card * Fintype.card (∀ i, X i) =
      (univ.filter f).card * (univ.filter g).card := by
  rw [← Finset.card_univ, ← Finset.card_product, ← Finset.card_product]
  refine Finset.card_nbij' (fun p => (mixP A p.1 p.2, mixP A p.2 p.1))
    (fun p => (mixP A p.1 p.2, mixP A p.2 p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨t, t'⟩ h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true] at h ⊢
    refine ⟨(hf t _ fun i hi => ?_).1 h.1, (hg t _ fun i hi => ?_).1 h.2⟩
    · simp [mixP, hi]
    · simp [mixP, hi]
  · rintro ⟨t, t'⟩ h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true] at h ⊢
    refine ⟨(hf t _ fun i hi => ?_).1 h.1, (hg t' _ fun i hi => ?_).1 h.2⟩
    · simp [mixP, hi]
    · simp [mixP, hi]
  · rintro ⟨t, t'⟩ _
    simp only [mixP_mixP]
  · rintro ⟨t, t'⟩ _
    simp only [mixP_mixP]

/-- Events depending on pairwise disjoint sets of coordinates are independent (counting form). -/
lemma card_filter_forall_indep {κ : Type*} [DecidableEq κ] (J : Finset κ) (S : κ → Finset ι)
    (hS : ∀ k ∈ J, ∀ k' ∈ J, k ≠ k' → Disjoint (S k) (S k'))
    (g : κ → (∀ i, X i) → Prop) [∀ k, DecidablePred (g k)]
    (hg : ∀ k ∈ J, ∀ t t', (∀ i ∈ S k, t i = t' i) → (g k t ↔ g k t')) :
    (univ.filter fun t => ∀ k ∈ J, g k t).card * Fintype.card (∀ i, X i) ^ J.card =
      (∏ k ∈ J, (univ.filter (g k)).card) * Fintype.card (∀ i, X i) := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert k J hk ih =>
    have hS' : ∀ k ∈ J, ∀ k' ∈ J, k ≠ k' → Disjoint (S k) (S k') :=
      fun a ha b hb hab => hS a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
    have hg' : ∀ k ∈ J, ∀ t t', (∀ i ∈ S k, t i = t' i) → (g k t ↔ g k t') :=
      fun a ha => hg a (mem_insert_of_mem ha)
    have key := card_filter_and_mul_card (X := X) (fun i => i ∈ S k) (g k)
      (fun t => ∀ k' ∈ J, g k' t) (hg k (mem_insert_self k J)) (by
        intro t t' h
        refine forall₂_congr fun k' hk' => hg' k' hk' t t' fun i hi => h i ?_
        intro hik
        have hne : k ≠ k' := fun h => hk (h ▸ hk')
        exact Finset.disjoint_left.1 (hS k (mem_insert_self k J) k' (mem_insert_of_mem hk') hne)
          hik hi)
    have e : (univ.filter fun t => ∀ k' ∈ insert k J, g k' t) =
        univ.filter fun t => g k t ∧ ∀ k' ∈ J, g k' t := by
      ext t; simp
    rw [e, card_insert_of_notMem hk, prod_insert hk, pow_succ]
    have ih' := ih hS' hg'
    set T := Fintype.card (∀ i, X i)
    set A := (univ.filter fun t => g k t ∧ ∀ k' ∈ J, g k' t).card
    set B := (univ.filter fun t => ∀ k' ∈ J, g k' t).card
    calc A * (T ^ J.card * T) = (A * T) * T ^ J.card := by ring
      _ = (univ.filter (g k)).card * B * T ^ J.card := by rw [key]
      _ = (univ.filter (g k)).card * (B * T ^ J.card) := by ring
      _ = _ := by rw [ih']; ring

end Indep

section Components

variable {q n : ℕ} [NeZero n]

lemma mem_component_self {ℰ : Finset (Model.Cond q n)} {C : Model.Cond q n} (hC : C ∈ ℰ) :
    C ∈ Model.component q n ℰ C := by
  classical
  unfold Model.component
  exact Finset.mem_filter.mpr ⟨hC, Relation.EqvGen.refl _⟩

lemma component_mem_components {ℰ : Finset (Model.Cond q n)} {C : Model.Cond q n} (hC : C ∈ ℰ) :
    Model.component q n ℰ C ∈ Model.components q n ℰ :=
  Finset.mem_image_of_mem _ hC

lemma eq_of_mem_components {ℰ : Finset (Model.Cond q n)} {K K' : Finset (Model.Cond q n)}
    (hK : K ∈ Model.components q n ℰ) (hK' : K' ∈ Model.components q n ℰ) {C : Model.Cond q n}
    (hCK : C ∈ K) (hCK' : C ∈ K') : K = K' := by
  have hC : C ∈ ℰ := (Model.components_partition ℰ).1 K hK hCK
  obtain ⟨K0, -, huniq⟩ := (Model.components_partition ℰ).2 C hC
  exact (huniq K ⟨hK, hCK⟩).trans (huniq K' ⟨hK', hCK'⟩).symm

lemma eq_of_sameComp_components {ℰ : Finset (Model.Cond q n)} {K K' : Finset (Model.Cond q n)}
    (hK : K ∈ Model.components q n ℰ) (hK' : K' ∈ Model.components q n ℰ) {C C' : Model.Cond q n}
    (hCK : C ∈ K) (hCK' : C' ∈ K') (h : Model.SameComp q n ℰ C C') : K = K' := by
  classical
  have hC : C ∈ ℰ := (Model.components_partition ℰ).1 K hK hCK
  have hC' : C' ∈ ℰ := (Model.components_partition ℰ).1 K' hK' hCK'
  have h1 : C' ∈ Model.component q n ℰ C := Finset.mem_filter.mpr ⟨hC', h⟩
  rw [eq_of_mem_components hK (component_mem_components hC) hCK (mem_component_self hC),
    eq_of_mem_components hK' (component_mem_components hC) hCK' h1]

end Components

section Setting

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
variable {Ω : Type*} [Field Ω] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]

local notation "q" => Fintype.card F
local notation "n" => Module.finrank F E

open Classical

/-- The event `G_K = {w : C(w) ≠ 0 for all C ∈ K}` (as a finite set of `w ∈ E`). -/
noncomputable def goodSet (ζ : Ω) (K : Finset (Model.Cond q n)) : Finset E :=
  univ.filter fun w => ∀ C ∈ K, w ∉ condKer (F := F) ζ C

open Classical in
/-- The number `CN_q(n)` of completely normal elements. -/
noncomputable def cnCount (F E : Type*) [Field F] [Field E] [Fintype E] [Algebra F E] : ℕ :=
  (univ.filter fun w : E => IsCompletelyNormal F E w).card

/-- A primitive `n'`-th root of unity in `AlgebraicClosure E`. -/
lemma exists_zeta : ∃ ζ : AlgebraicClosure E, IsPrimitiveRoot ζ (Model.nfree q n) := by
  apply exists_primitiveRoot_algebraicClosure
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  have : CharP E (ringChar F) := by
    have : CharP F (ringChar F) := ringChar.charP F
    exact charP_of_injective_algebraMap (algebraMap F E).injective _
  rw [Ne, CharP.cast_eq_zero_iff E (ringChar F), ← chr_eq_ringChar]
  exact (Nat.Prime.coprime_iff_not_dvd (Model.chr_prime hq)).1
    (Model.coprime_chr_nfree hq Module.finrank_pos.ne')

/-- The set of pair orbits met by the pairs of a condition (its *support*). -/
noncomputable def suppOrb (C : Model.Cond q n) : Finset (PairOrb q n) :=
  (Model.pairs q n C).image (Quotient.mk (pairSetoid q n))

/-- Membership in `V_C` only depends on the coordinates on the support of `C`. -/
lemma mem_condKer_iff_of_coord {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n))
    {C : Model.Cond q n} (hC : C ∈ Model.conds q n) {w w' : E}
    (h : ∀ ω ∈ suppOrb C, coordOrb (F := F) ζ w ω = coordOrb (F := F) ζ w' ω) :
    w ∈ condKer (F := F) ζ C ↔ w' ∈ condKer (F := F) ζ C := by
  obtain ⟨d, hdn, x0, hx0, rfl⟩ := Model.mem_conds.1 hC
  have hx0C : x0 ∈ (d, Model.orbit q n d x0).2 := Model.mem_orbit_self d x0
  rw [condKer_eq hζ hC hx0C, LinearMap.mem_ker, LinearMap.mem_ker]
  have heq : fibreSum ζ d x0 w = fibreSum ζ d x0 w' := by
    simp only [fibreSum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun u hu => ?_
    have hπ : (i, u) ∈ Model.pairs q n (d, Model.orbit q n d x0) := by
      simp only [Model.pairs, Finset.mem_product, Model.fibre, Finset.mem_filter, Finset.mem_univ,
        true_and]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨by rw [hi]; exact hx0C, hu⟩
    have := congrFun (h _ (Finset.mem_image_of_mem (Quotient.mk (pairSetoid q n)) hπ)) ⟨(i, u), rfl⟩
    simpa [coordOrb] using this
  rw [heq]

/-- The supports of distinct components are disjoint. -/
lemma disjoint_supp_components {ℰ : Finset (Model.Cond q n)} {K K' : Finset (Model.Cond q n)}
    (hK : K ∈ Model.components q n ℰ) (hK' : K' ∈ Model.components q n ℰ) (hne : K ≠ K') :
    Disjoint (K.biUnion suppOrb) (K'.biUnion suppOrb) := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  rw [Finset.disjoint_left]
  intro ω h1 h2
  simp only [Finset.mem_biUnion, suppOrb, Finset.mem_image] at h1 h2
  obtain ⟨C, hCK, π, hπ, rfl⟩ := h1
  obtain ⟨C', hCK', π', hπ', heq⟩ := h2
  have hrel : Model.PairRel q n π π' := (mk_eq_mk_iff hq).1 heq.symm
  have hC : C ∈ ℰ := (Model.components_partition ℰ).1 K hK hCK
  have hC' : C' ∈ ℰ := (Model.components_partition ℰ).1 K' hK' hCK'
  exact hne (eq_of_sameComp_components hK hK' hCK hCK'
    (Relation.EqvGen.rel _ _ ⟨hC, hC', π, hπ, π', hπ', hrel⟩))

lemma card_filter_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (P : α → Prop)
    [DecidablePred P] [DecidablePred fun b => P (e.symm b)] :
    (univ.filter P).card = (univ.filter fun b => P (e.symm b)).card := by
  refine Finset.card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> intro a ha <;> simp_all


open Classical in
/-- **Theorem 3.2** (product formula), independence in counting form: for a set `ℰ` of
essential conditions (the paper: all of them) and any set `J` of its components,
`#(⋂_{𝒞 ∈ J} G_𝒞) · |E|^{|J|} = (∏_{𝒞 ∈ J} #G_𝒞) · |E|`. -/
theorem goodSet_indep {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n))
    {ℰ : Finset (Model.Cond q n)} (hℰ : ℰ ⊆ Model.essConds q n)
    {J : Finset (Finset (Model.Cond q n))} (hJ : J ⊆ Model.components q n ℰ) :
    (univ.filter fun w : E => ∀ K ∈ J, w ∈ goodSet (F := F) ζ K).card * Fintype.card E ^ J.card =
      (∏ K ∈ J, (goodSet (F := F) (E := E) ζ K).card) * Fintype.card E := by
  have hq : IsPrimePow q := FiniteField.isPrimePow_card F
  set e : E ≃ (∀ ω : PairOrb q n, Set.range fun w : E => coordOrb (F := F) ζ w ω) :=
    Equiv.ofBijective _ (coord_product hζ) with he
  have hcoord : ∀ t ω, coordOrb (F := F) ζ (e.symm t) ω = (t ω).1 := by
    intro t ω
    have := congrFun (e.apply_symm_apply t) ω
    rw [← this]
    rfl
  have hEcard : Fintype.card E = Fintype.card (∀ ω : PairOrb q n,
      Set.range fun w : E => coordOrb (F := F) ζ w ω) := Fintype.card_congr e
  have h1 := card_filter_forall_indep J (fun K => K.biUnion suppOrb)
    (fun K hK K' hK' hne => disjoint_supp_components (hJ hK) (hJ hK') hne)
    (fun K t => e.symm t ∈ goodSet (F := F) (E := E) ζ K) (by
      intro K hK t t' htt'
      simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine forall₂_congr fun C hC => not_congr ?_
      have hCe : C ∈ Model.essConds q n :=
        hℰ ((Model.components_partition ℰ).1 K (hJ hK) hC)
      apply mem_condKer_iff_of_coord hζ (Model.essConds_subset hCe)
      intro ω hω
      rw [hcoord, hcoord, htt' ω (Finset.mem_biUnion.2 ⟨C, hC, hω⟩)])
  rw [← hEcard] at h1
  have h2 : (univ.filter fun w : E => ∀ K ∈ J, w ∈ goodSet (F := F) ζ K).card =
      (univ.filter fun t => ∀ K ∈ J, e.symm t ∈ goodSet (F := F) (E := E) ζ K).card :=
    card_filter_equiv e _
  have h3 : ∀ K, (goodSet (F := F) (E := E) ζ K).card =
      (univ.filter fun t => e.symm t ∈ goodSet (F := F) (E := E) ζ K).card := by
    intro K
    rw [← card_filter_equiv e (· ∈ goodSet (F := F) (E := E) ζ K)]
    congr 1
    ext w; simp
  rw [h2, h1]
  congr 1
  exact Finset.prod_congr rfl fun K _ => (h3 K).symm

/-- **Theorem 3.2**, the product formula `δ_n = CN_q(n)/q^n = ∏_i Pr[G_i]` over the components of
the set of all essential conditions. -/
theorem delta_eq_prod {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n)) :
    (cnCount F E : ℚ) / Fintype.card E =
      ∏ K ∈ Model.components q n (Model.essConds q n),
        ((goodSet (F := F) (E := E) ζ K).card : ℚ) / Fintype.card E := by
  set J := Model.components q n (Model.essConds q n)
  have h := goodSet_indep hζ (subset_refl _) (subset_refl J)
  have hcn : (univ.filter fun w : E => ∀ K ∈ J, w ∈ goodSet (F := F) ζ K).card = cnCount F E := by
    unfold cnCount
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, goodSet]
    rw [isCompletelyNormal_iff_essential hζ w]
    constructor
    · intro h C hC
      obtain ⟨K, ⟨hK, hCK⟩, -⟩ := (Model.components_partition _).2 C hC
      exact h K hK C hCK
    · intro h K hK C hCK
      exact h C ((Model.components_partition _).1 K hK hCK)
  rw [hcn] at h
  have hE : (Fintype.card E : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.prod_div_distrib, Finset.prod_const, div_eq_div_iff hE (pow_ne_zero _ hE)]
  exact_mod_cast h

/-- **Theorem 3.2**, union bound inside each component: `Pr[G_K] ≥ 1 - ∑_{C ∈ K} q^{-o(C)}`. -/
theorem prob_goodSet_ge {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Model.nfree q n))
    {K : Finset (Model.Cond q n)} (hK : K ⊆ Model.essConds q n) :
    1 - Model.weight q n K ≤ ((goodSet (F := F) (E := E) ζ K).card : ℚ) / Fintype.card E := by
  set V : Model.Cond q n → Finset E := fun C => univ.filter (· ∈ condKer (F := F) ζ C)
  have hV : ∀ C ∈ K, (V C).card = q ^ (n - Model.codim q n C) ∧ Model.codim q n C ≤ n := by
    intro C hC
    have h := card_condKer hζ (hK hC)
    refine ⟨?_, h.2⟩
    rw [← h.1, Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun w => by simp [V])
  have hsplit : Fintype.card E ≤ (goodSet (F := F) (E := E) ζ K).card + ∑ C ∈ K, (V C).card := by
    have h1 : (univ : Finset E) ⊆ goodSet (F := F) ζ K ∪ K.biUnion V := by
      intro w _
      by_cases hw : w ∈ goodSet (F := F) ζ K
      · exact Finset.mem_union_left _ hw
      · apply Finset.mem_union_right
        simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
          not_not] at hw
        obtain ⟨C, hC, hwC⟩ := hw
        exact Finset.mem_biUnion.2 ⟨C, hC, by simp [V, hwC]⟩
    calc Fintype.card E = (univ : Finset E).card := rfl
      _ ≤ (goodSet (F := F) ζ K ∪ K.biUnion V).card := Finset.card_le_card h1
      _ ≤ (goodSet (F := F) ζ K).card + (K.biUnion V).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _
  have hE : Fintype.card E = q ^ n := Module.card_eq_pow_finrank
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hEq : (Fintype.card E : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw : Model.weight q n K = (∑ C ∈ K, ((V C).card : ℚ)) / Fintype.card E := by
    unfold Model.weight
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun C hC => ?_
    rw [(hV C hC).1, hE]
    push_cast
    rw [eq_div_iff (pow_ne_zero _ hq0)]
    have e : (q : ℚ) ^ n = (q : ℚ) ^ Model.codim q n C * (q : ℚ) ^ (n - Model.codim q n C) := by
      rw [← pow_add, Nat.add_sub_cancel' (hV C hC).2]
    rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]
  rw [hw, sub_le_iff_le_add, ← add_div, le_div_iff₀ (by positivity), one_mul]
  exact_mod_cast hsplit

/-- **Theorem 3.2**, the lower bound `δ_n ≥ ∏_i (1 - w_{𝒞_i})` if every factor is
positive. (No root of unity is needed in the statement.) -/
theorem delta_ge_prod
    (hpos : ∀ K ∈ Model.components q n (Model.essConds q n), 0 < 1 - Model.weight q n K) :
    ∏ K ∈ Model.components q n (Model.essConds q n), (1 - Model.weight q n K) ≤
      (cnCount F E : ℚ) / Fintype.card E := by
  obtain ⟨ζ, hζ⟩ := exists_zeta (F := F) (E := E)
  rw [delta_eq_prod hζ]
  exact Finset.prod_le_prod₀ (fun K hK => (hpos K hK).le)
    (fun K hK => prob_goodSet_ge hζ ((Model.components_partition _).1 K hK))

end Setting


end MorganMullen
