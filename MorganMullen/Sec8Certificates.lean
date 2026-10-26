import MorganMullen.Sec2Coordinates
import MorganMullen.CertProofs
import MorganMullen.CertData
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Proposition 8.5: explicit certificates for the `70` remaining pairs

For each pair `(q, n)` in `certPairs` a monic `f ∈ 𝔽_p[x]` of degree `N = [E : 𝔽_p]` and an element
`w ∈ 𝔽_p[x]/(f)` are given (data from `verification_code/pcn_certificates.txt`, see `CertData.lean`). The Boolean
checker `Cert.checkRec` (`CertDefs.lean`) verifies by computation

* that `w` has multiplicative order `p^N - 1 = q^n - 1` (the listed prime factors of `q^n - 1` are
  certified prime by Pratt certificates and exhaust `q^n - 1`); hence `𝔽_p[x]/(f)` is a field with
  `q^n` elements and `w` is primitive;
* that `w` is normal over `𝔽_{q^d}` for every `d ∣ n`: the `N` elements `β_d^j w^{q^{dt}}`
  (`j < rd`, `t < n/d`, `β_d = ∏_t w^{q^{dt}}` checked to satisfy `β_d^{q^d} = β_d`) span
  `𝔽_p[x]/(f)` over `𝔽_p` (an inverse matrix is computed and the product with it is checked).

The soundness of the checker is proved in `CertProofs.lean` (`Cert.checkRec_sound`); the result is
transferred to an arbitrary extension `E/F` with `|F| = q`, `[E : F] = n` (`hasMM_of_spanProp`).
The computation itself (`Cert.checkAll_eq_true`) is evaluated by the Lean compiler/interpreter via
the axiom `Lean.ofReduceBool` (about one minute).
-/

namespace MorganMullen

open Module FiniteField

/-- The `70` pairs of Proposition 8.5. -/
def certPairs : List (ℕ × ℕ) :=
  [(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 12), (2, 14), (2, 15),
   (2, 18), (2, 20), (2, 21), (2, 24), (2, 27), (2, 30), (2, 36), (2, 40), (2, 42), (2, 54),
   (2, 60), (2, 63), (2, 126), (2, 378),
   (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 10), (3, 12), (3, 13), (3, 16), (3, 20), (3, 24),
   (3, 26), (3, 32), (3, 39), (3, 40), (3, 80), (3, 160),
   (4, 5), (4, 6), (4, 7), (4, 9), (4, 10), (4, 15), (4, 21), (4, 30),
   (5, 6), (5, 8), (5, 12), (5, 16), (5, 18), (5, 24), (5, 32), (5, 48), (5, 104),
   (7, 8), (7, 12), (7, 16), (7, 18), (7, 24), (7, 48),
   (9, 10), (9, 20), (11, 12), (13, 20), (19, 24)]

/-- A primitive element satisfying the intrinsic normality condition `Cert.SpanProp` (with
`q = |F|`, `n = [E : F]`) is a Morgan–Mullen witness. -/
theorem hasMM_of_spanProp {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (w : E) (hprim : w ≠ 0 ∧ ∀ x : E, x ≠ 0 → ∃ k : ℕ, w ^ k = x)
    (hspan : Cert.SpanProp E (Fintype.card F) (finrank F E) w) : HasMMProperty F E := by
  refine ⟨w, hprim, (isCompletelyNormal_iff_levelField w).2 fun d hd => ?_⟩
  have hdn : d ∣ finrank F E := (Nat.mem_divisors.1 hd).1
  let _ : Fintype (levelField (F := F) (E := E) d) := Fintype.ofFinite _
  rw [isNormalElem_iff_span, eq_top_iff]
  intro y _
  obtain ⟨c, hc, rfl⟩ := hspan d hdn y
  have hL := finrank_levelField_top (F := F) (E := E) hdn
  have hcardL := card_levelField (F := F) (E := E) hdn
  apply Submodule.sum_mem
  intro t _
  have hcL : c t ∈ levelField (F := F) (E := E) d := mem_levelField.2 (hc t)
  have key : c t * w ^ (Fintype.card F ^ (d * t)) =
      (⟨c t, hcL⟩ : levelField (F := F) (E := E) d) •
        ((frobeniusAlgHom (levelField (F := F) (E := E) d) E) ^
          ((Fin.cast hL.symm t : Fin _) : ℕ)) w := by
    rw [frob_pow_apply, hcardL, ← pow_mul, Algebra.smul_def]
    rfl
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.cast hL.symm t, rfl⟩)

namespace Cert

/-- The global Boolean check: all Pratt certificates are valid, and every pair of `certPairs` has a
record in `certData` passing `checkRec`. -/
def checkAll : Bool :=
  prattOK [] prattData &&
    certPairs.all fun qn => certData.any fun c =>
      c.p ^ c.r == qn.1 && c.n == qn.2 && checkRec (prattData.map (·.1)) c

theorem checkAll_sound (h : checkAll = true) :
    (∀ x ∈ prattData.map (·.1), x.Prime) ∧
      ∀ qn ∈ certPairs, ∃ c ∈ certData, c.p ^ c.r = qn.1 ∧ c.n = qn.2 ∧
        checkRec (prattData.map (·.1)) c = true := by
  simp only [checkAll, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  refine ⟨fun x hx => ?_, fun qn hqn => ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact prattOK_sound prattData [] (by simp) h.1 e he
  · obtain ⟨c, hc, ⟨h1, h2⟩, h3⟩ := h.2 qn hqn
    exact ⟨c, hc, h1, h2, h3⟩

open Lean Meta Elab Tactic in
/-- Close a goal `c = true`, `c` a closed constant, by the term `Lean.ofReduceBool c true rfl`:
the kernel has `Lean.reduceBool c` evaluated outside the kernel, by Lean's compiler and interpreter
(and rejects the proof if the value is not `true`). This is the reflection principle behind `native_decide`, with the axiom
`Lean.ofReduceBool` (in this Lean version `native_decide` would instead add an auxiliary axiom
asserting `c = true`). -/
elab "of_reduce_bool" : tactic => liftMetaTactic fun g => do
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "of_reduce_bool: expected an equation `c = true`"
  unless rhs.isConstOf ``Bool.true && lhs.isConst do
    throwError "of_reduce_bool: expected `c = true` with `c` a constant"
  g.assign <| mkApp3 (mkConst ``Lean.ofReduceBool) lhs (mkConst ``Bool.true)
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  return []

/-- **The computation**: all certificates pass the check. -/
theorem checkAll_eq_true : checkAll = true := by of_reduce_bool

end Cert

/-- **Proposition 8.5** (explicit certificates): each of the `70` pairs has the
Morgan–Mullen property (an explicit primitive completely normal element is verified). -/
theorem certificates (F E : Type*) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (h : (Fintype.card F, finrank F E) ∈ certPairs) : HasMMProperty F E := by
  obtain ⟨hk, hpairs⟩ := Cert.checkAll_sound Cert.checkAll_eq_true
  obtain ⟨c, -, hq, hn, hc⟩ := hpairs _ h
  have hE : Fintype.card E = c.p ^ (c.r * c.n) := by
    rw [pow_mul, hq, hn, Module.card_eq_pow_finrank (K := F)]
  obtain ⟨w, hprim, hspan⟩ := Cert.checkRec_sound _ hk c hc E hE
  rw [hq, hn] at hspan
  exact hasMM_of_spanProp w hprim hspan

end MorganMullen
