import MorganMullen.Sec7Structure
import MorganMullen.ExactSound

/-!
# Section 7 (continued): step (i) of the proof of Theorem 7.8

For `(q, o₀) ∈ {(2,3), (2,6), (3,2), (3,4)}` the bound `W_cl(q, o₀)` exceeds `W(q)`, so Theorem 7.8 computes
exactly; by Proposition 7.7 it suffices to consider the finitely many `n₀ ∣ N**`, and `N**` divides
`42, 378, 16, 320`. Here: for every divisor `n₀` of these numbers, every component (of the
essential conditions for `(q, n₀)`) without a condition of codimension `1` has weight at most
`3/4` (`q = 2`) resp. `4/9` (`q = 3`).

As in the paper, the check `Exact.caseOK q n₀ W` (`ExactComp.lean`, soundness in `ExactSound.lean`)
uses a labelling of `ℤ/n₀'`, computed by the unverified function `labArr` (only the check is trusted):
it verifies that the labels are invariant under `i ↦ q i` and constant on the fibres of the essential
conditions, and bounds the total weight of the essential conditions of codimension `≥ 2` of each label.
All 30 cases are run at once (`Exact.allOK_eq_true`, evaluated by the Lean compiler/interpreter via
the axiom `Lean.ofReduceBool`; about 0.2 s).
-/

namespace MorganMullen

namespace Exact

set_option linter.deprecated false in
/-- **The computation**: all cases pass the check. The proof term
`Lean.ofReduceBool allOK true rfl` is the one that the tactic `of_reduce_bool` of
`Sec8Certificates.lean` produces: the kernel hands `Lean.reduceBool allOK` to Lean's compiler and
interpreter (outside the kernel) and accepts the result. -/
theorem allOK_eq_true : allOK = true := Lean.ofReduceBool allOK true rfl

lemma caseOK_of_allOK {q n₀ : ℕ} (hn₀ : n₀ ≠ 0)
    (h : (q = 2 ∧ (n₀ ∣ 42 ∨ n₀ ∣ 378)) ∨ (q = 3 ∧ (n₀ ∣ 16 ∨ n₀ ∣ 320))) :
    caseOK q n₀ (if q = 2 then 3 / 4 else 4 / 9) = true := by
  have hall := allOK_eq_true
  simp only [allOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hall
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · have hle : n₀ < 379 := by
      rcases h with h | h <;> have := Nat.le_of_dvd (by norm_num) h <;> omega
    rcases hall.1 n₀ hle with (h0 | h1) | h2
    · exact absurd h0 hn₀
    · rcases h with h | h
      · exact absurd (Nat.mod_eq_zero_of_dvd h) h1.1
      · exact absurd (Nat.mod_eq_zero_of_dvd h) h1.2
    · simpa using h2
  · have hle : n₀ < 321 := by
      rcases h with h | h <;> have := Nat.le_of_dvd (by norm_num) h <;> omega
    rcases hall.2 n₀ hle with (h0 | h1) | h2
    · exact absurd h0 hn₀
    · rcases h with h | h
      · exact absurd (Nat.mod_eq_zero_of_dvd h) h1.1
      · exact absurd (Nat.mod_eq_zero_of_dvd h) h1.2
    · simpa using h2

end Exact

/-- **Exact maxima** (Theorem 7.8, step (i)): for `q = 2` and `n₀ ∣ 42` or `n₀ ∣ 378`, and for `q = 3` and
`n₀ ∣ 16` or `n₀ ∣ 320`, every component without a condition of codimension `1` has weight at most
`3/4` resp. `4/9`. -/
theorem exact_max_bound (q n₀ : ℕ) [NeZero n₀]
    (h : (q = 2 ∧ (n₀ ∣ 42 ∨ n₀ ∣ 378)) ∨ (q = 3 ∧ (n₀ ∣ 16 ∨ n₀ ∣ 320)))
    {K : Finset (Model.Cond q n₀)} (hK : K ∈ Model.components q n₀ (Model.essConds q n₀))
    (hK2 : ∀ C ∈ K, 2 ≤ Model.codim q n₀ C) :
    Model.weight q n₀ K ≤ if q = 2 then 3 / 4 else 4 / 9 := by
  have hq : q.Prime := by
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Nat.prime_two
    · exact Nat.prime_three
  obtain ⟨oF, lab, hchk⟩ := Exact.caseOK_sound (Exact.caseOK_of_allOK (NeZero.ne n₀) h)
  exact Exact.chk_sound hq hchk hK hK2

end MorganMullen
