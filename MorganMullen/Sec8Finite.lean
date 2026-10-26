import MorganMullen.Sec8Defs
import MorganMullen.Sec5Omega
import MorganMullen.Sec5Types
import MorganMullen.Sec7Weights
import MorganMullen.Sec8Certificates
import MorganMullen.Fin32Sound
import MorganMullen.Fin32Runs

/-!
# Proposition 8.4: the finite ranges (verified computation)

The Boolean checker `Fin32.chkN` (`Fin32Comp.lean`) evaluates criterion `(*)` with rational upper
bounds for `ω`, `M`, `c(W) S` and a rational lower bound for the right-hand side; its soundness is
`Fin32.chkN_sound` (`Fin32Sound.lean`), and the block checks covering all needed pairs are evaluated
in `Fin32Runs.lean` (via `Lean.ofReduceBool`).
-/

namespace MorganMullen

open Module Finset

/-- **Proposition 8.4** (finite ranges): for `q < 32`, `q < n`, outside the
ranges of Proposition 8.3 and outside the `70` pairs of Proposition 8.5, criterion `(*)` holds with
`W = W(q)`, the exact `M` and `S`, the bound of Lemma 5.1 for `ω(q^n - 1)`, and a margin of at
least one bit (`ω` is replaced by `omegaBd q n + 1`). -/
theorem finite_ranges (q n : ℕ) [NeZero n] (hq : IsPrimePow q) (hq32 : q < 32) (hqn : q < n)
    (hA : ¬ InAnalyticRange q n) (hC : (q, n) ∉ certPairs) :
    StarHolds q n (Wq q) ((omegaBd q n : ℝ) + 1) (Model.numM q n) (Model.sumS q n) := by
  have hneed := Fin32.needed_of hqn hA hC
  simp only [InAnalyticRange, not_or] at hA
  obtain ⟨h2, h3a, h3b, h4, h5, h7, h8, -⟩ := hA
  have h15 : q ≠ 15 := by
    rintro rfl
    exact Fin32.not_isPrimePow_of_dvd Nat.prime_three Nat.prime_five (by norm_num) (by norm_num)
      (by norm_num) hq
  have h21 : q ≠ 21 := by
    rintro rfl
    exact Fin32.not_isPrimePow_of_dvd Nat.prime_three Nat.prime_seven (by norm_num)
      (by norm_num) (by norm_num) hq
  have hqs : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 11 ∨ q = 13 ∨
      q = 16 ∨ q = 17 ∨ q = 19 ∨ q = 23 ∨ q = 25 ∨ q = 27 ∨ q = 29 ∨ q = 31 := by
    interval_cases q <;> first | omega | exact absurd hq (by decide)
  rcases hqs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact Fin32.blockOK_sound hq Fin32.blk2_ok n (by omega)
      (by by_contra h; exact h2 ⟨rfl, by omega⟩) hneed
  · have hn : n < 131200 := by
      by_contra h
      by_cases h3 : 3 ∣ n
      · exact h3a ⟨rfl, h3, by omega⟩
      · exact h3b ⟨rfl, h3, by omega⟩
    exact Fin32.blockOK_sound hq Fin32.blk3_ok n (by omega) hn hneed
  · exact Fin32.blockOK_sound hq Fin32.blk4_ok n (by omega)
      (by by_contra h; exact h4 ⟨rfl, by omega⟩) hneed
  · exact Fin32.blockOK_sound hq Fin32.blk5_ok n (by omega)
      (by by_contra h; exact h5 ⟨rfl, by omega⟩) hneed
  · exact Fin32.blockOK_sound hq Fin32.blk7_ok n (by omega)
      (by by_contra h; exact h7 ⟨rfl, by omega⟩) hneed
  · exact Fin32.blockOK_sound hq Fin32.blk8_ok n (by omega)
      (by by_contra h; exact h8 ⟨by norm_num, by norm_num, by rw [show thresholdN 8 = 171 from rfl]; omega⟩) hneed
  · exact Fin32.blockOK_sound hq Fin32.blk9_ok n (by omega)
      (by by_contra h; exact h8 ⟨by norm_num, by norm_num, by rw [show thresholdN 9 = 111 from rfl]; omega⟩) hneed
  · exact Fin32.blockOK_sound hq Fin32.blk11_ok n (by omega)
      (by by_contra h; exact h8 ⟨by norm_num, by norm_num, by rw [show thresholdN 11 = 65 from rfl]; omega⟩) hneed
  · exact Fin32.blockOK_sound hq Fin32.blk13_ok n (by omega)
      (by by_contra h; exact h8 ⟨by norm_num, by norm_num, by rw [show thresholdN 13 = 45 from rfl]; omega⟩) hneed
  · exact Fin32.blockOK_sound hq Fin32.blk16_ok n (by omega)
      (by by_contra h; exact h8 ⟨by norm_num, by norm_num, by rw [show thresholdN 16 = 32 from rfl]; omega⟩) hneed
  · exact Fin32.blockOK_sound hq Fin32.blk17_ok n (by omega)
      (by by_contra h; exact h8 ⟨by norm_num, by norm_num, by rw [show thresholdN 17 = 29 from rfl]; omega⟩) hneed
  · exact Fin32.blockOK_sound hq Fin32.blk19_ok n (by omega)
      (by by_contra h; exact h8 ⟨by norm_num, by norm_num, by rw [show thresholdN 19 = 25 from rfl]; omega⟩) hneed
  · exact absurd ⟨by norm_num, by norm_num, by rw [show thresholdN 23 = 19 from rfl]; omega⟩ h8
  · exact absurd ⟨by norm_num, by norm_num, by rw [show thresholdN 25 = 18 from rfl]; omega⟩ h8
  · exact absurd ⟨by norm_num, by norm_num, by rw [show thresholdN 27 = 16 from rfl]; omega⟩ h8
  · exact absurd ⟨by norm_num, by norm_num, by rw [show thresholdN 29 = 15 from rfl]; omega⟩ h8
  · exact absurd ⟨by norm_num, by norm_num, by rw [show thresholdN 31 = 14 from rfl]; omega⟩ h8

end MorganMullen
