import MorganMullen.Sec4Abstract
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Section 8: definitions shared by the main theorem and the finite computations

* `c(W)`, the criterion `(*)` of Theorem 8.1 (b) (`StarHolds`);
* the thresholds and ranges of Proposition 8.3.
-/

namespace MorganMullen

/-- `c(W) = log₂(1/(1-W)) / W`. -/
noncomputable def cW (W : ℝ) : ℝ := Real.logb 2 (1 / (1 - W)) / W

/-- Criterion `(*)`: `log₂(q^n - 1) - (n/2) log₂ q ≥ ω + M + c(W) S`. -/
def StarHolds (q n : ℕ) (W ω M S : ℝ) : Prop :=
  ω + M + cW W * S ≤ Real.logb 2 ((q : ℝ) ^ n - 1) - n / 2 * Real.logb 2 q

/-! ### Proposition 8.3: thresholds and ranges -/

/-- The thresholds `n_*(q)` of Proposition 8.3 for `8 ≤ q ≤ 31`. -/
def thresholdN : ℕ → ℕ
  | 8 => 171
  | 9 => 111
  | 11 => 65
  | 13 => 45
  | 16 => 32
  | 17 => 29
  | 19 => 25
  | 23 => 19
  | 25 => 18
  | 27 => 16
  | 29 => 15
  | 31 => 14
  | _ => 0

/-- The ranges of Proposition 8.3. -/
def InAnalyticRange (q n : ℕ) : Prop :=
  (q = 2 ∧ 16674 ≤ n) ∨
  (q = 3 ∧ 3 ∣ n ∧ 1575 ≤ n) ∨
  (q = 3 ∧ ¬ 3 ∣ n ∧ 131200 ≤ n) ∨
  (q = 4 ∧ 1010 ≤ n) ∨
  (q = 5 ∧ 43618 ≤ n) ∨
  (q = 7 ∧ 336 ≤ n) ∨
  (8 ≤ q ∧ q ≤ 31 ∧ thresholdN q ≤ n) ∨
  (32 ≤ q ∧ 14 ≤ n)

end MorganMullen
