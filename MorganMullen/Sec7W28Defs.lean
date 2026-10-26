import MorganMullen.Sec7Structure
import MorganMullen.Sec7W28Data

/-!
# Theorem 7.8: computable checkers for the bounds `W_cl(q, o₀)` and `W_cr(q, o₀)`

All checks are Boolean functions, evaluated in `Sec7W28Runs.lean` (via `Lean.ofReduceBool`);
their soundness is proved in `Sec7W28Sound.lean`.

For `O, D` and a cut-off `m ≥ max(7, o₀)` the checker `chkW` bounds
`Wsum q o₀ O D = ∑_{o ∣ O, o ≥ o₀} q^{-o} ∑_{d ∣ o, d' ∣ D} d gcd(q^o - 1, D/d')`
by the exact terms with `o < m` plus the crude tail `3 m² D q^{-m}` (from
`∑_{d ∣ o, d' ∣ D} d gcd(⋯) ≤ σ_1(o) D ≤ o² D` and `∑_{o ≥ m} o² q^{-o} ≤ 3 m² q^{-m}`),
and compares with `W` in exact rational arithmetic.

* `certOK` checks the hypotheses of `closure_cert` (modular exponentiations only);
* `chkU` is the uniform crude check for all `q ≥ 32` (with `Λ = o₀ lcm(1, …, o₀)`, `q ≥ 32`);
* `rsOK` checks the start of the Rosser–Schoenfeld tail `3 o³ 2.83^o q^{-o} ≤ W`.
-/

namespace MorganMullen.W28

open MorganMullen Finset

/-- `n` with all factors `p` removed. -/
def remP (p n : ℕ) : ℕ :=
  if _h : 1 < p ∧ 0 < n ∧ n % p = 0 then remP p (n / p) else n
termination_by n
decreasing_by exact Nat.div_lt_self _h.2.1 _h.1

/-- Modular exponentiation `b^e mod m` by repeated squaring. -/
def powMod (b m : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | e + 1 =>
    let h := powMod b m ((e + 1) / 2)
    if (e + 1) % 2 = 0 then h * h % m else h * h % m * b % m
decreasing_by omega

/-- The inner sum `∑_{d ∣ o, d' ∣ D} d gcd(q^o - 1, D/d')`. -/
def innerN (q p o D : ℕ) : ℕ :=
  ∑ d ∈ o.divisors.filter (fun d => remP p d ∣ D), d * Nat.gcd (q ^ o - 1) (D / remP p d)

/-- The exact part `∑_{o₀ ≤ o < m, o ∣ O} inner(o) q^{m-o}` (scaled by `q^m`). -/
def exactS (q p o₀ O D m : ℕ) : ℕ :=
  ∑ o ∈ (Ico o₀ m).filter (· ∣ O), innerN q p o D * q ^ (m - o)

/-- The crude tail `3 m² B` (scaled by `Q^m`); it vanishes if `O < m`. -/
def tailS (O B m : ℕ) : ℕ := if O < m then 0 else 3 * m ^ 2 * B

/-- The check `Wsum q o₀ O D ≤ W` with cut-off `m`. -/
def chkW (q o₀ O D m : ℕ) (W : ℚ) : Bool :=
  decide (7 ≤ m) && decide (o₀ ≤ m) && decide (0 < O) && decide (0 < D) &&
    decide (((exactS q q.minFac o₀ O D m + tailS O D m : ℕ) : ℚ) ≤ W * (q : ℚ) ^ m)

/-- `K₀ = o₀' (q^{o₀} - 1)`. -/
def K0c (q o₀ : ℕ) : ℕ := remP q.minFac o₀ * (q ^ o₀ - 1)

/-- The hypotheses of `closure_cert` for `(Ô, D̂, M) = (O, D, M)`. -/
def certOK (q o₀ O D M : ℕ) : Bool :=
  decide (0 < O) && decide (0 < D) && O % o₀ == 0 &&
    powMod q (K0c q o₀) O == 1 % K0c q o₀ && D % remP q.minFac O == 0 &&
    powMod q D M == 1 % D && D % remP q.minFac M == 0 && O % M == 0

/-- The cut-off `m = o₀ + 41` of the proof of Theorem 7.8: the terms with `o ≤ o₀ + 40` are
evaluated exactly, the others by the crude tail `3 m² D q^{-m}`. -/
def mm (o₀ : ℕ) : ℕ := o₀ + 41

/-! ### Closure certificates (`q = 2, 3`) -/

/-- Parse `"a b c"`. -/
def parseTriple (s : String) : ℕ × ℕ × ℕ :=
  match (s.splitOn " ").map (fun t => t.toNat?.getD 0) with
  | [a, b, c] => (a, b, c)
  | _ => (0, 0, 0)

/-- Parse `"a b c;a b c;…"`. -/
def parseData (s : String) : Array (ℕ × ℕ × ℕ) := ((s.splitOn ";").map parseTriple).toArray

/-- the certificates for `q = 2` -/
def data2 : Array (ℕ × ℕ × ℕ) := parseData dataStr2

/-- the certificates for `q = 3` -/
def data3 : Array (ℕ × ℕ × ℕ) := parseData dataStr3

/-- The check of `W_cl(q, o₀) ≤ W` via the certificate of index `o₀ - 2`. -/
def clOK (q : ℕ) (W : ℚ) (data : Array (ℕ × ℕ × ℕ)) (o₀ : ℕ) : Bool :=
  let c := data.getD (o₀ - 2) (0, 0, 0)
  certOK q o₀ c.1 c.2.1 c.2.2 && chkW q o₀ c.1 c.2.1 (mm o₀) W

/-- The target for `W_cl(2, o₀)`: `W(2) = 3/4` for `o₀ ≤ 8`, and `0.032` from `o₀ = 9` on. -/
def tgt2 (o₀ : ℕ) : ℚ := if o₀ ≤ 8 then 3 / 4 else 4 / 125

/-- `q = 2`: `W_cl(2, o₀) ≤ tgt2 o₀` for `2 ≤ o₀ ≤ 4095`, `o₀ ∉ {3, 6}`. -/
def run2 : Bool := (List.range' 2 4094).all fun o₀ => o₀ == 3 || o₀ == 6 || clOK 2 (tgt2 o₀) data2 o₀

/-- The target for `W_cl(3, o₀)`: `W(3) = 4/9` for `o₀ ≤ 6`, and `0.051` from `o₀ = 7` on. -/
def tgt3 (o₀ : ℕ) : ℚ := if o₀ ≤ 6 then 4 / 9 else 51 / 1000

/-- `q = 3`: `W_cl(3, o₀) ≤ tgt3 o₀` for `3 ≤ o₀ ≤ 374`, `o₀ ≠ 4`. -/
def run3 : Bool := (List.range' 3 372).all fun o₀ => o₀ == 4 || clOK 3 (tgt3 o₀) data3 o₀

/-- The exceptional cases: certified multiples (step (i) of Theorem 7.8) with `N** ∣ 42, 378, 16, 320`. -/
def runExc : Bool :=
  certOK 2 3 6 3 2 && Nat.lcm (Nat.lcm (K0c 2 3) 3) 6 ∣ 42 &&
  certOK 2 6 18 9 6 && Nat.lcm (Nat.lcm (K0c 2 6) 9) 18 ∣ 378 &&
  certOK 3 2 4 4 2 && Nat.lcm (Nat.lcm (K0c 3 2) 4) 4 ∣ 16 &&
  certOK 3 4 16 16 4 && Nat.lcm (Nat.lcm (K0c 3 4) 16) 16 ∣ 320

/-! ### The crude choice (A) for `4 ≤ q ≤ 31` -/

/-- `Λ = o₀' lcm(1, …, o₀)`. -/
def LamC (q o₀ : ℕ) : ℕ := remP q.minFac o₀ * lcmUpTo o₀

/-- The check of `W_cr(q, o₀) ≤ W`. -/
def crOK (q : ℕ) (W : ℚ) (o₀ : ℕ) : Bool :=
  chkW q o₀ (LamC q o₀) (remP q.minFac (LamC q o₀)) (mm o₀) W

/-- Start of the Rosser–Schoenfeld tail: `3 o₁³ 283^{o₁} ≤ W (100 q)^{o₁}` and the ratio of
consecutive terms is `≤ 1` from `o₁` on. -/
def rsOK (q o₁ : ℕ) (W : ℚ) : Bool :=
  decide (7 ≤ o₁) && decide ((3 * o₁ ^ 3 * 283 ^ o₁ : ℕ) ≤ W * ((100 * q) ^ o₁ : ℕ)) &&
    decide ((o₁ + 1) ^ 3 * 283 ≤ o₁ ^ 3 * (100 * q))

/-- `W_cr(q, o₀) ≤ W` for `2 ≤ o₀ < o₁` and the start of the tail at `o₁`. -/
def fixedOK (q o₁ : ℕ) (W : ℚ) : Bool :=
  (List.range' 2 (o₁ - 2)).all (crOK q W) && rsOK q o₁ W

/-- The prime powers `4 ≤ q ≤ 31`, the start `o₁` of the analytic tail, and `W(q)`. -/
def qtab : List (ℕ × ℕ × ℚ) :=
  [(4, 39, 0.2946), (5, 20, 0.3392), (7, 12, 0.1683), (8, 11, 0.0469), (9, 9, 0.1006),
   (11, 8, 0.0670), (13, 7, 0.0478), (16, 7, 0.0118), (17, 7, 0.0279), (19, 7, 0.0223),
   (23, 7, 0.0152), (25, 7, 0.0129), (27, 7, 0.0110), (29, 7, 0.0096), (31, 7, 0.0084)]

/-- All fixed `q`. -/
def runFixed : Bool := qtab.all fun e => fixedOK e.1 e.2.1 e.2.2

/-! ### `q ≥ 32` (uniformly) and the tail for `q = 3` -/

/-- `σ_1(o)`. -/
def sigmaN (o : ℕ) : ℕ := ∑ d ∈ o.divisors, d

/-- `Λ⁺ = o₀ lcm(1, …, o₀)` (a multiple of `Λ` for every `p`). -/
def LamF (o₀ : ℕ) : ℕ := o₀ * lcmUpTo o₀

/-- The uniform check `∑_{o ∣ Λ⁺, o ≥ o₀} σ_1(o) Λ⁺ 32^{-o} ≤ 0.0118` (cut-off `m`). -/
def chkU (o₀ m : ℕ) : Bool :=
  decide (7 ≤ m) && decide (o₀ ≤ m) && decide (0 < LamF o₀) &&
    decide (((∑ o ∈ (Ico o₀ m).filter (· ∣ LamF o₀), sigmaN o * LamF o₀ * 32 ^ (m - o) +
      tailS (LamF o₀) (LamF o₀) m : ℕ) : ℚ) ≤ (0.0118 : ℚ) * (32 : ℚ) ^ m)

/-- `q ≥ 32`: `2 ≤ o₀ ≤ 6` uniformly (cut-off `o₀ + 41`), and the tail from `7` on;
`q = 3`: the tail `≤ 0.051` from `375` on. -/
def runBig : Bool :=
  (List.range' 2 5).all (fun o₀ => chkU o₀ (o₀ + 41)) && rsOK 32 7 0.0118 && rsOK 3 375 (51 / 1000)

end MorganMullen.W28
