import MorganMullen.Sec5Omega
import MorganMullen.Sec7Weights
import MorganMullen.Sec8Defs
import MorganMullen.Sec8Certificates

/-!
# Proposition 8.4: computational definitions

The Boolean checker for criterion `(*)` on the finite ranges of Proposition 8.4.
Soundness is proved in `Fin32Sound.lean`; the computations are run in `Fin32Runs.lean`.

For a pair `(q, n)` the checker computes

* the divisors of `n` (trial division up to `√n`, `divList`);
* `Ω = ω(q - 1) + ∑_{k ∣ n, k > 1} tUpper q k ≥ omegaBd q n`, where `tUpper q k` is the value of a sieve
  for `t_k` of Lemma 5.1 (only `tUpper q k ≥ t_k` is proved) if `φ(k) ⌊log₂ q⌋ ≤ 3000`, and otherwise an
  integer upper bound for the second bound of Lemma 5.1 (the proof of Proposition 8.4 in the paper);
* the exact `M = ∑_{(d,e)} ν_{d,e}` over the essential types (`numM_eq`), with `ord_e(q)`
  computed by the standard algorithm and *verified* (`verifyOrd`), and `φ(e)` by `totientFast`;
* an upper bound `S ≤ Sint / 2^64` (each `q^{-o}` replaced by `⌊2^64/q^o⌋ + 1`, resp. by `1`
  if `o ≥ 64`);

and checks `q^n ≥ 2048` and the rational inequality
`Ω + M + (r/s)/W · Sint/2^64 + 1 + 1/1000 ≤ n a / (2 b)` with `2^a ≤ q^b` (so `a/b ≤ log₂ q`) and
`(1/(1-W))^s ≤ 2^r` (so `c(W) ≤ (r/s)/W`). Since `log₂(q^n - 1) ≥ n log₂ q - 1/1000` for
`q^n ≥ 2048`, this is criterion `(*)` with one bit to spare (Proposition 8.4).
-/

namespace MorganMullen.Fin32

open MorganMullen

/-! ### Divisors by trial division -/

/-- `sdAux n i acc`: the divisors `j ∈ [1, i]` of `n` (ascending), prepended to `acc`. -/
def sdAux (n : ℕ) : ℕ → List ℕ → List ℕ
  | 0, acc => acc
  | i + 1, acc => sdAux n i (if n % (i + 1) = 0 then (i + 1) :: acc else acc)

/-- The divisors `≤ √n` of `n`. -/
def smallDivs (n : ℕ) : List ℕ := sdAux n n.sqrt []

/-- All divisors of `n` (`n > 0`), without repetition. -/
def divList (n : ℕ) : List ℕ :=
  let s := smallDivs n
  s ++ (s.filter (fun i => i * i != n)).map (n / ·)

/-! ### `p`-free part -/

/-- `n` with all factors `p` removed. -/
def remP (p n : ℕ) : ℕ :=
  if _h : 1 < p ∧ 0 < n ∧ n % p = 0 then remP p (n / p) else n
termination_by n
decreasing_by exact Nat.div_lt_self _h.2.1 _h.1

/-! ### Multiplicative orders -/

/-- Divide `o` by `r` as long as `r ∣ o` and `q^(o/r) ≡ 1 (mod e)`. -/
def reduceOne (q e o r : ℕ) : ℕ :=
  if _h : 1 < r ∧ 0 < o ∧ o % r = 0 then
    if Cert.powModNat q (o / r) e = 1 % e then reduceOne q e (o / r) r else o
  else o
termination_by o
decreasing_by exact Nat.div_lt_self _h.2.1 _h.1

/-- Candidate for `ord_e(q)` (standard algorithm, starting from `φ(e)`); not trusted. -/
def ordCand (q e : ℕ) : ℕ :=
  let ph := totientFast e
  ph.primeFactorsList.dedup.foldl (fun o r => reduceOne q e o r) ph

/-- Verification that `o = ord_e(q)`: `q^o ≡ 1` and `q^(o/r) ≢ 1` for the primes `r ∣ o`. -/
def verifyOrd (q e o : ℕ) : Bool :=
  0 < o && 0 < e && Cert.powModNat q o e == 1 % e &&
    o.primeFactorsList.all (fun r => Cert.powModNat q (o / r) e != 1 % e)

/-- `ord_e(q)` if the verification succeeds, `0` otherwise. -/
def ordChecked (q e : ℕ) : ℕ :=
  let o := ordCand q e
  if verifyOrd q e o then o else 0

/-! ### Tables -/

/-- table lookup with fallback. -/
@[inline] def look (tbl : Array ℕ) (f : ℕ → ℕ) (i : ℕ) : ℕ :=
  if h : i < tbl.size then tbl[i] else f i

/-- `ordChecked q e` for `e < N`. -/
def ordTbl (q N : ℕ) : Array ℕ := Array.ofFn (n := N) fun i => ordChecked q i.1

/-- `φ(e)` for `e < N`. -/
def phiTbl (N : ℕ) : Array ℕ := Array.ofFn (n := N) fun i => totientFast i.1

/-- `tUpper q k` for `k < N`. -/
def tTbl (q N : ℕ) : Array ℕ := Array.ofFn (n := N) fun i => tUpper q i.1

/-! ### The check for one pair `(q, n)` -/

/-- Parameters: `2^a ≤ q^b` and `(1/(1-W))^s ≤ 2^r`. -/
structure Par where
  a : ℕ
  b : ℕ
  r : ℕ
  s : ℕ

/-- `⌊2^64/q^o⌋ + 1 ≥ 2^64 q^{-o}` (`1` if `o ≥ 64`). -/
def U64 (q o : ℕ) : ℕ := if 64 ≤ o then 1 else 2 ^ 64 / q ^ o + 1

/-- `ω(q-1) + ∑_{k ∈ D, k > 1} tF k`. -/
def omegaC (q : ℕ) (tF : ℕ → ℕ) (D : List ℕ) : ℕ :=
  (q - 1).primeFactors.card + (D.map fun k => if 1 < k then tF k else 0).sum

/-- The double sum over `d ∈ D`, `e ∈ E` of `g d e` restricted to the essential types. -/
def essSum (oF : ℕ → ℕ) (p n' : ℕ) (D E : List ℕ) (g : ℕ → ℕ → ℕ) : ℕ :=
  (D.map fun d =>
    let N := n' / remP p d
    (E.map fun e => if N % e = 0 ∧ oF e % d = 0 then g d e else 0).sum).sum

/-- `ν_{d,e}` from the tables. -/
def nuC (oF phiF : ℕ → ℕ) (d e : ℕ) : ℕ := d * phiF e / oF e

/-- The summand of `Sint`. -/
def sTerm (q : ℕ) (oF phiF : ℕ → ℕ) (d e : ℕ) : ℕ :=
  if 2 ≤ oF e then nuC oF phiF d e * U64 q (oF e) else 0

/-- The rational inequality. -/
def finalIneq (q : ℕ) (P : Par) (n Ω M S : ℕ) : Bool :=
  decide (((Ω + M : ℕ) : ℚ) + (P.r : ℚ) / P.s / Wq q * ((S : ℚ) / 2 ^ 64) + 1 + 1 / 1000 ≤
    (n : ℚ) * P.a / (2 * P.b))

/-- The check of `(*)` for one pair `(q, n)`. -/
def chkN (q : ℕ) (P : Par) (oF phiF tF : ℕ → ℕ) (n : ℕ) : Bool :=
  let p := q.minFac
  let n' := remP p n
  let D := divList n
  let E := D.filter (fun e => n' % e = 0)
  E.all (fun e => oF e != 0) && decide (2048 ≤ q ^ min n 11) &&
    finalIneq q P n (omegaC q tF D) (essSum oF p n' D E (nuC oF phiF))
      (essSum oF p n' D E (sTerm q oF phiF))

/-! ### Parameters and blocks -/

/-- Checks of the parameters: `2^a ≤ q^b`, `0 < W < 1`, `(1/(1-W))^s ≤ 2^r`. -/
def parOK (q : ℕ) (P : Par) : Bool :=
  let W := Wq q
  decide (0 < P.b) && decide (2 ^ P.a ≤ q ^ P.b) && decide (0 < P.s) && decide (0 < W.num) &&
    decide (W.num.toNat < W.den) &&
    decide (W.den ^ P.s ≤ 2 ^ P.r * (W.den - W.num.toNat) ^ P.s)

/-- Boolean version of `InAnalyticRange`. -/
def inAnalyticB (q n : ℕ) : Bool :=
  (q == 2 && 16674 ≤ n) ||
  (q == 3 && n % 3 == 0 && 1575 ≤ n) ||
  (q == 3 && n % 3 != 0 && 131200 ≤ n) ||
  (q == 4 && 1010 ≤ n) ||
  (q == 5 && 43618 ≤ n) ||
  (q == 7 && 336 ≤ n) ||
  (8 ≤ q && q ≤ 31 && thresholdN q ≤ n) ||
  (32 ≤ q && 14 ≤ n)

/-- The pairs that have to be checked. -/
def needed (q n : ℕ) : Bool :=
  q < n && !inAnalyticB q n && !certPairs.contains (q, n)

/-- `∀ n ∈ [lo, lo + len), f n`. -/
def allFrom (f : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, len + 1 => f lo && allFrom f (lo + 1) len

/-- The check of all needed `n ∈ [lo, hi)` (tables of size `N`). -/
def blockOK (q : ℕ) (P : Par) (N lo hi : ℕ) : Bool :=
  let OT := ordTbl q N
  let PT := phiTbl N
  let TT := tTbl q N
  parOK q P && allFrom (fun n => !needed q n ||
    chkN q P (look OT (ordChecked q)) (look PT totientFast) (look TT (tUpper q)) n) lo (hi - lo)

/-! ### The parameters -/

/-- The parameters for `q ≤ 19`: `a/b` is a lower convergent of `log₂ q` (exact for `q = 2^k`) and
`r/s` an upper convergent of `log₂(1/(1 - W(q)))` (exact for `q = 2`); both are checked by `parOK`.
(For `q ∈ {23, …, 31}` there is nothing to check.) -/
def par : ℕ → Par
  | 2 => ⟨1, 1, 2, 1⟩
  | 3 => ⟨50508, 31867, 6583, 7763⟩
  | 4 => ⟨2, 1, 9170, 18213⟩
  | 5 => ⟨29384, 12655, 5178, 8663⟩
  | 7 => ⟨6718, 2393, 2719, 10227⟩
  | 8 => ⟨3, 1, 107, 1544⟩
  | 9 => ⟨2108, 665, 374, 2445⟩
  | 11 => ⟨3283, 949, 1569, 15682⟩
  | 13 => ⟨19357, 5231, 442, 6255⟩
  | 16 => ⟨4, 1, 33, 1927⟩
  | 17 => ⟨16497, 4036, 355, 8696⟩
  | 19 => ⟨5123, 1206, 83, 2551⟩
  | _ => ⟨0, 1, 0, 1⟩

/-! ### The computations of Proposition 8.4 (run in `Fin32Runs.lean`) -/

def blk2 : Bool := blockOK 2 (par 2) 16674 3 16674
def blk3 : Bool := blockOK 3 (par 3) 131200 4 131200
def blk4 : Bool := blockOK 4 (par 4) 1010 5 1010
def blk5 : Bool := blockOK 5 (par 5) 43618 6 43618
def blk7 : Bool := blockOK 7 (par 7) 336 8 336
def blk8 : Bool := blockOK 8 (par 8) 171 9 171
def blk9 : Bool := blockOK 9 (par 9) 111 10 111
def blk11 : Bool := blockOK 11 (par 11) 65 12 65
def blk13 : Bool := blockOK 13 (par 13) 45 14 45
def blk16 : Bool := blockOK 16 (par 16) 32 17 32
def blk17 : Bool := blockOK 17 (par 17) 29 18 29
def blk19 : Bool := blockOK 19 (par 19) 25 20 25

end MorganMullen.Fin32
