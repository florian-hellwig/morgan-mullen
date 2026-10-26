import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Frobenius

/-!
# Certificate checker: computational definitions (Proposition 8.5)

Packed arithmetic in `𝔽_p[x]/(f)` (Kronecker substitution, base `2^k`), Pratt primality
certificates, and the Boolean certificate checker. Soundness is proved in `CertProofs.lean`.
-/

namespace MorganMullen.Cert

open Finset

/-! ### Computational definitions -/

/-- `[a, f a, f (f a), …]` (length `n`). -/
def iterL {α : Type} (f : α → α) (a : α) : Nat → List α
  | 0 => []
  | n + 1 => a :: iterL f (f a) n

/-- digit `i` of `A` in base `2^k`. -/
def dig (k A i : Nat) : Nat := (A >>> (k * i)) &&& (2 ^ k - 1)

/-- `∑_{i<N} (e i % p) * 2^(k i)`. -/
def mkVec (p N k : Nat) (e : Nat → Nat) : Nat :=
  (List.range N).foldl (fun acc i => acc + (e i % p) <<< (k * i)) 0

/-- multiplication by `x` modulo `x^N + ∑ f_i x^i` (`f_i = dig k F i`). -/
def mulX (p N k F T : Nat) : Nat :=
  let s := p - dig k T (N - 1) % p
  mkVec p N k (fun i => (if i = 0 then 0 else dig k T (i - 1)) + s * dig k F i)

/-- the vector `x^j`. -/
def unitV (p N k j : Nat) : Nat := mkVec p N k (fun i => if i = j then 1 else 0)

def oneV (p N k : Nat) : Nat := unitV p N k 0

/-- table of `x^(N+j) mod f`, `j < N`. -/
def table (p N k F : Nat) : Array Nat :=
  (iterL (mulX p N k F) (mulX p N k F (unitV p N k (N - 1))) N).toArray

/-- multiplication modulo `f` (Kronecker substitution, then reduction with the table). -/
def mulMod (p N k : Nat) (T : Array Nat) (A A' : Nat) : Nat :=
  let C := A * A'
  let S := (List.range N).foldl (fun acc j => acc + dig k C (N + j) * T.getD j 0)
    (C &&& (2 ^ (k * N) - 1))
  mkVec p N k (dig k S)

/-- left-to-right binary powering. -/
def powMod (mul : Nat → Nat → Nat) (one b : Nat) (e : Nat) : Nat :=
  if h0 : e = 0 then one else if h1 : e = 1 then b else
    let h := powMod mul one b (e / 2)
    if e % 2 = 1 then mul (mul h h) b else mul h h
termination_by e
decreasing_by omega

/-- `w^E` from the Frobenius orbit `P[i] = w^(p^i)`, via the base-`p` digits of `E`. -/
def powDigits (mul : Nat → Nat → Nat) (one p N : Nat) (P : Array Nat) (E : Nat) : Nat :=
  (List.range N).foldl (fun acc i =>
    let e := E / p ^ i % p
    if e = 0 then acc else mul acc (powMod mul one (P.getD i 0) e)) one

/-- natural number modular exponentiation. -/
def powModNat (a e m : Nat) : Nat := powMod (fun x y => x * y % m) (1 % m) (a % m) e

def divOut (m f : Nat) : Nat → Nat
  | 0 => m
  | fuel + 1 => if 2 ≤ f ∧ 0 < m ∧ m % f = 0 then divOut (m / f) f fuel else m

def removeFactors (m : Nat) : List Nat → Nat
  | [] => m
  | f :: fs => removeFactors (divOut m f m) fs

/-- Pratt / Lucas check of one entry `(p, a, prime factors of p - 1)` given known primes. -/
def entryOK (known : List Nat) (e : Nat × Nat × List Nat) : Bool :=
  decide (2 ≤ e.1) && powModNat e.2.1 (e.1 - 1) e.1 == 1 &&
    e.2.2.all (fun f => decide (f ∈ known) && powModNat e.2.1 ((e.1 - 1) / f) e.1 != 1) &&
    removeFactors (e.1 - 1) e.2.2 == 1

def prattOK : List Nat → List (Nat × Nat × List Nat) → Bool
  | _, [] => true
  | known, e :: rest => entryOK known e && prattOK (e.1 :: known) rest

/-- linear combination `∑_{col<N} (dig h col % p) * V[col]`. -/
def lc (p N k h : Nat) (V : Array Nat) : Nat :=
  (List.range N).foldl (fun acc col => acc + (dig k h col % p) * V.getD col 0) 0

/-- Gauss–Jordan inverse over `𝔽_p`, packed rows (unverified; the result is checked). -/
def gaussP (p N k : Nat) (V : Array Nat) : Array Nat := Id.run do
  let mut rows : Array Nat := Array.ofFn (n := N) fun c => V.getD c.val 0 + 2 ^ (k * (N + c.val))
  for c in [0:N] do
    let mut piv := N
    for i in [c:N] do
      if piv == N && dig k (rows[i]!) c % p != 0 then piv := i
    if piv == N then return #[]
    let rc := rows[piv]!
    rows := rows.set! piv (rows[c]!)
    let inv := powModNat (dig k rc c % p) (p - 2) p
    let rc := mkVec p (2 * N) k (fun i => dig k rc i * inv)
    rows := rows.set! c rc
    for i in [0:N] do
      if i != c then
        let t := dig k (rows[i]!) c % p
        if t != 0 then
          rows := rows.set! i (rows[i]! + (p - t) * rc)
  return rows.map fun r => mkVec p N k (fun i => dig k r (N + i))

/-- Gauss–Jordan inverse over `𝔽_2` with bitsets (unverified; the result is checked). -/
def gauss2 (N k : Nat) (V : Array Nat) : Array Nat := Id.run do
  let toBits (x : Nat) : Nat :=
    (List.range N).foldl (fun acc i => if dig k x i % 2 = 1 then acc ||| (1 <<< i) else acc) 0
  let mut rows : Array Nat := Array.ofFn (n := N) fun c => toBits (V.getD c.val 0) ||| (1 <<< (N + c.val))
  for c in [0:N] do
    let mut piv := N
    for i in [c:N] do
      if piv == N && (rows[i]!).testBit c then piv := i
    if piv == N then return #[]
    let rc := rows[piv]!
    rows := rows.set! piv (rows[c]!)
    rows := rows.set! c rc
    for i in [0:N] do
      if i != c && (rows[i]!).testBit c then
        rows := rows.set! i (rows[i]! ^^^ rc)
  return rows.map fun r =>
    (List.range N).foldl (fun acc i => if r.testBit (N + i) then acc + (1 <<< (k * i)) else acc) 0

def gauss (p N k : Nat) (V : Array Nat) : Array Nat :=
  if p = 2 then gauss2 N k V else gaussP p N k V

def fromBase (p N k A : Nat) : Nat := mkVec p N k (fun i => A / p ^ i % p)

def goodify (p N k x : Nat) : Nat := mkVec p N k (dig k x)

def kOf (p N : Nat) : Nat := Nat.log2 (2 * N ^ 3 * p ^ 3) + 1

/-- normality check for one divisor `d` (`P[i] = w^(p^i)`). -/
def checkD (p r n N k : Nat) (T P : Array Nat) (d : Nat) : Bool :=
  let mul := mulMod p N k T
  let one := oneV p N k
  let rd := r * d
  let u := fun t => P.getD (r * (d * t)) 0
  let Bd := goodify p N k ((List.range (n / d)).foldl (fun acc t => mul acc (u t)) one)
  let BP := (iterL (fun b => mul b Bd) one rd).toArray
  let V := Array.ofFn (n := N) fun col =>
    if col.val % rd = 0 then u (col.val / rd) else mul (BP.getD (col.val % rd) 0) (u (col.val / rd))
  let H := gauss p N k V
  powMod mul one Bd (p ^ rd) == Bd &&
    (List.range N).all fun kk => mkVec p N k (dig k (lc p N k (H.getD kk 0) V)) == 2 ^ (k * kk)

structure CertRec where
  p : Nat
  r : Nat
  n : Nat
  fdat : Nat
  wdat : Nat
  primes : List Nat

def checkRec (known : List Nat) (c : CertRec) : Bool :=
  let p := c.p
  let N := c.r * c.n
  let k := kOf p N
  let F := fromBase p N k c.fdat
  let W := fromBase p N k c.wdat
  let T := table p N k F
  let mul := mulMod p N k T
  let one := oneV p N k
  let M := p ^ N - 1
  let P := (iterL (fun u => powMod mul one u p) W N).toArray
  let pw := powDigits mul one p N P
  decide (p ∈ known) && decide (0 < c.r) && decide (0 < c.n) &&
    pw M == one &&
    c.primes.all (fun l => decide (l ∈ known) && pw (M / l) != one) &&
    removeFactors M c.primes == 1 &&
    (List.range (c.n + 1)).all (fun d => if d ≠ 0 ∧ c.n % d = 0 then checkD p c.r c.n N k T P d else true)

end MorganMullen.Cert
