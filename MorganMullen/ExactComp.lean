import MorganMullen.Model

/-!
# Exact maximal weights: the computable check

For a pair `(q, n)` (`q` prime) with `m = n'` (`p`-free part of `n`), an order table `oF`
(`oF e = ord_e(q)` for `e ∣ m`, verified by `OrdOK`) and a labelling `lab` of `ZMod m`
(represented by `0, …, m-1`), the proposition `Chk q n m oF lab W` states

* `lab (q i) = lab i` for all `i`;
* for every level `d ∣ n` and every `i` with `d ∣ ord_{d' i}(q)` (i.e. the condition of level `d` with
  target `d' i` is essential): `lab (i + N) = lab i` (`N = m/d'`); hence `lab` is constant on the
  fibres of the essential conditions;
* for every label `ℓ`, the total weight `wsum ℓ` of the essential conditions of codimension `≥ 2`
  whose fibres carry the label `ℓ` is at most `W`. Here an essential condition `(d, orbit of x)`
  with `o = ord_x(q)` has `o/d` targets, and each target `x = d' k` (`k < N`) contributes `d/(o q^o)`.

Soundness (`Chk → bound`) is proved in `ExactSound.lean`. The labels are computed by min-propagation
(`labArr`, not trusted: only `Chk` matters), the orders by search (`ordS`, verified by `OrdOK`).
-/

namespace MorganMullen.Exact

open Finset

/-- `n` with all factors `p` removed. -/
def rp (p n : ℕ) : ℕ :=
  if _h : 1 < p ∧ 0 < n ∧ n % p = 0 then rp p (n / p) else n
termination_by n
decreasing_by exact Nat.div_lt_self _h.2.1 _h.1

/-- Candidate for `ord_e(q)`: the least `k ∈ [1, e]` with `q^k ≡ 1 (mod e)` (`0` if none). -/
def ordS (q e : ℕ) : ℕ :=
  match (List.range e).find? (fun k => q ^ (k + 1) % e == 1 % e) with
  | some k => k + 1
  | none => 0

/-- `o = ord_e(q)`, in checkable form. -/
def OrdOK (q e o : ℕ) : Prop :=
  0 < o ∧ q ^ o % e = 1 % e ∧ ∀ k ∈ range o, 0 < k → q ^ k % e ≠ 1 % e

instance (q e o : ℕ) : Decidable (OrdOK q e o) := by unfold OrdOK; infer_instance

/-- The additive order of `x mod m` (`m / gcd(m, x)`). -/
def ordAdd (m x : ℕ) : ℕ := m / Nat.gcd m x

/-- The weight `d / (o q^o)` of one target of an essential condition of level `d`, codimension `o`. -/
def wt (q d o : ℕ) : ℚ := (d : ℚ) / ((o : ℚ) * (q : ℚ) ^ o)

/-- The total weight of the essential conditions of codimension `≥ 2` with label `ℓ`. -/
def wsum (q n m : ℕ) (oF lab : ℕ → ℕ) (ℓ : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, ∑ k ∈ range (m / rp q d),
    if d ∣ oF (ordAdd m (rp q d * k)) ∧ 2 ≤ oF (ordAdd m (rp q d * k)) ∧ lab k = ℓ then
      wt q d (oF (ordAdd m (rp q d * k))) else 0

/-- The check for one pair `(q, n)`. -/
def Chk (q n m : ℕ) (oF lab : ℕ → ℕ) (W : ℚ) : Prop :=
  (∀ e ∈ m.divisors, OrdOK q e (oF e)) ∧
  (∀ i ∈ range m, lab (q * i % m) = lab i) ∧
  (∀ d ∈ n.divisors, ∀ i ∈ range m, d ∣ oF (ordAdd m (rp q d * i)) →
      lab ((i + m / rp q d) % m) = lab i) ∧
  (∀ ℓ ∈ (range m).image lab, wsum q n m oF lab ℓ ≤ W)

instance (q n m : ℕ) (oF lab : ℕ → ℕ) (W : ℚ) : Decidable (Chk q n m oF lab W) := by
  unfold Chk; infer_instance

/-! ### Computing the labels (untrusted) -/

/-- Merge the labels at `i` and `j` (both get the minimum). -/
def merge (a : Array ℕ) (i j : ℕ) : Array ℕ :=
  let v := min a[i]! a[j]!
  (a.set! i v).set! j v

/-- One propagation pass along the edges `{i, q i}` and `{i, i + N}` (essential level `d`). -/
def labStep (q m : ℕ) (oF : ℕ → ℕ) (D : List ℕ) (a : Array ℕ) : Array ℕ :=
  let a := (List.range m).foldl (fun a i => merge a i (q * i % m)) a
  D.foldl (fun a d =>
    let d' := rp q d
    let N := m / d'
    (List.range m).foldl (fun a i =>
      if oF (ordAdd m (d' * i)) % d == 0 then merge a i ((i + N) % m) else a) a) a

/-- Iterate the propagation until it is stable (at most `fuel` passes). -/
def labIter (q m : ℕ) (oF : ℕ → ℕ) (D : List ℕ) : ℕ → Array ℕ → Array ℕ
  | 0, a => a
  | k + 1, a =>
    let b := labStep q m oF D a
    if b == a then a else labIter q m oF D k b

/-- The labels: the least element of the class of `i`. -/
def labArr (q n m : ℕ) (oF : ℕ → ℕ) : Array ℕ :=
  labIter q m oF ((List.range (n + 1)).filter fun d => d != 0 && n % d == 0) (m + 1)
    (Array.range m)

/-- The order table. -/
def ordArr (q m : ℕ) : Array ℕ := Array.ofFn (n := m + 1) fun e => ordS q e.1

/-- The check for `(q, n)` with the computed tables. -/
def caseOK (q n : ℕ) (W : ℚ) : Bool :=
  let m := rp q n
  let oT := ordArr q m
  let oF : ℕ → ℕ := fun e => oT[e]!
  let lT := labArr q n m oF
  let lab : ℕ → ℕ := fun i => lT[i]!
  decide (Chk q n m oF lab W)

theorem caseOK_sound {q n : ℕ} {W : ℚ} (h : caseOK q n W = true) :
    ∃ oF lab : ℕ → ℕ, Chk q n (rp q n) oF lab W := by
  unfold caseOK at h
  exact ⟨_, _, of_decide_eq_true h⟩

/-- All cases of `exact_max_bound`. -/
def allOK : Bool :=
  (List.range 379).all (fun n => n == 0 || !(42 % n == 0 || 378 % n == 0) || caseOK 2 n (3 / 4)) &&
  (List.range 321).all (fun n => n == 0 || !(16 % n == 0 || 320 % n == 0) || caseOK 3 n (4 / 9))

end MorganMullen.Exact
