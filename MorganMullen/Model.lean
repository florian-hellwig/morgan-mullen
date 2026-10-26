import MorganMullen.NT
import Mathlib.Logic.Relation
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Field

/-!
# The combinatorial model of the conditions (Definitions 2.2, 2.4, 3.1 of the paper)

Fix `q` (a power of the prime `p = minFac q`) and `n ≥ 1`, `n = p^a n'` with `p ∤ n'`.
A primitive `n'`-th root of unity `ζ` identifies `μ_{n'}` with `ZMod n'` via `i ↦ ζ^i`;
all combinatorial objects of the paper are therefore described inside `ZMod n'`:

* a *pair* is `(i, u) ∈ ZMod n' × ZMod p^a` (the paper's `(η, u)` with `η = ζ^i`);
  the *pair orbits* are the orbits of `(i, u) ↦ (q i, u + 1)`;
* a *condition* of level `d ∣ n` (`d = p^c d'`, `N = n'/d'`) has a *target* `x ∈ ZMod n'` with
  `N x = 0` (the paper's `ζ^{d'k}`, `x = d' k`); the conditions `(d, x)` and `(d, q^d x)` are
  identified, so a condition is the pair `(d, orbit of x under x ↦ q^d x)`;
* its *fibre* is `{i : d' i = x}` (for the targets `x` of the orbit), its *pairs* are
  `fibre × {u : p^c ∣ u}`;
* `e = addOrderOf x` (the order of `ζ^x`) and `o = ord_e(q)` (called `codim` below: by Theorem 2.5 the
  codimension of the kernel `V_C` is `lcm(d, o)`, which equals `o` exactly when `C` is essential), and the
  condition is *essential* if `d ∣ ord_e(q)`.

The fibre sums `C_{d,k}(w)` themselves (which need the field `E`) are in `Sec2Coordinates.lean`.
-/

namespace MorganMullen
namespace Model

open Finset

variable (q n : ℕ)

/-- the characteristic `p` of `q` -/
abbrev chr : ℕ := charOf q

/-- `a = v_p(n)` -/
def a : ℕ := n.factorization (chr q)

/-- `n' = n / p^a`, the `p`-free part of `n` -/
def nfree : ℕ := pfree (chr q) n

/-- `p^a` -/
def pa : ℕ := chr q ^ a q n

/-- `d'`, the `p`-free part of the level `d` -/
def dfree (d : ℕ) : ℕ := pfree (chr q) d

/-- `c = v_p(d)` -/
def dval (d : ℕ) : ℕ := d.factorization (chr q)

/-- `N = n'/d'` -/
def bigN (d : ℕ) : ℕ := nfree q n / dfree q d

lemma chr_pos : 0 < chr q := Nat.minFac_pos q

instance pa_neZero : NeZero (pa q n) := ⟨(pow_pos (chr_pos q) _).ne'⟩

instance nfree_neZero [NeZero n] : NeZero (nfree q n) :=
  ⟨(Nat.ordCompl_pos (chr q) (NeZero.ne n)).ne'⟩

section Conditions

variable [NeZero n]

/-- The possible targets of level `d`: the `x ∈ ZMod n'` with `N x = 0`
(i.e. `ζ^x ∈ μ_N`, equivalently `x ∈ d' · ZMod n'`). -/
def targets (d : ℕ) : Finset (ZMod (nfree q n)) :=
  univ.filter fun x => ((bigN q n d : ℕ) : ZMod (nfree q n)) * x = 0

/-- The orbit of the target `x` under `x ↦ q^d x` (identification `(d,k) ∼ (d, q^d k)`). -/
def orbit (d : ℕ) (x : ZMod (nfree q n)) : Finset (ZMod (nfree q n)) :=
  (range (nfree q n)).image fun j => ((q : ZMod (nfree q n)) ^ d) ^ j * x

/-- A condition: its level `d` and the orbit of its targets. -/
abbrev Cond : Type := ℕ × Finset (ZMod (nfree q n))

/-- The set of all conditions `(d, k)`, `d ∣ n`, `k ∈ ℤ/N`, up to `(d,k) ∼ (d, q^d k)`. -/
def conds : Finset (Cond q n) :=
  n.divisors.biUnion fun d => (targets q n d).image fun x => (d, orbit q n d x)

/-- The number `ord_e(q)` attached to a target `x` (`e = ` order of `ζ^x`); it is the codimension of
the kernel of an essential condition with target `x` (Theorem 2.5). -/
noncomputable def tcodim (x : ZMod (nfree q n)) : ℕ := ordMod q (addOrderOf x)

/-- The order `e` of the targets of a condition (all targets of an orbit have the same order). -/
noncomputable def tord (C : Cond q n) : ℕ := C.2.sup addOrderOf

/-- `o(C) = ord_e(q)` for a condition `C` (the codimension of `V_C` if `C` is essential, Theorem 2.5;
in general that codimension is `lcm(d, o(C))`). -/
noncomputable def codim (C : Cond q n) : ℕ := C.2.sup (tcodim q n)

/-- A condition of level `d` is *essential* if `d ∣ o(C)`. -/
def IsEssential (C : Cond q n) : Prop := C.1 ∣ codim q n C

open Classical in
/-- The set of essential conditions. -/
noncomputable def essConds : Finset (Cond q n) := (conds q n).filter (IsEssential q n)

/-- `M`, the number of essential conditions. -/
noncomputable def numM : ℕ := (essConds q n).card

/-- The *weight* `∑ q^{-o(C)}` of a set of conditions. -/
noncomputable def weight (K : Finset (Cond q n)) : ℚ := ∑ C ∈ K, ((q : ℚ) ^ codim q n C)⁻¹

open Classical in
/-- `S`, the total weight of the essential conditions of codimension `≥ 2`. -/
noncomputable def sumS : ℚ := weight q n ((essConds q n).filter fun C => 2 ≤ codim q n C)

/-- The fibre of a condition: all `i ∈ ZMod n'` (i.e. `η = ζ^i`) with `d' i` a target of the
condition. (For a single target `x` the fibre is `{i : d' i = x}`; taking the union over the orbit
does not change the set of pair orbits met, see the paragraph after Definition 2.4.) -/
def fibre (C : Cond q n) : Finset (ZMod (nfree q n)) :=
  univ.filter fun i => ((dfree q C.1 : ℕ) : ZMod (nfree q n)) * i ∈ C.2

/-- `p^c ℤ/p^a ℤ ⊆ ℤ/p^a`, the residues `u` occurring at level `d = p^c d'`. -/
def resSet (d : ℕ) : Finset (ZMod (pa q n)) :=
  univ.filter fun u => chr q ^ dval q d ∣ u.val

/-- The pairs `(η, u)` of a condition. -/
def pairs (C : Cond q n) : Finset (ZMod (nfree q n) × ZMod (pa q n)) :=
  fibre q n C ×ˢ resSet q n C.1

/-- `π'` lies in the pair orbit of `π` (orbits of `(i, u) ↦ (q i, u + 1)`). -/
def PairRel (π π' : ZMod (nfree q n) × ZMod (pa q n)) : Prop :=
  ∃ j : ℕ, π'.1 = (q : ZMod (nfree q n)) ^ j * π.1 ∧ π'.2 = π.2 + (j : ZMod (pa q n))

/-- `η'` lies in the `q`-orbit of `η` (`η' = η^{q^j}`). -/
def QRel (i i' : ZMod (nfree q n)) : Prop := ∃ j : ℕ, i' = (q : ZMod (nfree q n)) ^ j * i

/-- Two conditions are *adjacent* if their supports share a pair orbit (Definition 3.1). -/
def Adj (C C' : Cond q n) : Prop :=
  ∃ π ∈ pairs q n C, ∃ π' ∈ pairs q n C', PairRel q n π π'

/-- Two conditions of a set `ℰ` of conditions lie in the same *component* of `ℰ` (equivalence relation
generated by adjacency inside `ℰ`, Definition 3.1, for an arbitrary set `ℰ`; the paper uses `ℰ` = all
essential conditions). -/
def SameComp (ℰ : Finset (Cond q n)) : Cond q n → Cond q n → Prop :=
  Relation.EqvGen fun C C' => C ∈ ℰ ∧ C' ∈ ℰ ∧ Adj q n C C'

open Classical in
/-- The component of `C` in `ℰ`. -/
noncomputable def component (ℰ : Finset (Cond q n)) (C : Cond q n) : Finset (Cond q n) :=
  ℰ.filter (SameComp q n ℰ C)

/-- The set of components of `ℰ`. -/
noncomputable def components (ℰ : Finset (Cond q n)) : Finset (Finset (Cond q n)) :=
  ℰ.image (component q n ℰ)

/-- `o₀` is the minimal codimension of the set of conditions `𝒞`. -/
def IsMinCodim (𝒞 : Finset (Cond q n)) (o₀ : ℕ) : Prop :=
  (∃ C ∈ 𝒞, codim q n C = o₀) ∧ ∀ C ∈ 𝒞, o₀ ≤ codim q n C

/-- `D_𝒞`: the least common multiple of the `p`-free parts `d'` of the levels in `𝒞`. -/
def levelLcm (𝒞 : Finset (Cond q n)) : ℕ := 𝒞.lcm fun C => dfree q C.1

/-- The permutation `(i, u) ↦ (q i, u + 1)` whose orbits are the pair orbits. -/
def pairStep (π : ZMod (nfree q n) × ZMod (pa q n)) : ZMod (nfree q n) × ZMod (pa q n) :=
  ((q : ZMod (nfree q n)) * π.1, π.2 + 1)

/-- The size `|π|` of the pair orbit of `π`. -/
noncomputable def pairPeriod (π : ZMod (nfree q n) × ZMod (pa q n)) : ℕ :=
  Function.minimalPeriod (pairStep q n) π

/-- `R` is a system of representatives of the pair orbits. -/
def IsPairOrbitReps (R : Finset (ZMod (nfree q n) × ZMod (pa q n))) : Prop :=
  ∀ π, ∃! r, r ∈ R ∧ PairRel q n r π

end Conditions

/-- The essential *types* `(d, e)`: `d ∣ n`, `e ∣ n'/d'`, `d ∣ ord_e(q)` (Lemma 5.2). -/
noncomputable def essTypes : Finset (ℕ × ℕ) := by
  classical
  exact (n.divisors ×ˢ (nfree q n).divisors).filter fun de =>
    de.2 ∣ bigN q n de.1 ∧ de.1 ∣ ordMod q de.2

/-- `ν_{d,e} = d φ(e) / ord_e(q)`, the number of essential conditions of type `(d, e)`. -/
noncomputable def nu (d e : ℕ) : ℕ := d * Nat.totient e / ordMod q e

end Model
end MorganMullen
