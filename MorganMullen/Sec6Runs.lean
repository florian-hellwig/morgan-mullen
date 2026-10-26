import MorganMullen.Sec6Comp

/-!
# Proposition 6.5: the computations

Each Boolean check of `Sec6Comp.lean` is evaluated by the Lean compiler/interpreter via the axiom
`Lean.ofReduceBool` (tactic `msmall_of_reduce_bool`, which works like `of_reduce_bool` in
`Sec8Certificates.lean`). The ranges and constants are those of the proof of Proposition 6.5:

* `q = 2`: local maxima `R*_a(o)` for `o ≤ 60`, `0 ≤ a ≤ 6`, and `R*_1(90)` (`chkRs2`);
  for `61 ≤ o ≤ 340000`: `f_0(o) ≤ 22/63`, `max_{a ≥ 1} f_a(o) ≤ 12/35` except `(o, a) = (90, 1)`,
  `max_{a ≥ 2} f_a(o) ≤ 121/360`, `max_{a ≥ 3} f_a(o) ≤ 5/16` (`chkQ2`); beyond, the tail bound
  with `κ_4`.
* `q = 3`: `R*_a(o)` for `o ≤ 36`, `0 ≤ a ≤ 4` (`chkRs3`); for `37 ≤ o ≤ 42000`: `f_0(o) ≤ 3/5`,
  `max_{a ≥ 1} f_a(o) ≤ 0.4667` (`chkQ3`); beyond, the tail bound with `κ_3`.
* `q = 4`, `n` even: `max_{a ≥ 1} f_a(o) ≤ 3/4` for `o ≤ 12000` (`chkQ4`); from `o = 10822` on the
  tail bound with `κ_3`.

The factorisations of `q^o - 1` (computed outside Lean) are only checked: the product is compared
with `q^o - 1` and every factor is checked to be prime by trial division (`Nat.minFac`).

Timings (interpreter, one core): `chkQ2` about 1–2 min, the others a few seconds each.
-/

namespace MorganMullen.Msmall

open MorganMullen

open Lean Meta Elab Tactic in
/-- Close a goal `c = true`, `c` a closed constant, by `Lean.ofReduceBool c true rfl`. The same
tactic as `of_reduce_bool` in `Sec8Certificates.lean`, under its own name so that both files can be
imported together. -/
elab "msmall_of_reduce_bool" : tactic => liftMetaTactic fun g => do
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "msmall_of_reduce_bool: expected an equation `c = true`"
  unless rhs.isConstOf ``Bool.true && lhs.isConst do
    throwError "msmall_of_reduce_bool: expected `c = true` with `c` a constant"
  g.assign <| mkApp3 (mkConst ``Lean.ofReduceBool) lhs (mkConst ``Bool.true)
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  return []

/-! ### The classes of the finite ranges -/

/-- `q = 2`: `f_0(o) ≤ 22/63`. -/
def clsQ2A0 : FCls := ⟨2, 0, false, 22, 63, []⟩
/-- `q = 2`: `f_a(o) ≤ 12/35` for all `a ≥ 1`, except `(o, a) = (90, 1)`. -/
def clsQ2A1 : FCls := ⟨2, 1, true, 12, 35, [(90, 1)]⟩
/-- `q = 2`: `f_a(o) ≤ 121/360` for all `a ≥ 2`. -/
def clsQ2A2 : FCls := ⟨2, 2, true, 121, 360, []⟩
/-- `q = 2`: `f_a(o) ≤ 5/16` for all `a ≥ 3`. -/
def clsQ2A3 : FCls := ⟨2, 3, true, 5, 16, []⟩
/-- `q = 3`: `f_0(o) ≤ 3/5`. -/
def clsQ3A0 : FCls := ⟨3, 0, false, 3, 5, []⟩
/-- `q = 3`: `f_a(o) ≤ 0.4667` for all `a ≥ 1`. -/
def clsQ3A1 : FCls := ⟨3, 1, true, 4667, 10000, []⟩
/-- `q = 4`: `f_a(o) ≤ 3/4` for all `a ≥ 1`. -/
def clsQ4A1 : FCls := ⟨2, 1, true, 3, 4, []⟩

/-- `q = 2`, `61 ≤ o ≤ 340000`. -/
def chkQ2 : Bool := allFrom (oOKs [clsQ2A0, clsQ2A1, clsQ2A2, clsQ2A3]) 61 339940
/-- `q = 3`, `37 ≤ o ≤ 42000`. -/
def chkQ3 : Bool := allFrom (oOKs [clsQ3A0, clsQ3A1]) 37 41964
/-- `q = 4`, `1 ≤ o ≤ 12000`. -/
def chkQ4 : Bool := allFrom (oOKs [clsQ4A1]) 1 12000

/-! ### The local maxima `R*_a(o)` -/

/-- Factorisations of `2^o - 1` (`o ≤ 60` and `o = 90`), checked by `rsOKs`. -/
def fac2Tab : List (ℕ × List (ℕ × ℕ)) :=
  [(1, []),
   (2, [(3, 1)]),
   (3, [(7, 1)]),
   (4, [(3, 1), (5, 1)]),
   (5, [(31, 1)]),
   (6, [(3, 2), (7, 1)]),
   (7, [(127, 1)]),
   (8, [(3, 1), (5, 1), (17, 1)]),
   (9, [(7, 1), (73, 1)]),
   (10, [(3, 1), (11, 1), (31, 1)]),
   (11, [(23, 1), (89, 1)]),
   (12, [(3, 2), (5, 1), (7, 1), (13, 1)]),
   (13, [(8191, 1)]),
   (14, [(3, 1), (43, 1), (127, 1)]),
   (15, [(7, 1), (31, 1), (151, 1)]),
   (16, [(3, 1), (5, 1), (17, 1), (257, 1)]),
   (17, [(131071, 1)]),
   (18, [(3, 3), (7, 1), (19, 1), (73, 1)]),
   (19, [(524287, 1)]),
   (20, [(3, 1), (5, 2), (11, 1), (31, 1), (41, 1)]),
   (21, [(7, 2), (127, 1), (337, 1)]),
   (22, [(3, 1), (23, 1), (89, 1), (683, 1)]),
   (23, [(47, 1), (178481, 1)]),
   (24, [(3, 2), (5, 1), (7, 1), (13, 1), (17, 1), (241, 1)]),
   (25, [(31, 1), (601, 1), (1801, 1)]),
   (26, [(3, 1), (2731, 1), (8191, 1)]),
   (27, [(7, 1), (73, 1), (262657, 1)]),
   (28, [(3, 1), (5, 1), (29, 1), (43, 1), (113, 1), (127, 1)]),
   (29, [(233, 1), (1103, 1), (2089, 1)]),
   (30, [(3, 2), (7, 1), (11, 1), (31, 1), (151, 1), (331, 1)]),
   (31, [(2147483647, 1)]),
   (32, [(3, 1), (5, 1), (17, 1), (257, 1), (65537, 1)]),
   (33, [(7, 1), (23, 1), (89, 1), (599479, 1)]),
   (34, [(3, 1), (43691, 1), (131071, 1)]),
   (35, [(31, 1), (71, 1), (127, 1), (122921, 1)]),
   (36, [(3, 3), (5, 1), (7, 1), (13, 1), (19, 1), (37, 1), (73, 1), (109, 1)]),
   (37, [(223, 1), (616318177, 1)]),
   (38, [(3, 1), (174763, 1), (524287, 1)]),
   (39, [(7, 1), (79, 1), (8191, 1), (121369, 1)]),
   (40, [(3, 1), (5, 2), (11, 1), (17, 1), (31, 1), (41, 1), (61681, 1)]),
   (41, [(13367, 1), (164511353, 1)]),
   (42, [(3, 2), (7, 2), (43, 1), (127, 1), (337, 1), (5419, 1)]),
   (43, [(431, 1), (9719, 1), (2099863, 1)]),
   (44, [(3, 1), (5, 1), (23, 1), (89, 1), (397, 1), (683, 1), (2113, 1)]),
   (45, [(7, 1), (31, 1), (73, 1), (151, 1), (631, 1), (23311, 1)]),
   (46, [(3, 1), (47, 1), (178481, 1), (2796203, 1)]),
   (47, [(2351, 1), (4513, 1), (13264529, 1)]),
   (48, [(3, 2), (5, 1), (7, 1), (13, 1), (17, 1), (97, 1), (241, 1), (257, 1), (673, 1)]),
   (49, [(127, 1), (4432676798593, 1)]),
   (50, [(3, 1), (11, 1), (31, 1), (251, 1), (601, 1), (1801, 1), (4051, 1)]),
   (51, [(7, 1), (103, 1), (2143, 1), (11119, 1), (131071, 1)]),
   (52, [(3, 1), (5, 1), (53, 1), (157, 1), (1613, 1), (2731, 1), (8191, 1)]),
   (53, [(6361, 1), (69431, 1), (20394401, 1)]),
   (54, [(3, 4), (7, 1), (19, 1), (73, 1), (87211, 1), (262657, 1)]),
   (55, [(23, 1), (31, 1), (89, 1), (881, 1), (3191, 1), (201961, 1)]),
   (56, [(3, 1), (5, 1), (17, 1), (29, 1), (43, 1), (113, 1), (127, 1), (15790321, 1)]),
   (57, [(7, 1), (32377, 1), (524287, 1), (1212847, 1)]),
   (58, [(3, 1), (59, 1), (233, 1), (1103, 1), (2089, 1), (3033169, 1)]),
   (59, [(179951, 1), (3203431780337, 1)]),
   (60, [(3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (31, 1), (41, 1), (61, 1), (151, 1), (331, 1), (1321, 1)]),
   (90, [(3, 3), (7, 1), (11, 1), (19, 1), (31, 1), (73, 1), (151, 1), (331, 1), (631, 1), (23311, 1), (18837001, 1)])]

/-- Factorisations of `3^o - 1` (`o ≤ 36`), checked by `rsOKs`. -/
def fac3Tab : List (ℕ × List (ℕ × ℕ)) :=
  [(1, [(2, 1)]),
   (2, [(2, 3)]),
   (3, [(2, 1), (13, 1)]),
   (4, [(2, 4), (5, 1)]),
   (5, [(2, 1), (11, 2)]),
   (6, [(2, 3), (7, 1), (13, 1)]),
   (7, [(2, 1), (1093, 1)]),
   (8, [(2, 5), (5, 1), (41, 1)]),
   (9, [(2, 1), (13, 1), (757, 1)]),
   (10, [(2, 3), (11, 2), (61, 1)]),
   (11, [(2, 1), (23, 1), (3851, 1)]),
   (12, [(2, 4), (5, 1), (7, 1), (13, 1), (73, 1)]),
   (13, [(2, 1), (797161, 1)]),
   (14, [(2, 3), (547, 1), (1093, 1)]),
   (15, [(2, 1), (11, 2), (13, 1), (4561, 1)]),
   (16, [(2, 6), (5, 1), (17, 1), (41, 1), (193, 1)]),
   (17, [(2, 1), (1871, 1), (34511, 1)]),
   (18, [(2, 3), (7, 1), (13, 1), (19, 1), (37, 1), (757, 1)]),
   (19, [(2, 1), (1597, 1), (363889, 1)]),
   (20, [(2, 4), (5, 2), (11, 2), (61, 1), (1181, 1)]),
   (21, [(2, 1), (13, 1), (1093, 1), (368089, 1)]),
   (22, [(2, 3), (23, 1), (67, 1), (661, 1), (3851, 1)]),
   (23, [(2, 1), (47, 1), (1001523179, 1)]),
   (24, [(2, 5), (5, 1), (7, 1), (13, 1), (41, 1), (73, 1), (6481, 1)]),
   (25, [(2, 1), (11, 2), (8951, 1), (391151, 1)]),
   (26, [(2, 3), (398581, 1), (797161, 1)]),
   (27, [(2, 1), (13, 1), (109, 1), (433, 1), (757, 1), (8209, 1)]),
   (28, [(2, 4), (5, 1), (29, 1), (547, 1), (1093, 1), (16493, 1)]),
   (29, [(2, 1), (59, 1), (28537, 1), (20381027, 1)]),
   (30, [(2, 3), (7, 1), (11, 2), (13, 1), (31, 1), (61, 1), (271, 1), (4561, 1)]),
   (31, [(2, 1), (683, 1), (102673, 1), (4404047, 1)]),
   (32, [(2, 7), (5, 1), (17, 1), (41, 1), (193, 1), (21523361, 1)]),
   (33, [(2, 1), (13, 1), (23, 1), (3851, 1), (2413941289, 1)]),
   (34, [(2, 3), (103, 1), (307, 1), (1021, 1), (1871, 1), (34511, 1)]),
   (35, [(2, 1), (11, 2), (71, 1), (1093, 1), (2664097031, 1)]),
   (36, [(2, 4), (5, 1), (7, 1), (13, 1), (19, 1), (37, 1), (73, 1), (757, 1), (530713, 1)])]

/-- The factorisation of `2^o - 1` from the table. -/
def fac2 (o : ℕ) : List (ℕ × ℕ) := (fac2Tab.lookup o).getD []

/-- The factorisation of `3^o - 1` from the table. -/
def fac3 (o : ℕ) : List (ℕ × ℕ) := (fac3Tab.lookup o).getD []

/-- The bounds for `R*_a(o)`, `q = 2`, `o ≤ 60`: `R*_0(o) ≤ 2/5` for `o ∉ {1,2,3,6}`;
`R*_1(o) ≤ 3/8` for `o ∉ {1,2,6}` and `≤ 3/4` for `o ∈ {1,2,6}`; `R*_2(o) ≤ 3/8` for `o ≠ 4` and
`R*_2(4) ≤ 7/16`; `R*_a(o) ≤ 15/64` for `3 ≤ a ≤ 6`. -/
def as2 (o : ℕ) : List (ℕ × ℚ) :=
  (if o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 6 then [] else [(0, 2 / 5)]) ++
  [(1, if o = 1 ∨ o = 2 ∨ o = 6 then 3 / 4 else 3 / 8), (2, if o = 4 then 7 / 16 else 3 / 8),
   (3, 15 / 64), (4, 15 / 64), (5, 15 / 64), (6, 15 / 64)]

/-- The bounds for `R*_a(o)`, `q = 3`, `o ≤ 36`: `R*_0(o) ≤ 7/16` for `o ∉ {1,2,4,8}`;
`R*_a(o) ≤ 4/9` for `1 ≤ a ≤ 4`. -/
def as3 (o : ℕ) : List (ℕ × ℚ) :=
  (if o = 1 ∨ o = 2 ∨ o = 4 ∨ o = 8 then [] else [(0, 7 / 16)]) ++
  [(1, 4 / 9), (2, 4 / 9), (3, 4 / 9), (4, 4 / 9)]

/-- `q = 2`: all `o ≤ 60`, and `R*_1(90) ≤ 2/15`. -/
def chkRs2 : Bool :=
  (List.range' 1 60).all (fun o => rsOKs 2 2 o (as2 o) (fac2 o)) && rsOKs 2 2 90 [(1, 2 / 15)] (fac2 90)

/-- `q = 3`: all `o ≤ 36`. -/
def chkRs3 : Bool := (List.range' 1 36).all fun o => rsOKs 3 3 o (as3 o) (fac3 o)

/-! ### The computations (computer-assisted) -/

theorem chkQ2_ok : chkQ2 = true := by msmall_of_reduce_bool
theorem chkQ3_ok : chkQ3 = true := by msmall_of_reduce_bool
theorem chkQ4_ok : chkQ4 = true := by msmall_of_reduce_bool
theorem chkRs2_ok : chkRs2 = true := by msmall_of_reduce_bool
theorem chkRs3_ok : chkRs3 = true := by msmall_of_reduce_bool

/-! ### Consequences: the bounds used in the proof of Proposition 6.5 -/

theorem fQ2A0 : ∀ o, 61 ≤ o → o ≤ 340000 → faX 2 0 o ≤ 22 / 63 := by
  intro o h1 h2
  have := range_bound _ (c := clsQ2A0) (by simp) Nat.prime_two (by decide) chkQ2_ok o (by omega)
    h1 (by omega) 0 (Or.inr ⟨rfl, rfl⟩) (by simp [clsQ2A0])
  simpa [clsQ2A0] using this

theorem fQ2A1 : ∀ o, 61 ≤ o → o ≤ 340000 → ∀ a, 1 ≤ a → (o, a) ≠ (90, 1) →
    faX 2 a o ≤ 12 / 35 := by
  intro o h1 h2 a ha hne
  have := range_bound _ (c := clsQ2A1) (by simp) Nat.prime_two (by decide) chkQ2_ok o (by omega)
    h1 (by omega) a (Or.inl ⟨rfl, ha⟩) (by simpa [clsQ2A1] using hne)
  simpa [clsQ2A1] using this

theorem fQ2A2 : ∀ o, 61 ≤ o → o ≤ 340000 → ∀ a, 2 ≤ a → faX 2 a o ≤ 121 / 360 := by
  intro o h1 h2 a ha
  have := range_bound _ (c := clsQ2A2) (by simp) Nat.prime_two (by decide) chkQ2_ok o (by omega)
    h1 (by omega) a (Or.inl ⟨rfl, ha⟩) (by simp [clsQ2A2])
  simpa [clsQ2A2] using this

theorem fQ2A3 : ∀ o, 61 ≤ o → o ≤ 340000 → ∀ a, 3 ≤ a → faX 2 a o ≤ 5 / 16 := by
  intro o h1 h2 a ha
  have := range_bound _ (c := clsQ2A3) (by simp) Nat.prime_two (by decide) chkQ2_ok o (by omega)
    h1 (by omega) a (Or.inl ⟨rfl, ha⟩) (by simp [clsQ2A3])
  simpa [clsQ2A3] using this

/-- `q = 2`, `o > 340000`: `f_a(o) ≤ κ_4 o^{-1/4} < 0.35`. -/
theorem fQ2tail : ∀ o, 340000 < o → ∀ a, faX 2 a o ≤ 7 / 20 := fun o ho a =>
  faX_le_of_kappa4 (by norm_num) a (7 / 20) 340001 (by norm_num) (by norm_num) ho (by omega)

theorem fQ3A0 : ∀ o, 37 ≤ o → o ≤ 42000 → faX 3 0 o ≤ 3 / 5 := by
  intro o h1 h2
  have := range_bound _ (c := clsQ3A0) (by simp) Nat.prime_three (by decide) chkQ3_ok o
    (by omega) h1 (by omega) 0 (Or.inr ⟨rfl, rfl⟩) (by simp [clsQ3A0])
  simpa [clsQ3A0] using this

theorem fQ3A1 : ∀ o, 37 ≤ o → o ≤ 42000 → ∀ a, 1 ≤ a → faX 3 a o ≤ 4667 / 10000 := by
  intro o h1 h2 a ha
  have := range_bound _ (c := clsQ3A1) (by simp) Nat.prime_three (by decide) chkQ3_ok o
    (by omega) h1 (by omega) a (Or.inl ⟨rfl, ha⟩) (by simp [clsQ3A1])
  simpa [clsQ3A1] using this

/-- `q = 3`, `o > 42000`: `f_a(o) ≤ κ_3 o^{-1/6} < 0.5983`. -/
theorem fQ3tail : ∀ o, 42000 < o → ∀ a, faX 3 a o ≤ 5983 / 10000 := fun o ho a =>
  faX_le_of_kappa3 (by norm_num) a (5983 / 10000) 42001 (by norm_num) (by norm_num) ho (by omega)

/-- `q = 4`, `n` even: `max_{a ≥ 1} f_a(o) ≤ 3/4` for all `o` (exact evaluation for `o ≤ 12000`,
the tail bound `κ_3 o^{-1/6} ≤ 3/4` for `o ≥ 10822`). -/
theorem fQ4A1 : ∀ o, 0 < o → ∀ a, 1 ≤ a → faX 2 a o ≤ 3 / 4 := by
  intro o ho a ha
  rcases le_or_gt o 12000 with h | h
  · have := range_bound _ (c := clsQ4A1) (by simp) Nat.prime_two (by decide) chkQ4_ok o ho
      (by omega) (by omega) a (Or.inl ⟨rfl, ha⟩) (by simp [clsQ4A1])
    simpa [clsQ4A1] using this
  · exact faX_le_of_kappa3 (by norm_num) a (3 / 4) 10822 (by norm_num) (by norm_num) (by omega)
      (by omega)

lemma rs2_of_mem {o : ℕ} (h1 : 1 ≤ o) (h2 : o ≤ 60) {a : ℕ} {ϑ : ℚ} (hmem : (a, ϑ) ∈ as2 o) :
    RaStarX 2 2 a o ≤ ϑ := by
  have h := chkRs2_ok
  simp only [chkRs2, Bool.and_eq_true, List.all_eq_true, List.mem_range'_1] at h
  exact rsOKs_sound Nat.prime_two (h.1 o ⟨h1, by omega⟩) hmem

theorem rsQ2_90 : RaStarX 2 2 1 90 ≤ 2 / 15 := by
  have h := chkRs2_ok
  simp only [chkRs2, Bool.and_eq_true] at h
  exact rsOKs_sound Nat.prime_two h.2 (by simp)

lemma rs3_of_mem {o : ℕ} (h1 : 1 ≤ o) (h2 : o ≤ 36) {a : ℕ} {ϑ : ℚ} (hmem : (a, ϑ) ∈ as3 o) :
    RaStarX 3 3 a o ≤ ϑ := by
  have h := chkRs3_ok
  simp only [chkRs3, List.all_eq_true, List.mem_range'_1] at h
  exact rsOKs_sound Nat.prime_three (h o ⟨h1, by omega⟩) hmem

lemma factorization_le_of_le {p o B : ℕ} (hp : 1 < p) (ho : o ≠ 0) (hB : o < p ^ (B + 1)) :
    o.factorization p ≤ B := by
  by_contra hc
  push Not at hc
  have h1 : p ^ o.factorization p ≤ o := Nat.ordProj_le p ho
  have h2 : p ^ (B + 1) ≤ p ^ o.factorization p := Nat.pow_le_pow_right (by omega) hc
  omega

theorem rsQ2A0 : ∀ o, 1 ≤ o → o ≤ 60 → ¬ (o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 6) →
    RaStarX 2 2 0 o ≤ 2 / 5 :=
  fun o h1 h2 hT => rs2_of_mem h1 h2 (by simp [as2, hT])

theorem rsQ2A1 : ∀ o, 1 ≤ o → o ≤ 60 →
    RaStarX 2 2 1 o ≤ if o = 1 ∨ o = 2 ∨ o = 6 then 3 / 4 else 3 / 8 :=
  fun o h1 h2 => rs2_of_mem h1 h2 (by simp [as2])

theorem rsQ2A2 : ∀ o, 1 ≤ o → o ≤ 60 → RaStarX 2 2 2 o ≤ if o = 4 then 7 / 16 else 3 / 8 :=
  fun o h1 h2 => rs2_of_mem h1 h2 (by simp [as2])

theorem rsQ2A3 : ∀ o, 1 ≤ o → o ≤ 60 → ∀ a, 3 ≤ a → RaStarX 2 2 a o ≤ 15 / 64 := by
  intro o h1 h2 a ha
  rcases le_or_gt a 6 with h6 | h6
  · exact rs2_of_mem h1 h2 (by interval_cases a <;> simp [as2])
  · have hv : o.factorization 2 ≤ 6 :=
      factorization_le_of_le (by norm_num) (by omega) (by calc o ≤ 60 := h2
        _ < 2 ^ (6 + 1) := by norm_num)
    exact (RaStarX_anti (by norm_num) (by omega) hv a h6.le).trans
      (rs2_of_mem h1 h2 (by simp [as2]))

theorem rsQ3A0 : ∀ o, 1 ≤ o → o ≤ 36 → ¬ (o = 1 ∨ o = 2 ∨ o = 4 ∨ o = 8) →
    RaStarX 3 3 0 o ≤ 7 / 16 :=
  fun o h1 h2 hT => rs3_of_mem h1 h2 (by simp [as3, hT])

theorem rsQ3A1 : ∀ o, 1 ≤ o → o ≤ 36 → ∀ a, 1 ≤ a → RaStarX 3 3 a o ≤ 4 / 9 := by
  intro o h1 h2 a ha
  rcases le_or_gt a 4 with h4 | h4
  · exact rs3_of_mem h1 h2 (by interval_cases a <;> simp [as3])
  · have hv : o.factorization 3 ≤ 4 :=
      factorization_le_of_le (by norm_num) (by omega) (by calc o ≤ 36 := h2
        _ < 3 ^ (4 + 1) := by norm_num)
    exact (RaStarX_anti (by norm_num) (by omega) hv a h4.le).trans
      (rs3_of_mem h1 h2 (by simp [as3]))

end MorganMullen.Msmall
