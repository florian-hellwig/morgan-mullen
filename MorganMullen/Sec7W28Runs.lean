import MorganMullen.Sec7W28Defs

/-!
# Theorem 7.8: the computations

Each Boolean check of `Sec7W28Defs.lean` is evaluated by the Lean compiler/interpreter via the
axiom `Lean.ofReduceBool` (tactic `w28_of_reduce_bool`, which works like `of_reduce_bool` in
`Sec8Certificates.lean`).
-/

namespace MorganMullen.W28

open Lean Meta Elab Tactic in
/-- Close a goal `c = true`, `c` a closed constant, by `Lean.ofReduceBool c true rfl`. The same
tactic as `of_reduce_bool` in `Sec8Certificates.lean`, under its own name so that both files can be
imported together. -/
elab "w28_of_reduce_bool" : tactic => liftMetaTactic fun g => do
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "w28_of_reduce_bool: expected an equation `c = true`"
  unless rhs.isConstOf ``Bool.true && lhs.isConst do
    throwError "w28_of_reduce_bool: expected `c = true` with `c` a constant"
  g.assign <| mkApp3 (mkConst ``Lean.ofReduceBool) lhs (mkConst ``Bool.true)
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  return []

theorem run2_ok : run2 = true := by w28_of_reduce_bool
theorem run3_ok : run3 = true := by w28_of_reduce_bool
theorem runExc_ok : runExc = true := by w28_of_reduce_bool
theorem runFixed_ok : runFixed = true := by w28_of_reduce_bool
theorem runBig_ok : runBig = true := by w28_of_reduce_bool

end MorganMullen.W28
