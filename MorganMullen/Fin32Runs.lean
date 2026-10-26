import MorganMullen.Fin32Comp
import MorganMullen.Sec8Certificates

/-!
# Proposition 8.4: the computations

Each Boolean block check of `Fin32Comp.lean` is evaluated by the Lean compiler/interpreter via the
axiom `Lean.ofReduceBool` (tactic `of_reduce_bool` of `Sec8Certificates.lean`).
Timings (interpreter, one core): `blk3` ≈ 55 s, `blk5` ≈ 22 s, `blk2` ≈ 9 s, the others < 1 s.
-/

namespace MorganMullen.Fin32

theorem blk2_ok : blk2 = true := by of_reduce_bool
theorem blk3_ok : blk3 = true := by of_reduce_bool
theorem blk4_ok : blk4 = true := by of_reduce_bool
theorem blk5_ok : blk5 = true := by of_reduce_bool
theorem blk7_ok : blk7 = true := by of_reduce_bool
theorem blk8_ok : blk8 = true := by of_reduce_bool
theorem blk9_ok : blk9 = true := by of_reduce_bool
theorem blk11_ok : blk11 = true := by of_reduce_bool
theorem blk13_ok : blk13 = true := by of_reduce_bool
theorem blk16_ok : blk16 = true := by of_reduce_bool
theorem blk17_ok : blk17 = true := by of_reduce_bool
theorem blk19_ok : blk19 = true := by of_reduce_bool

end MorganMullen.Fin32
