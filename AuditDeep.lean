import MorganMullen

/-!
# Deeper audit of the trusted base

`Audit.lean` prints the axioms of the main theorem (and of Corollaries 8.8 and 8.9). Two of them, `Lean.ofReduceBool` and
`Lean.trustCompiler`, mean that some closed Boolean terms `c` are evaluated by compiled code
(`Lean.ofReduceBool c true rfl`). This file makes that part of the trusted base visible:

1. it lists every constant `c` that the proof of `MorganMullen.morgan_mullen` evaluates in this way
   (the verified checkers of the paper's computations);
2. it collects every constant those checkers depend on and reports the ones whose compiled code is
   *not* the compiled form of their Lean definition (`@[implemented_by]`, `@[extern]`);
3. it **fails** if any such constant belongs to this project (namespace `MorganMullen`), or if the
   project declares an axiom other than the two cited results.

Constants from Lean core with `@[implemented_by]`/`@[extern]` (GMP arithmetic on `Nat`/`Int`,
arrays, `WellFounded.fix` and the like) are expected: they are what `Lean.trustCompiler` stands for,
exactly as for every proof that uses `native_decide`.

Run with `lake env lean AuditDeep.lean` (a few minutes, after `lake build`).
-/

namespace MorganMullen.AuditDeep

open Lean Meta Elab Command

/-- All constants reachable from `roots` through types and values. -/
partial def reach (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let cs := ci.type.getUsedConstants ++
        (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
      for c in cs do
        if !seen.contains c then stack := c :: stack
  return seen

/-- The constants `c` occurring as `Lean.ofReduceBool c _ _` in `e`. -/
partial def reduceBoolTargets (e : Expr) (acc : Array Name) : Array Name :=
  match e with
  | .app f a =>
    let acc := reduceBoolTargets f (reduceBoolTargets a acc)
    if e.isAppOfArity ``Lean.ofReduceBool 3 then
      match e.getArg! 0 with
      | .const c _ => if acc.contains c then acc else acc.push c
      | _ => acc
    else acc
  | .lam _ t b _ | .forallE _ t b _ => reduceBoolTargets b (reduceBoolTargets t acc)
  | .letE _ t v b _ => reduceBoolTargets b (reduceBoolTargets v (reduceBoolTargets t acc))
  | .mdata _ b | .proj _ _ b => reduceBoolTargets b acc
  | _ => acc

elab "#audit_deep" : command => do
  let env ← getEnv
  let isProj (n : Name) : Bool := (`MorganMullen).isPrefixOf n
  -- 1. the evaluated checkers
  let all := reach env [``MorganMullen.morgan_mullen]
  let mut targets : Array Name := #[]
  for n in all.toList do
    if let some ci := env.find? n then
      if let some v := ci.value? (allowOpaque := true) then
        targets := reduceBoolTargets v targets
  let sorted := targets.qsort (·.toString < ·.toString)
  logInfo m!"constants reachable from morgan_mullen: {all.size}"
  logInfo m!"checkers evaluated by `Lean.ofReduceBool` ({sorted.size}):\n{sorted.toList}"
  -- 2. what the checkers depend on
  let deps := reach env sorted.toList
  let special := deps.toList.filter fun n =>
    (Compiler.implementedByAttr.getParam? env n).isSome || isExtern env n
  let (projSpecial, coreSpecial) := special.partition isProj
  logInfo m!"constants the checkers depend on: {deps.size}, of which {(deps.toList.filter isProj).length} \
    belong to this project"
  logInfo m!"core constants with @[implemented_by]/@[extern] (covered by Lean.trustCompiler): \
    {coreSpecial.length}"
  -- 3. failures
  unless projSpecial.isEmpty do
    throwError m!"project constants with @[implemented_by]/@[extern] used by a checker: {projSpecial}"
  let axs := env.constants.toList.filterMap fun (n, ci) => match ci with
    | .axiomInfo _ => if isProj n then some n else none
    | _ => none
  let expected := [``MorganMullen.garefalakis_kapetanakis, ``MorganMullen.rosser_schoenfeld_psi]
  unless axs.all expected.contains && expected.all axs.contains do
    throwError m!"unexpected axioms declared in the project: {axs}"
  logInfo m!"OK: no project constant used by a checker has @[implemented_by]/@[extern]; the project \
    declares exactly the axioms {expected}"

/-- The checkers evaluated by `Lean.ofReduceBool` in the proofs of `roots`. -/
def checkersOf (env : Environment) (roots : List Name) : Array Name := Id.run do
  let mut targets : Array Name := #[]
  for n in (reach env roots).toList do
    if let some ci := env.find? n then
      if let some v := ci.value? (allowOpaque := true) then
        targets := reduceBoolTargets v targets
  return targets.qsort (·.toString < ·.toString)

/-- Corollary 8.8 (`Sec8Corollary.lean`): its proofs evaluate no checker beyond those of the main
theorem (they enter through Theorem 7.8, `weight_le_Wq`). Fails otherwise. -/
elab "#audit_deep_cor36" : command => do
  let env ← getEnv
  let main := checkersOf env [``MorganMullen.morgan_mullen]
  let cor := checkersOf env [``MorganMullen.hachenberger_lower_bound, ``MorganMullen.hachenberger_eq_iff]
  logInfo m!"checkers evaluated by the proofs of Corollary 8.8 ({cor.size}):\n{cor.toList}"
  unless cor.all main.contains do
    throwError m!"Corollary 8.8 uses checkers not used by the main theorem: {cor.filter (!main.contains ·)}"
  logInfo m!"OK: all of them are among the {main.size} checkers of the main theorem"

/-- Corollary 8.9 (`Sec8PCN.lean`): the first inequality of (a) evaluates no checker; the second inequality
of (a) and (b) evaluate only checkers of the main theorem (Theorem 7.8, and for (b) also Proposition 6.5).
Fails otherwise. -/
elab "#audit_deep_cor37" : command => do
  let env ← getEnv
  let main := checkersOf env [``MorganMullen.morgan_mullen]
  let first := checkersOf env [``MorganMullen.pcn_sub_theta_cn_abs_le]
  unless first.isEmpty do
    throwError m!"the first inequality of Corollary 8.9 (a) evaluates checkers: {first}"
  logInfo m!"checkers evaluated by the proof of pcn_sub_theta_cn_abs_le (Corollary 8.9 (a), first inequality): 0"
  for n in [``MorganMullen.pcn_error_le_star, ``MorganMullen.pcn_ratio_tendsto_one] do
    let cs := checkersOf env [n]
    logInfo m!"checkers evaluated by the proof of {n} ({cs.size}):\n{cs.toList}"
    unless cs.all main.contains do
      throwError m!"{n} uses checkers not used by the main theorem: {cs.filter (!main.contains ·)}"
  logInfo m!"OK: the checkers of Corollary 8.9 are among the {main.size} checkers of the main theorem"

end MorganMullen.AuditDeep

#audit_deep
#print axioms MorganMullen.morgan_mullen
#audit_deep_cor36
#print axioms MorganMullen.hachenberger_lower_bound
#print axioms MorganMullen.hachenberger_eq_iff
#audit_deep_cor37
#print axioms MorganMullen.pcn_sub_theta_cn_abs_le
#print axioms MorganMullen.pcn_error_le_star
#print axioms MorganMullen.pcn_ratio_tendsto_one
