import Project.Euler2DConservative.GuardOperations

namespace Project.Euler2DConservative.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

macro "energy_checked" call:term "condition" condition:term : tactic => `(tactic|
  (refine wp_call_tw $call ?_
   rintro st values ⟨hst, hvalues⟩
   subst st
   subst values
   cases hcheck : $condition
   case false =>
     guard_peel
     simp_all +zetaDelta [Model.energyGuard, func10Def, boolWord]
   all_goals guard_peel))

theorem energyGuard_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env m 10 initial [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Model.energyGuard rho mx my energy))]) := by
  let top := Model.topExponent rho mx my energy
  let result := Model.energyResidual (Model.normalizedMagnitude rho top)
    (Model.normalizedMagnitude mx top) (Model.normalizedMagnitude my top)
    (Model.normalizedMagnitude energy top)
  refine TerminatesWith.of_wp_entry_for (f := func10Def)
    (by simpa [layout.noImports] using layout.energy) ?_ (by simp [layout.noImports])
  change wp m func10 _ initial (func10Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func10
  wp_run [func10Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  energy_checked (positiveBits_exact layout env initial rho) condition (Model.positiveBits rho)
  energy_checked (finiteBits_exact layout env initial mx) condition (Model.finiteBits mx)
  energy_checked (finiteBits_exact layout env initial my) condition (Model.finiteBits my)
  energy_checked (positiveBits_exact layout env initial energy) condition (Model.positiveBits energy)
  guard_call (topExponent_exact layout env initial rho mx my energy)
  energy_checked (normalizable_exact layout env initial rho top) condition (Model.normalizable rho top)
  energy_checked (normalizable_exact layout env initial mx top) condition (Model.normalizable mx top)
  energy_checked (normalizable_exact layout env initial my top) condition (Model.normalizable my top)
  energy_checked (normalizable_exact layout env initial energy top) condition (Model.normalizable energy top)
  guard_call (normalizedMagnitude_exact layout env initial rho top)
  guard_call (normalizedMagnitude_exact layout env initial mx top)
  guard_call (normalizedMagnitude_exact layout env initial my top)
  guard_call (normalizedMagnitude_exact layout env initial energy top)
  guard_call (energyResidual_exact layout env initial (Model.normalizedMagnitude rho top)
    (Model.normalizedMagnitude mx top) (Model.normalizedMagnitude my top)
    (Model.normalizedMagnitude energy top))
  energy_checked (positiveBits_exact layout env initial result) condition (Model.positiveBits result)
  by_cases hm : (0x3CE0000000000000 : UInt64) < result
  all_goals
    dsimp only [result, top] at hm
    guard_peel
    try rw [if_pos hm]
    try rw [if_neg hm]
    guard_peel
    simp_all +zetaDelta [Model.energyGuard, func10Def, boolWord]

#print axioms energyGuard_exact
end Project.Euler2DConservative.Execution
