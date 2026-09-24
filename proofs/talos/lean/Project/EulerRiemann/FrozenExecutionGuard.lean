import Project.EulerRiemann.FrozenExecutionGuardMomentum
import Project.EulerRiemann.FrozenNumerics

namespace Project.EulerRiemann.Frozen.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Order (positiveBits finiteBits)
open Project.ProofKit.F64Admissibility (normalizable topExponent)
open Project.ProofKit.F64NormalizeTiny (momentumNormalizable)

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

macro "riemann_energy_checked" call:term "condition" test:term : tactic => `(tactic|
  (refine wp_call_tw $call ?_
   rintro st values ⟨hst, hvalues⟩
   subst st
   subst values
   cases hcheck : $test
   case false =>
     guard_peel
     simp_all +zetaDelta [Project.ProofKit.F64AdmissibilityTiny.checked, func19Def, boolWord]
   all_goals guard_peel))

theorem energy_guard_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerRiemann.Frozen.«module» 19 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64AdmissibilityTiny.checked rho mx my energy))]) := by
  let top := topExponent rho mx my energy
  let result := Project.ProofKit.F64AdmissibilityTiny.residual rho mx my energy
  refine TerminatesWith.of_wp_entry_for (f := func19Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.Frozen.«module» func19 _ initial
    (func19Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func19
  wp_run [func19Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  riemann_energy_checked (guard_positive_exact env initial rho) condition (positiveBits rho)
  riemann_energy_checked (guard_finite_exact env initial mx) condition (finiteBits mx)
  riemann_energy_checked (guard_finite_exact env initial my) condition (finiteBits my)
  riemann_energy_checked (guard_positive_exact env initial energy) condition (positiveBits energy)
  guard_call (top_exact env initial rho mx my energy)
  riemann_energy_checked (normalizable_exact env initial rho top) condition (normalizable rho top)
  riemann_energy_checked (momentum_normalizable_exact env initial mx top) condition (momentumNormalizable mx top)
  riemann_energy_checked (momentum_normalizable_exact env initial my top) condition (momentumNormalizable my top)
  riemann_energy_checked (normalizable_exact env initial energy top) condition (normalizable energy top)
  guard_call (tiny_residual_exact env initial rho mx my energy)
  riemann_energy_checked (guard_positive_exact env initial result) condition (positiveBits result)
  by_cases hm : (0x3CE0000000000000 : UInt64) < result
  all_goals
    dsimp only [result] at hm
    guard_peel
    try rw [if_pos hm]
    try rw [if_neg hm]
    simp_all +zetaDelta [Project.ProofKit.F64AdmissibilityTiny.checked]

theorem state_guard_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerRiemann.Frozen.«module» 20 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Numerics.stateGuard rho mx my energy))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func20Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.Frozen.«module» func20 _ initial
    (func20Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func20
  wp_run [func20Def]
  refine wp_call_tw (narrow_exact env initial rho mx my energy) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hn : Project.Euler2DConservative.Model.narrowStateGuard rho mx my energy
  · guard_peel
    refine wp_call_tw (energy_guard_exact env initial rho mx my energy) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases he : Project.ProofKit.F64AdmissibilityTiny.checked rho mx my energy <;> guard_peel <;>
      simp [Numerics.stateGuard, hn, he]
  · guard_peel
    simp [Numerics.stateGuard, hn]

#print axioms energy_guard_exact
#print axioms state_guard_exact
end Project.EulerRiemann.Frozen.Execution
