import Project.EulerOutwardCfl.Arithmetic
import Project.EulerRiemann.OutwardCfl

namespace Project.EulerOutwardCfl.Execution
open Wasm
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.ProofKit.F64Order (positiveBits)
open Project.ProofKit.F64Outward (div mul rejected)
open Project.EulerRiemann.OutwardCfl (ratioChecked)

theorem ratio_exact (env : HostEnv Unit) (initial : Store Unit) (dt spacing alpha : UInt64) :
    TerminatesWith env Project.EulerOutwardCfl.«module» 14 initial
      [.i64 alpha, .i64 spacing, .i64 dt]
      (fun final values => final = initial ∧ values = checkedValues (ratioChecked dt spacing alpha)) := by
  refine TerminatesWith.of_wp_entry_for (f := func14Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardCfl.«module» func14 _ initial
    (func14Def.toLocals [.i64 dt, .i64 spacing, .i64 alpha]) env
  unfold func14
  wp_run [func14Def]
  cases hd : positiveBits dt
  all_goals guard_call (positive_exact env initial dt)
  · guard_call (rejected_exact env initial)
    simp [ratioChecked, hd, checkedValues, rejected]
  · cases hh : positiveBits spacing
    all_goals guard_call (positive_exact env initial spacing)
    · guard_call (rejected_exact env initial)
      simp [ratioChecked, hd, hh, checkedValues, rejected]
    · cases ha : positiveBits alpha
      all_goals guard_call (positive_exact env initial alpha)
      · guard_call (rejected_exact env initial)
        simp [ratioChecked, hd, hh, ha, checkedValues, rejected]
      · outward_call (div_exact env initial true dt spacing)
        by_cases hr : (div true dt spacing).status = 0
        · guard_peel
          outward_call (mul_exact env initial true (div true dt spacing).value alpha)
          by_cases hc : (mul true (div true dt spacing).value alpha).status = 0
          · by_cases hb : (mul true (div true dt spacing).value alpha).value ≤ 0x3FE0000000000000
            · guard_peel
              simp [ratioChecked, hd, hh, ha, hr, hc, hb, checkedValues]
            · guard_peel
              guard_call (rejected_exact env initial)
              simp [ratioChecked, hd, hh, ha, hr, hc, hb, checkedValues, rejected]
          · guard_peel
            guard_call (rejected_exact env initial)
            simp [ratioChecked, hd, hh, ha, hr, hc, checkedValues, rejected]
        · guard_peel
          guard_call (rejected_exact env initial)
          simp [ratioChecked, hd, hh, ha, hr, checkedValues, rejected]

#print axioms ratio_exact
end Project.EulerOutwardCfl.Execution
