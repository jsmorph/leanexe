import Project.Beck.ExecutionScalar
import Project.ProofKit.CheckedArrayGet

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

theorem frozen_exact (env : HostEnv Unit) (initial : Store Unit) (point : Point)
    (owner pointer : UInt64) (job : Nat) (array : UInt64Array.At initial pointer point.numerators)
    (bounded : job < point.numerators.size) :
    TerminatesWith env «module» 12 initial (.i64 job.toUInt64 :: pointValues point owner pointer)
      (fun final values => final = initial ∧ values = [.i64 (boolWord (frozen point job))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func12Def) rfl ?_
  change wp «module» func12 _ initial
    { params := [.i64 point.denominator, .i64 owner, .i64 pointer, .i64 job.toUInt64],
      locals := List.replicate 5 (.i64 0) } env
  unfold func12
  simp only [List.replicate]
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  change wp «module» (CheckedArrayGet.checkedGetCore 7 8 ++ _) _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 7 8 _ _ _ _ pointer point.numerators job []
    rfl rfl rfl array bounded _ _ ?_
  wp_fixed_frame
  refine wp_call_tw (magnitude_exact env initial point.numerators[job]) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  by_cases h : magnitude point.numerators[job] = point.denominator
  · simp [h]
    wp_fixed_frame [func12Def, boolWord, frozen, getElem!_pos point.numerators job bounded, h]
    simp [pointValues]
  · simp [h]
    wp_fixed_frame [func12Def, boolWord, frozen, getElem!_pos point.numerators job bounded, h]
    simp [pointValues, h]

#print axioms frozen_exact

end Project.Beck.Execution
