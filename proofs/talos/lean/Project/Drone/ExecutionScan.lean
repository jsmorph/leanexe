import Project.Drone.ExecutionScanEntry
import Project.Drone.ExecutionScanStep

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 32768 in
theorem scanPredecessors_exact (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 owner pointer : UInt64) (target count source : Nat)
    (previous : Array UInt64) (best : Choice)
    (ha : UInt64Array.At initial pointer previous)
    (hRange : 3*(source+count) ≤ previous.size) (ht : target < UInt64.size) :
    TerminatesWith env «module» 14 initial
      (choiceValues best ++ [.i64 (UInt64.ofNat target), .i64 pointer, .i64 owner,
        .i64 r1, .i64 r0, .i64 (UInt64.ofNat source), .i64 (UInt64.ofNat count)])
      (fun final values => final = initial ∧
        values = choiceValues (scanPredecessors count source r0 r1 previous target best)) := by
  have hb : source+count < UInt64.size := by have := ha.size_lt; omega
  have hc : count < UInt64.size := by omega
  apply scanPredecessors_entry env initial r0 r1 owner pointer target count source best
  simp only [func14, List.drop, scanFrame]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := scanInv initial r0 r1 owner pointer target (source+count) previous
      (scanPredecessors count source r0 r1 previous target best)) (μ := scanMeasure)
  · refine ⟨rfl, count, source, best, ⟨0, 0, 0⟩, List.replicate 58 (.i64 0),
      rfl, rfl, rfl, rfl⟩
  · rintro store frame ⟨hStore, f, i, incumbent, result, scratch, rfl, hScratch, hBound, hInv⟩
    subst store
    have hf : f < UInt64.size := by omega
    have hi : i < UInt64.size := by omega
    change wp «module» (FuelGuard.program 0 14 ++ _) _ initial _ env
    refine FuelGuard.program_spec 0 14 _ _ _ _ (UInt64.ofNat f) 0 rfl rfl (by simp [scanFrame, Locals.get, hScratch]) _ _ ?_
    cases f with
    | zero =>
      rw [if_pos (by simp)]
      simp only [scanPredecessors] at hInv
      subst incumbent
      wp_scan_frame [hScratch, func14Def]
      refine wp_iff_cons rfl ?_
      simp
      wp_scan_frame [hScratch, func14Def, choiceValues]
    | succ f =>
      have hFuel : UInt64.ofNat (f+1) ≠ 0 := by
        intro he
        have he' := congrArg UInt64.toNat he
        rw [UInt64.toNat_ofNat_of_lt' hf, UInt64.toNat_zero] at he'
        omega
      have hNext : i+1 < UInt64.size := by omega
      have hRead : 3*i+1 < previous.size := by omega
      rw [if_neg (by simpa only [ne_eq, eq_self_iff_true, not_true_eq_false, or_false] using hFuel)]
      change wp «module» scanStepBody _ initial
        (scanFrame r0 r1 owner pointer target (f+1) i incumbent result scratch) env
      refine scanStep_spec env initial r0 r1 owner pointer target f i incumbent
        (predecessor r0 r1 previous target i) result scratch hScratch hNext
        (predecessor_exact env initial r0 r1 owner pointer target i previous ha hRead ht) _ ?_
      intro nextScratch hLength
      exact scanInv_step hLength hBound hInv rfl hf
#print axioms scanPredecessors_exact
end Project.Drone.Execution
