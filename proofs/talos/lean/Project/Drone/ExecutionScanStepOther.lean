import Project.Drone.ExecutionScanStepPrefix

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

set_option maxHeartbeats 500000 in
set_option maxRecDepth 32768 in
set_option Elab.async false in
theorem scanStep_time_other (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 owner pointer : UInt64) (target fuel source : Nat)
    (incumbent candidate result : Choice) (scratch : List Value)
    (hScratch : scratch.length = 58) (hNextIndex : source+1 < UInt64.size)
    (hTime : ¬ candidate.time < incumbent.time)
    (hEq : ¬ candidate.time = incumbent.time)
    (hPred : TerminatesWith env «module» 13 initial
      [.i64 (UInt64.ofNat source), .i64 (UInt64.ofNat target), .i64 pointer,
        .i64 owner, .i64 r1, .i64 r0]
      (fun final values => final = initial ∧ values = choiceValues candidate))
    (Q : Assertion Unit)
    (hNext : ∀ nextScratch : List Value, nextScratch.length = 58 →
      Q (.Break 0 initial (scanFrame r0 r1 owner pointer target fuel (source+1)
        (choose incumbent candidate) result nextScratch))) :
    wp «module» scanStepBody Q initial
      (scanFrame r0 r1 owner pointer target (fuel+1) source incumbent result scratch) env := by
  change wp «module» ((scanStepBody.take 47) ++ (scanLoopBody.drop 54)) Q initial _ env
  apply scanPrefix_spec env initial r0 r1 owner pointer target fuel source
    incumbent candidate result scratch hScratch hNextIndex hPred
  simp only [scanLoopBody, func14, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.drop, scanCandidateFrame, scanCandidateScratch]
  by_cases hOwner : owner = 0
  all_goals
    have hCall := hPred
    try simp only [hOwner] at hCall
    scan_calls hCall [hScratch, choiceValues, func13Def, hTime, hEq, hOwner]
    try subst owner
    try simp only [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, UInt64.add_sub_cancel] at ⊢
    simp only [choose, hTime, hEq, false_or, false_and, ↓reduceIte,
      scanFrame, List.cons_append, List.nil_append, UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl] at hNext
    apply hNext
    simp only [List.length_set, hScratch]

#print axioms scanStep_time_other
end Project.Drone.Execution
