import Project.Drone.ExecutionScanStepTime
import Project.Drone.ExecutionScanStepTie
import Project.Drone.ExecutionScanStepOther

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

set_option maxHeartbeats 500000 in
set_option Elab.async false in
set_option maxRecDepth 32768 in
theorem scanStep_spec (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 owner pointer : UInt64) (target fuel source : Nat)
    (incumbent candidate result : Choice) (scratch : List Value)
    (hScratch : scratch.length = 58) (hNextIndex : source+1 < UInt64.size)
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
  by_cases hTime : candidate.time < incumbent.time
  · exact scanStep_time_lt env initial r0 r1 owner pointer target fuel source
      incumbent candidate result scratch hScratch hNextIndex hTime hPred Q hNext
  · by_cases hEq : candidate.time = incumbent.time
    · exact scanStep_time_eq env initial r0 r1 owner pointer target fuel source
        incumbent candidate result scratch hScratch hNextIndex hTime hEq hPred Q hNext
    · exact scanStep_time_other env initial r0 r1 owner pointer target fuel source
        incumbent candidate result scratch hScratch hNextIndex hTime hEq hPred Q hNext

#print axioms scanStep_spec
end Project.Drone.Execution
