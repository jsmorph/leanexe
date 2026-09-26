import Project.Drone.ExecutionScanFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

def scanLoopBody : Wasm.Program :=
  match (func14[4]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def scanStepBody : Wasm.Program := scanLoopBody.drop 7

def scanCandidateScratch (r0 r1 owner pointer : UInt64) (target source : Nat)
    (candidate : Choice) (scratch : List Value) : List Value :=
  ((((((((((((((((((scratch.set 55 (.i64 (UInt64.ofNat source))).set 56 (.i64 1)).set 57 (.i64 (UInt64.ofNat source + 1))).set 0 (.i64 (UInt64.ofNat (source + 1)))).set 1 (.i64 r0)).set 2 (.i64 r1)).set 3 (.i64 owner)).set 4 (.i64 pointer)).set 5 (.i64 (UInt64.ofNat target))).set 6 (.i64 r0)).set 7 (.i64 r1)).set 8 (.i64 owner)).set 9 (.i64 pointer)).set 10 (.i64 (UInt64.ofNat target))).set 11 (.i64 (UInt64.ofNat source))).set 14 (.i64 candidate.parent)).set 13 (.i64 candidate.excess)).set 12 (.i64 candidate.time))

def scanCandidateFrame (r0 r1 owner pointer : UInt64) (target fuel source : Nat)
    (incumbent candidate result : Choice) (scratch : List Value) : Locals :=
  { scanFrame r0 r1 owner pointer target (fuel+1) source incumbent result
      (scanCandidateScratch r0 r1 owner pointer target source candidate scratch) with
    values := [.i32 (if candidate.time < incumbent.time then 1 else 0)] }

set_option maxHeartbeats 50000 in
set_option maxRecDepth 32768 in
set_option Elab.async false in
theorem scanPrefix_spec (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 owner pointer : UInt64) (target fuel source : Nat)
    (incumbent candidate result : Choice) (scratch : List Value)
    (hScratch : scratch.length = 58) (hNextIndex : source+1 < UInt64.size)
    (hPred : TerminatesWith env «module» 13 initial
      [.i64 (UInt64.ofNat source), .i64 (UInt64.ofNat target), .i64 pointer,
        .i64 owner, .i64 r1, .i64 r0]
      (fun final values => final = initial ∧ values = choiceValues candidate))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q initial
      (scanCandidateFrame r0 r1 owner pointer target fuel source incumbent candidate result scratch) env) :
    wp «module» ((scanStepBody.take 47) ++ rest) Q initial
      (scanFrame r0 r1 owner pointer target (fuel+1) source incumbent result scratch) env := by
  simp only [scanStepBody, scanLoopBody, func14, List.getElem?_cons_succ,
    List.getElem?_cons_zero, List.drop, List.take, List.cons_append, List.nil_append]
  wp_scan_frame [hScratch]
  refine CheckedNatAdd.guard_spec 72 _ _ _ _ source 1 [] rfl ?_ hNextIndex _ _ ?_
  · simp [Locals.get, hScratch, UInt64.ofNat_add]
  wp_scan_frame [hScratch]
  refine wp_call_tw hPred ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_scan_frame [hScratch, choiceValues, func13Def]
  simpa only [scanCandidateFrame, scanCandidateScratch, scanFrame,
    List.cons_append, List.nil_append] using hNext

#print axioms scanPrefix_spec
end Project.Drone.Execution
