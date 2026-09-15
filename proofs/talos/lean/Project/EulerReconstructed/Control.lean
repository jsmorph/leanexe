import Project.EulerReconstructed.Traversal
import Project.EulerRiemann.Control
import Project.EulerRiemann.OutwardMaximum
import Project.EulerRiemann.OutwardMesh

namespace Project.EulerReconstructed.Control
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell initialCells accepted)
open Project.EulerRiemann.Control (Attempt Result)
open Project.EulerReconstructed.Traversal (step)
open Wasm.IEEE64 (add mul)

def retry : Nat → Nat → Nat → UInt64 → UInt64 → UInt64 → Array Cell → Attempt
  | 0, _, _, _, dt, _, _ => ⟨4, dt, #[]⟩
  | fuel + 1, n, trials, time, dt, alpha, grid =>
      if Time.validAdvance time dt then
        let ratio := OutwardCfl.gridRatioChecked n dt alpha
        if ratio.status == 0 then
          let trial := step n trials ratio.value grid
          if accepted trial then ⟨0, dt, trial⟩
          else
            let _ := LeanExe.Runtime.release trial
            retry fuel n trials time (mul 0x3FE0000000000000 dt) alpha grid
        else retry fuel n trials time (mul 0x3FE0000000000000 dt) alpha grid
      else ⟨3, dt, #[]⟩

def advance : Nat → Nat → Nat → UInt64 → Array Cell → Result
  | 0, _, _, time, grid =>
      ⟨if time == Time.endTime then 0 else 5, time, grid⟩
  | fuel + 1, n, trials, time, grid =>
      if time == Time.endTime then ⟨0, time, grid⟩
      else
        let stats := OutwardMaximum.gridUpper grid
        if stats.status == 0 then
          let dt := Time.proposal n time stats.value
          let trial := retry (dt.toNat + 1) n trials time dt stats.value grid
          if trial.status == 0 then
            advance fuel n trials (add time trial.dt) trial.grid
          else ⟨trial.status, time, grid⟩
        else ⟨2, time, grid⟩

def run (n trials : Nat) : Result :=
  if 2 ≤ n ∧ n ≤ 800 then
    advance (Time.endTime.toNat + 1) n trials 0 (initialCells n)
  else ⟨1, 0, #[]⟩

def solve (n trials : Nat) : Array UInt64 :=
  let result := run n trials
  Output.pack n result.time result.status result.grid

end Project.EulerReconstructed.Control
