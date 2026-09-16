import Project.EulerCertificate.Boundary
import Project.EulerReconstructed.Control

namespace Project.EulerCertificate.Control
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell accepted)
open Project.EulerReconstructed.Traversal (sweep)
open Project.EulerCertificate.Flux (Vector)
open Wasm.IEEE64 (add mul)

structure Trial where
  grid : Array Cell
  boundary : Vector

structure Attempt where
  status : UInt64
  dt : UInt64
  grid : Array Cell
  boundary : Vector

structure Result where
  status : UInt64
  time : UInt64
  grid : Array Cell
  boundary : Vector

def attempt (n trials : Nat) (dt ratio : UInt64) (grid : Array Cell) : Option Trial :=
  let middle := sweep n trials false ratio grid
  if accepted middle then
    let next := sweep n trials true ratio middle
    if accepted next then
      let boundary := Boundary.physicalStep n trials dt grid middle
      let _ := LeanExe.Runtime.release middle
      some ⟨next, boundary⟩
    else
      let _ := LeanExe.Runtime.release middle
      let _ := LeanExe.Runtime.release next
      none
  else
    let _ := LeanExe.Runtime.release middle
    none

def retry : Nat → Nat → Nat → UInt64 → UInt64 → UInt64 → Array Cell → Attempt
  | 0, _, _, _, dt, _, _ => ⟨4, dt, #[], Vectors.zero⟩
  | fuel + 1, n, trials, time, dt, alpha, grid =>
      if Time.validAdvance time dt then
        let ratio := OutwardCfl.gridRatioChecked n dt alpha
        if ratio.status == 0 then
          match attempt n trials dt ratio.value grid with
          | some trial => ⟨0, dt, trial.grid, trial.boundary⟩
          | none => retry fuel n trials time (mul 0x3FE0000000000000 dt) alpha grid
        else retry fuel n trials time (mul 0x3FE0000000000000 dt) alpha grid
      else ⟨3, dt, #[], Vectors.zero⟩

def advance : Nat → Nat → Nat → UInt64 → Array Cell → Vector → Result
  | 0, _, _, time, grid, boundary =>
      ⟨if time == Time.endTime then 0 else 5, time, grid, boundary⟩
  | fuel + 1, n, trials, time, grid, boundary =>
      if time == Time.endTime then ⟨0, time, grid, boundary⟩
      else
        let stats := OutwardMaximum.gridUpper grid
        if stats.status == 0 then
          let dt := Time.proposal n time stats.value
          let trial := retry (dt.toNat + 1) n trials time dt stats.value grid
          if trial.status == 0 then
            let total := Vectors.add boundary trial.boundary
            advance fuel n trials (add time trial.dt) trial.grid total
          else ⟨trial.status, time, grid, boundary⟩
        else ⟨2, time, grid, boundary⟩

end Project.EulerCertificate.Control
