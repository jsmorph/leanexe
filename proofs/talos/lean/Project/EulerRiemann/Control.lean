import Project.EulerRiemann.Time
import Project.EulerRiemann.Output

namespace Project.EulerRiemann.Control
open Traversal
open Wasm.IEEE64 (add mul div)

structure Attempt where
  status : UInt64
  dt : UInt64
  grid : Array Cell

def retry : Nat → Nat → UInt64 → UInt64 → Array Cell → Attempt
  | 0, _, _, dt, _ => ⟨4, dt, #[]⟩
  | fuel + 1, n, time, dt, grid =>
      if Time.validAdvance time dt then
        let trial := step n (div dt (Time.spacing n)) grid
        if accepted trial then ⟨0, dt, trial⟩
        else
          let _ := LeanExe.Runtime.release trial
          retry fuel n time (mul 0x3FE0000000000000 dt) grid
      else ⟨3, dt, #[]⟩

structure Result where
  status : UInt64
  time : UInt64
  grid : Array Cell

def advance : Nat → Nat → UInt64 → Array Cell → Result
  | 0, _, time, grid =>
      ⟨if time == Time.endTime then 0 else 5, time, grid⟩
  | fuel + 1, n, time, grid =>
      if time == Time.endTime then ⟨0, time, grid⟩
      else
        let stats := scan grid
        if stats.status == 0 then
          let dt := Time.proposal n time stats.alpha
          let trial := retry (dt.toNat + 1) n time dt grid
          if trial.status == 0 then
            advance fuel n (add time trial.dt) trial.grid
          else ⟨trial.status, time, grid⟩
        else ⟨2, time, grid⟩

def run (n : Nat) : Result :=
  if 2 ≤ n ∧ n ≤ 800 then
    advance (Time.endTime.toNat + 1) n 0 (initialCells n)
  else ⟨1, 0, #[]⟩

def solve (n : Nat) : Array UInt64 :=
  let result := run n
  Output.pack n result.time result.status result.grid

end Project.EulerRiemann.Control
