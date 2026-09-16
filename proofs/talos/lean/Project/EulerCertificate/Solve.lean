import Project.EulerCertificate.Control

namespace Project.EulerCertificate.Solve
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell initialCells)
open Project.EulerCertificate.Flux (Vector)

structure Report where
  status : UInt64
  time : UInt64
  grid : Array Cell
  residual : Vector

def run (n trials : Nat) : Report :=
  if 2 ≤ n ∧ n ≤ 800 then
    let grid := initialCells n
    let initial := Totals.physical n grid
    let result := Control.advance (Time.endTime.toNat + 1) n trials 0 grid Vectors.zero
    let final := Totals.physical n result.grid
    let change := Vectors.sub final initial
    let residual := Vectors.sub change result.boundary
    ⟨result.status, result.time, result.grid, residual⟩
  else
    let rejected := Project.ProofKit.F64Interval.rejected
    ⟨1, 0, #[], ⟨rejected, rejected, rejected, rejected⟩⟩

def pack (n : Nat) (report : Report) : Array UInt64 :=
  let base := Output.pack n report.time report.status report.grid
  let r := report.residual
  let certificate := #[r.mass.status, r.mass.lower, r.mass.upper,
    r.momentum.status, r.momentum.lower, r.momentum.upper,
    r.transverse.status, r.transverse.lower, r.transverse.upper,
    r.energy.status, r.energy.lower, r.energy.upper]
  let result := base ++ certificate
  let _ := LeanExe.Runtime.release base
  let _ := LeanExe.Runtime.release certificate
  result

def solve (n trials : Nat) : Array UInt64 := pack n (run n trials)

end Project.EulerCertificate.Solve
