import Project.EulerCertificate.SolveSpec

namespace Project.EulerCertificate.Solve

def certificateWords (r : Flux.Vector) : List UInt64 :=
  [r.mass.status, r.mass.lower, r.mass.upper,
    r.momentum.status, r.momentum.lower, r.momentum.upper,
    r.transverse.status, r.transverse.lower, r.transverse.upper,
    r.energy.status, r.energy.lower, r.energy.upper]

theorem pack_toList (n : Nat) (report : Report) :
    (pack n report).toList =
      (Project.EulerRiemann.Output.pack n report.time report.status report.grid).toList ++
        certificateWords report.residual := by
  simp [pack, certificateWords]

theorem pack_size (n : Nat) (report : Report) :
    (pack n report).size = 16 + 2 * report.grid.size := by
  simp [pack, Project.EulerRiemann.Output.pack_size]
  omega

theorem solve_toList (n trials : Nat) :
    (solve n trials).toList = (Project.EulerReconstructed.Control.solve n trials).toList ++
      certificateWords (run n trials).residual := by
  have he := congrArg (fun out : Project.EulerRiemann.Control.Result =>
    Project.EulerRiemann.Output.pack n out.time out.status out.grid) (run_base n trials)
  change Project.EulerRiemann.Output.pack n (run n trials).time (run n trials).status (run n trials).grid =
    Project.EulerReconstructed.Control.solve n trials at he
  rw [solve, pack_toList, he]

theorem solve_size (n trials : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    (solve n trials).size = 16 + 2 * (n * n) := by
  have he := congrArg Project.EulerRiemann.Control.Result.grid (run_base n trials)
  change (run n trials).grid = (Project.EulerReconstructed.Control.run n trials).grid at he
  rw [solve, pack_size, he, (Project.EulerReconstructed.Control.run_indexed n trials hn).1]

#print axioms pack_toList
#print axioms solve_toList
#print axioms solve_size
end Project.EulerCertificate.Solve
