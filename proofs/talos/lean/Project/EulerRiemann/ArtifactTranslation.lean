import Project.EulerRiemann.ArtifactModule
import Project.EulerRiemann.FrozenSpec
import Project.EulerRiemann.UpdateResidualArtifact
import Project.EulerRiemann.ComponentResidualArtifact
import Project.EulerRiemann.SideResidualArtifact
import Project.EulerRiemann.InterfaceResidualArtifact
import Project.EulerRiemann.CellResidualArtifact

namespace Project.EulerRiemann.Artifact
open Wasm Wasm.Binary

theorem artifact_solve_exact :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Frozen.Spec.ExactSpecFor validated.toTalos := by
  exact artifact_correct_of Frozen.Spec.ExactSpecFor Frozen.Spec.solve_exact

theorem artifact_solve_success :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Frozen.Spec.SafeSpecFor validated.toTalos := by
  exact artifact_correct_of Frozen.Spec.SafeSpecFor Frozen.Spec.solve_success

theorem artifact_solve_hyperbolic :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Frozen.Spec.HyperbolicSpecFor validated.toTalos := by
  exact artifact_correct_of Frozen.Spec.HyperbolicSpecFor Frozen.Spec.solve_hyperbolic

theorem artifact_solve_balance :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Frozen.Spec.BalanceSpecFor validated.toTalos := by
  exact artifact_correct_of Frozen.Spec.BalanceSpecFor Frozen.Spec.solve_balance

#print axioms artifact_solve_exact
#print axioms artifact_solve_success
#print axioms artifact_solve_hyperbolic
#print axioms artifact_solve_balance

end Project.EulerRiemann.Artifact
