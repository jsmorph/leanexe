import Project.EulerRiemann.ArtifactModule
import Project.EulerRiemann.Spec
import Project.EulerRiemann.UpdateResidualArtifact
import Project.EulerRiemann.ComponentResidualArtifact
import Project.EulerRiemann.SideResidualArtifact

namespace Project.EulerRiemann.Artifact
open Wasm Wasm.Binary

theorem artifact_solve_exact :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Spec.ExactSpecFor validated.toTalos := by
  exact artifact_correct_of Spec.ExactSpecFor Spec.solve_exact

theorem artifact_solve_success :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Spec.SafeSpecFor validated.toTalos := by
  exact artifact_correct_of Spec.SafeSpecFor Spec.solve_success

theorem artifact_solve_hyperbolic :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Spec.HyperbolicSpecFor validated.toTalos := by
  exact artifact_correct_of Spec.HyperbolicSpecFor Spec.solve_hyperbolic

#print axioms artifact_solve_exact
#print axioms artifact_solve_success
#print axioms artifact_solve_hyperbolic

end Project.EulerRiemann.Artifact
