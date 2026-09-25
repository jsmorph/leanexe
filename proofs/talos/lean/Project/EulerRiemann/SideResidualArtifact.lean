import Project.EulerRiemann.FrozenSideResidualExecution
import Project.EulerRiemann.ArtifactModule

namespace Project.EulerRiemann.SideResidual
open Project.EulerRiemann.Frozen.SideResidual

theorem artifact_side_residual :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧ SpecFor validated.toTalos :=
  Artifact.artifact_correct_of SpecFor side_residual

#print axioms artifact_side_residual
end Project.EulerRiemann.SideResidual
