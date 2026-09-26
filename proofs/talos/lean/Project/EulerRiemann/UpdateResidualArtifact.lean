import Project.EulerRiemann.FrozenUpdateResidualExecution
import Project.EulerRiemann.ArtifactModule

namespace Project.EulerRiemann.UpdateResidual
open Project.EulerRiemann.Frozen.UpdateResidual

theorem artifact_update_residual :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧ SpecFor validated.toTalos :=
  Artifact.artifact_correct_of SpecFor update_residual

#print axioms artifact_update_residual

end Project.EulerRiemann.UpdateResidual
