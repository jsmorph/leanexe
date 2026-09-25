import Project.EulerRiemann.FrozenComponentResidualExecution
import Project.EulerRiemann.ArtifactModule

namespace Project.EulerRiemann.ComponentResidual
open Project.EulerRiemann.Frozen.ComponentResidual

theorem artifact_component_residual :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧ SpecFor validated.toTalos :=
  Artifact.artifact_correct_of SpecFor component_residual

#print axioms artifact_component_residual

end Project.EulerRiemann.ComponentResidual
