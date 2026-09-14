import Project.EulerRiemann.InterfaceResidualExecution
import Project.EulerRiemann.ArtifactModule

namespace Project.EulerRiemann.InterfaceResidual

theorem artifact_interface_residual :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧ SpecFor validated.toTalos :=
  Artifact.artifact_correct_of SpecFor interface_residual

#print axioms artifact_interface_residual
end Project.EulerRiemann.InterfaceResidual
