import Project.EulerRiemann.FrozenCellResidualExecution
import Project.EulerRiemann.ArtifactModule

namespace Project.EulerRiemann.CellResidual
open Project.EulerRiemann.Frozen.CellResidual

theorem artifact_cell_residual :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧ SpecFor validated.toTalos :=
  Artifact.artifact_correct_of SpecFor cell_residual

#print axioms artifact_cell_residual
end Project.EulerRiemann.CellResidual
