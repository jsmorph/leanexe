import Project.EulerCellStep.ArtifactDecoded
import Project.EulerCellStep.ArtifactRawCache

namespace Project.EulerCellStep.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerCellStep.Artifact
