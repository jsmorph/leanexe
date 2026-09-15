import Project.EulerReconstructed.ArtifactDecoded
import Project.EulerReconstructed.ArtifactRawCache

namespace Project.EulerReconstructed.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerReconstructed.Artifact
