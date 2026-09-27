import Project.EulerOutwardFaceStep.ArtifactDecoded
import Project.EulerOutwardFaceStep.ArtifactRawCache

namespace Project.EulerOutwardFaceStep.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerOutwardFaceStep.Artifact
