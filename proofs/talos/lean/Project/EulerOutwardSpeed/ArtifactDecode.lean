import Project.EulerOutwardSpeed.ArtifactDecoded
import Project.EulerOutwardSpeed.ArtifactRawCache

namespace Project.EulerOutwardSpeed.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerOutwardSpeed.Artifact
