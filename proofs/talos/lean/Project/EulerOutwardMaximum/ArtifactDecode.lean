import Project.EulerOutwardMaximum.ArtifactDecoded
import Project.EulerOutwardMaximum.ArtifactRawCache

namespace Project.EulerOutwardMaximum.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerOutwardMaximum.Artifact
