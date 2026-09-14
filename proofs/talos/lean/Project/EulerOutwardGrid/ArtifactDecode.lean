import Project.EulerOutwardGrid.ArtifactDecoded
import Project.EulerOutwardGrid.ArtifactRawCache

namespace Project.EulerOutwardGrid.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerOutwardGrid.Artifact
