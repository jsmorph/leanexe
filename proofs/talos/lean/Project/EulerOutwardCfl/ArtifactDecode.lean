import Project.EulerOutwardCfl.ArtifactDecoded
import Project.EulerOutwardCfl.ArtifactRawCache

namespace Project.EulerOutwardCfl.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerOutwardCfl.Artifact
