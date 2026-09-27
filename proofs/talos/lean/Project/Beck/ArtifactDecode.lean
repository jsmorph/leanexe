import Project.Beck.ArtifactDecoded
import Project.Beck.ArtifactRawCache

namespace Project.Beck.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.Beck.Artifact
