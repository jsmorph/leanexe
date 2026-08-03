import Project.PushSize.ArtifactDecoded
import Project.PushSize.ArtifactRawCache

namespace Project.PushSize.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.PushSize.Artifact
