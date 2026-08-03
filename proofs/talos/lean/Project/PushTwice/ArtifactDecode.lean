import Project.PushTwice.ArtifactDecoded
import Project.PushTwice.ArtifactRawCache

namespace Project.PushTwice.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.PushTwice.Artifact
