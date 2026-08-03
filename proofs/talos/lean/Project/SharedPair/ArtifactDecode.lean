import Project.SharedPair.ArtifactDecoded
import Project.SharedPair.ArtifactRawCache

namespace Project.SharedPair.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.SharedPair.Artifact
