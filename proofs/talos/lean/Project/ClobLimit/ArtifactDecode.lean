import Project.ClobLimit.ArtifactDecoded
import Project.ClobLimit.ArtifactRawCache

namespace Project.ClobLimit.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.ClobLimit.Artifact
