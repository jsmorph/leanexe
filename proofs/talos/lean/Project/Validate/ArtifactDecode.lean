import Project.Validate.ArtifactDecoded
import Project.Validate.ArtifactRawCache

namespace Project.Validate.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.Validate.Artifact
