import Project.ExpArm.ArtifactDecoded
import Project.ExpArm.ArtifactRawCache

namespace Project.ExpArm.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.ExpArm.Artifact
