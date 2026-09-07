import Project.F64SubBits.ArtifactDecoded
import Project.F64SubBits.ArtifactRawCache

namespace Project.F64SubBits.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.F64SubBits.Artifact
