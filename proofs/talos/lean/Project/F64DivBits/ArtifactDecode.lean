import Project.F64DivBits.ArtifactDecoded
import Project.F64DivBits.ArtifactRawCache

namespace Project.F64DivBits.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.F64DivBits.Artifact
