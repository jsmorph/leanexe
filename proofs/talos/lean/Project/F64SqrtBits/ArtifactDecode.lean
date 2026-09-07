import Project.F64SqrtBits.ArtifactDecoded
import Project.F64SqrtBits.ArtifactRawCache

namespace Project.F64SqrtBits.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.F64SqrtBits.Artifact
