import Project.ClobPostOnly.ArtifactDecoded
import Project.ClobPostOnly.ArtifactRawCache

namespace Project.ClobPostOnly.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.ClobPostOnly.Artifact
