import Project.ClobMatchFuel.ArtifactDecoded
import Project.ClobMatchFuel.ArtifactRawCache

namespace Project.ClobMatchFuel.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.ClobMatchFuel.Artifact
