import Project.ClobMarket.ArtifactDecoded
import Project.ClobMarket.ArtifactRawCache

namespace Project.ClobMarket.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.ClobMarket.Artifact
