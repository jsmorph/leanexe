import Project.OrderBook.ArtifactDecoded
import Project.OrderBook.ArtifactRawCache

namespace Project.OrderBook.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.OrderBook.Artifact
