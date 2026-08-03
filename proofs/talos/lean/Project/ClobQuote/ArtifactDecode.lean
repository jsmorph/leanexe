import Project.ClobQuote.ArtifactDecoded
import Project.ClobQuote.ArtifactRawCache

namespace Project.ClobQuote.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.ClobQuote.Artifact
