import Project.ClobDepth.ArtifactDecoded
import Project.ClobDepth.ArtifactRawCache

namespace Project.ClobDepth.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.ClobDepth.Artifact
