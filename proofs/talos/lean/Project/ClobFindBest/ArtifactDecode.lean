import Project.ClobFindBest.ArtifactDecoded
import Project.ClobFindBest.ArtifactRawCache

namespace Project.ClobFindBest.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.ClobFindBest.Artifact
