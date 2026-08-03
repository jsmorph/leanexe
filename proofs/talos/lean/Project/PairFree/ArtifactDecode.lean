import Project.PairFree.ArtifactDecoded
import Project.PairFree.ArtifactRawCache

namespace Project.PairFree.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.PairFree.Artifact
