import Project.AssocList.ArtifactDecoded
import Project.AssocList.ArtifactRawCache

namespace Project.AssocList.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.AssocList.Artifact
