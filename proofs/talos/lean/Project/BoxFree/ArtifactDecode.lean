import Project.BoxFree.ArtifactDecoded
import Project.BoxFree.ArtifactRawCache

namespace Project.BoxFree.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.BoxFree.Artifact
