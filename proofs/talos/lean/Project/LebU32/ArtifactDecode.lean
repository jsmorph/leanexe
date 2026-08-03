import Project.LebU32.ArtifactDecoded
import Project.LebU32.ArtifactRawCache

namespace Project.LebU32.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.LebU32.Artifact
