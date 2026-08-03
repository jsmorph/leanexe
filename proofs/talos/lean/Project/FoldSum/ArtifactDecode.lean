import Project.FoldSum.ArtifactDecoded
import Project.FoldSum.ArtifactRawCache

namespace Project.FoldSum.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.FoldSum.Artifact
