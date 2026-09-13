import Project.EulerRiemann.ArtifactDecoded
import Project.EulerRiemann.ArtifactRawCache

namespace Project.EulerRiemann.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerRiemann.Artifact
