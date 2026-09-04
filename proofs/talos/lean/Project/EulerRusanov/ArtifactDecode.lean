import Project.EulerRusanov.ArtifactDecoded
import Project.EulerRusanov.ArtifactRawCache

namespace Project.EulerRusanov.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerRusanov.Artifact
