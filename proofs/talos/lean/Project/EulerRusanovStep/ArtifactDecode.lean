import Project.EulerRusanovStep.ArtifactDecoded
import Project.EulerRusanovStep.ArtifactRawCache

namespace Project.EulerRusanovStep.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerRusanovStep.Artifact
