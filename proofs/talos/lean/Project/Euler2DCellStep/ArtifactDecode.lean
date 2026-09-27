import Project.Euler2DCellStep.ArtifactDecoded
import Project.Euler2DCellStep.ArtifactRawCache

namespace Project.Euler2DCellStep.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.Euler2DCellStep.Artifact
