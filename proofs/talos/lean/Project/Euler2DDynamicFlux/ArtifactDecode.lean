import Project.Euler2DDynamicFlux.ArtifactDecoded
import Project.Euler2DDynamicFlux.ArtifactRawCache

namespace Project.Euler2DDynamicFlux.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.Euler2DDynamicFlux.Artifact
