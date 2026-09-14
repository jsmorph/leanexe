import Project.EulerOutwardFlux.ArtifactDecoded
import Project.EulerOutwardFlux.ArtifactRawCache

namespace Project.EulerOutwardFlux.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerOutwardFlux.Artifact
