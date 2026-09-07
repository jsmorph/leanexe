import Project.EulerDynamicFlux.ArtifactDecoded
import Project.EulerDynamicFlux.ArtifactRawCache

namespace Project.EulerDynamicFlux.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerDynamicFlux.Artifact
