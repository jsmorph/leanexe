import Project.EulerConservative.ArtifactDecoded
import Project.EulerConservative.ArtifactRawCache

namespace Project.EulerConservative.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerConservative.Artifact
