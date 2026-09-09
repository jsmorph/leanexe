import Project.EulerGridStep.ArtifactDecoded
import Project.EulerGridStep.ArtifactRawCache

namespace Project.EulerGridStep.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerGridStep.Artifact
