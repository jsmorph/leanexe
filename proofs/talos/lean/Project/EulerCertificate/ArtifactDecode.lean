import Project.EulerCertificate.ArtifactDecoded
import Project.EulerCertificate.ArtifactRawCache

namespace Project.EulerCertificate.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.EulerCertificate.Artifact
