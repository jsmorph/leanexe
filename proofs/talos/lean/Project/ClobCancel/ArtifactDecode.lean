import Project.ClobCancel.ArtifactDecoded
import Project.ClobCancel.ArtifactRawCache

namespace Project.ClobCancel.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.ClobCancel.Artifact
