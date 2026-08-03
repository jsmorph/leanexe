import Project.AppendBang.ArtifactDecoded
import Project.AppendBang.ArtifactRawCache

namespace Project.AppendBang.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.AppendBang.Artifact
