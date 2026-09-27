import LeanExeGen.GeneratedRf75664d74ca656b6.ArtifactDecoded
import LeanExeGen.GeneratedRf75664d74ca656b6.ArtifactRawCache

namespace LeanExeGen.GeneratedRf75664d74ca656b6.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end LeanExeGen.GeneratedRf75664d74ca656b6.Artifact
