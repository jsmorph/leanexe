import LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactDecoded
import LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactRawCache

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact
