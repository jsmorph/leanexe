import LeanExeGen.GeneratedRb9ad29e25c8033e5.ArtifactDecoded
import LeanExeGen.GeneratedRb9ad29e25c8033e5.ArtifactRawCache

namespace LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact
