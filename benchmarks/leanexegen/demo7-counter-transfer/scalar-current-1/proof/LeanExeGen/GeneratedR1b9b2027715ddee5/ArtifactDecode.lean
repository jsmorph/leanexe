import LeanExeGen.GeneratedR1b9b2027715ddee5.ArtifactDecoded
import LeanExeGen.GeneratedR1b9b2027715ddee5.ArtifactRawCache

namespace LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact
