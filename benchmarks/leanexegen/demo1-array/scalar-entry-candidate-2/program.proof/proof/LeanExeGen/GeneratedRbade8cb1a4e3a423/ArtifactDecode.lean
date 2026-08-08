import LeanExeGen.GeneratedRbade8cb1a4e3a423.ArtifactDecoded
import LeanExeGen.GeneratedRbade8cb1a4e3a423.ArtifactRawCache

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact
