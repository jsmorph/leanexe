import LeanExeGen.GeneratedR23fa7efc3fb0298b.ArtifactDecoded
import LeanExeGen.GeneratedR23fa7efc3fb0298b.ArtifactRawCache

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact
