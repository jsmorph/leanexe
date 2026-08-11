import LeanExeGen.GeneratedR40ee67377869b401.ArtifactDecoded
import LeanExeGen.GeneratedR40ee67377869b401.ArtifactRawCache

namespace LeanExeGen.GeneratedR40ee67377869b401.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end LeanExeGen.GeneratedR40ee67377869b401.Artifact
