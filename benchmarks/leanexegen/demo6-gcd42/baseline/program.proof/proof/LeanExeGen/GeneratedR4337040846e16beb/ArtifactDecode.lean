import LeanExeGen.GeneratedR4337040846e16beb.ArtifactDecoded
import LeanExeGen.GeneratedR4337040846e16beb.ArtifactRawCache

namespace LeanExeGen.GeneratedR4337040846e16beb.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end LeanExeGen.GeneratedR4337040846e16beb.Artifact
