import Project.Gpt2CachedStep.ArtifactDecoded
import Project.Gpt2CachedStep.ArtifactRawCache

namespace Project.Gpt2CachedStep.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.Gpt2CachedStep.Artifact
