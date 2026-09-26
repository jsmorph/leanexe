import Project.Gpt2QuantizedCached.ArtifactDecoded
import Project.Gpt2QuantizedCached.ArtifactRawCache

namespace Project.Gpt2QuantizedCached.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.Gpt2QuantizedCached.Artifact
