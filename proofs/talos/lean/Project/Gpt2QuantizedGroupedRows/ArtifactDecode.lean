import Project.Gpt2QuantizedGroupedRows.ArtifactDecoded
import Project.Gpt2QuantizedGroupedRows.ArtifactRawCache

namespace Project.Gpt2QuantizedGroupedRows.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.Gpt2QuantizedGroupedRows.Artifact
