import Project.Gpt2QuantizedGroupedRows.ArtifactDecoded

namespace Project.Gpt2QuantizedGroupedRows.Artifact

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Except.ok.inj (decode_eq_decodedRaw.symm.trans decode_eq_cache_parts)

end Project.Gpt2QuantizedGroupedRows.Artifact
