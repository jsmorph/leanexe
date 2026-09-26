import Project.Gpt2QuantizedCached.ArtifactDecoded

namespace Project.Gpt2QuantizedCached.Artifact

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Except.ok.inj (decode_eq_decodedRaw.symm.trans decode_eq_cache_parts)

end Project.Gpt2QuantizedCached.Artifact
