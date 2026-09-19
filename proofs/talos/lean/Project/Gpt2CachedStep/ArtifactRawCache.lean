import Project.Gpt2CachedStep.ArtifactDecoded

namespace Project.Gpt2CachedStep.Artifact

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Except.ok.inj (decode_eq_decodedRaw.symm.trans decode_eq_cache_parts)

end Project.Gpt2CachedStep.Artifact
