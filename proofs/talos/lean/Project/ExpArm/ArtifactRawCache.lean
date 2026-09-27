import Project.ExpArm.ArtifactDecoded

namespace Project.ExpArm.Artifact

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Except.ok.inj (decode_eq_decodedRaw.symm.trans decode_eq_cache_parts)

end Project.ExpArm.Artifact
