import Project.EulerRiemann.ArtifactDecoded

namespace Project.EulerRiemann.Artifact

open Wasm.Binary

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Except.ok.inj (decode_eq_decodedRaw.symm.trans decode_eq_cache_parts)

end Project.EulerRiemann.Artifact
