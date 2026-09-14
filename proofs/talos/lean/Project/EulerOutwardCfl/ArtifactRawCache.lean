import Project.EulerOutwardCfl.ArtifactDecoded

namespace Project.EulerOutwardCfl.Artifact

open Wasm.Binary

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Except.ok.inj (decode_eq_decodedRaw.symm.trans decode_eq_cache_computed)

end Project.EulerOutwardCfl.Artifact
