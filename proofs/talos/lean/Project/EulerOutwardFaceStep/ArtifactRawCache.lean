import Project.EulerOutwardFaceStep.ArtifactDecoded

namespace Project.EulerOutwardFaceStep.Artifact

open Wasm.Binary

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Except.ok.inj (decode_eq_decodedRaw.symm.trans decode_eq_cache_computed)

end Project.EulerOutwardFaceStep.Artifact
