import Project.ClobCancel.ArtifactDecoded
import Project.ClobCancel.ArtifactCache
import Project.Artifact.Binary.Equality

namespace Project.ClobCancel.Artifact

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end Project.ClobCancel.Artifact
