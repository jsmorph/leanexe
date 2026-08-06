import LeanExeGen.GeneratedRbade8cb1a4e3a423.ArtifactDecoded
import LeanExeGen.GeneratedRbade8cb1a4e3a423.ArtifactCache
import Project.Artifact.Binary.Equality

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact
