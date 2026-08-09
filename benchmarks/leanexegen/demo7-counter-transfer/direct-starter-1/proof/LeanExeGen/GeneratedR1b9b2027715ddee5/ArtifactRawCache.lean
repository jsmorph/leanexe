import LeanExeGen.GeneratedR1b9b2027715ddee5.ArtifactDecoded
import LeanExeGen.GeneratedR1b9b2027715ddee5.ArtifactCache
import Project.Artifact.Binary.Equality

namespace LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact
