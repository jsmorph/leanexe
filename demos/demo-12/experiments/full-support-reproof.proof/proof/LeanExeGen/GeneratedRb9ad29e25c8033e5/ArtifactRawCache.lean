import LeanExeGen.GeneratedRb9ad29e25c8033e5.ArtifactDecoded
import LeanExeGen.GeneratedRb9ad29e25c8033e5.ArtifactCache
import Project.Artifact.Binary.Equality

namespace LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact
