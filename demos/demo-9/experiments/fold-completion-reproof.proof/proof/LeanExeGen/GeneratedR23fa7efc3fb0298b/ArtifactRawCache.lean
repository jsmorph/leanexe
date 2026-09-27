import LeanExeGen.GeneratedR23fa7efc3fb0298b.ArtifactDecoded
import LeanExeGen.GeneratedR23fa7efc3fb0298b.ArtifactCache
import Project.Artifact.Binary.Equality

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact
