import LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactDecoded
import LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactCache
import Project.Artifact.Binary.Equality

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact
