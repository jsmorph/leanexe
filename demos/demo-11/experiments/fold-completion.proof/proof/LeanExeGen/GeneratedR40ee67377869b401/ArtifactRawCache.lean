import LeanExeGen.GeneratedR40ee67377869b401.ArtifactDecoded
import LeanExeGen.GeneratedR40ee67377869b401.ArtifactCache
import Project.Artifact.Binary.Equality

namespace LeanExeGen.GeneratedR40ee67377869b401.Artifact

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end LeanExeGen.GeneratedR40ee67377869b401.Artifact
