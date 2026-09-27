import LeanExeGen.GeneratedR4337040846e16beb.ArtifactDecoded
import LeanExeGen.GeneratedR4337040846e16beb.ArtifactCache
import Project.Artifact.Binary.Equality

namespace LeanExeGen.GeneratedR4337040846e16beb.Artifact

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end LeanExeGen.GeneratedR4337040846e16beb.Artifact
