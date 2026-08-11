import LeanExeGen.GeneratedR40ee67377869b401.ArtifactValidation
import LeanExeGen.GeneratedR40ee67377869b401.Program
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace LeanExeGen.GeneratedR40ee67377869b401.Artifact

open Wasm
open Wasm.Binary

theorem function0_eq :
    Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!) =
      LeanExeGen.GeneratedR40ee67377869b401.func0Def := by
  rfl

theorem function1_eq :
    Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!) =
      LeanExeGen.GeneratedR40ee67377869b401.func1Def := by
  rfl

theorem function2_eq :
    Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!) =
      LeanExeGen.GeneratedR40ee67377869b401.func2Def := by
  rfl

theorem function3_eq :
    Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!) =
      LeanExeGen.GeneratedR40ee67377869b401.func3Def := by
  rfl

theorem function4_eq :
    Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!) =
      LeanExeGen.GeneratedR40ee67377869b401.func4Def := by
  rfl

theorem functions_eq : Translation.functions Cache.raw =
    LeanExeGen.GeneratedR40ee67377869b401.«module».funcs := by
  change
    [
     Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!),
     Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!),
     Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!),
     Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!),
     Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!)
    ] =
    [LeanExeGen.GeneratedR40ee67377869b401.func0Def, LeanExeGen.GeneratedR40ee67377869b401.func1Def, LeanExeGen.GeneratedR40ee67377869b401.func2Def, LeanExeGen.GeneratedR40ee67377869b401.func3Def, LeanExeGen.GeneratedR40ee67377869b401.func4Def]
  rw [function0_eq, function1_eq, function2_eq, function3_eq, function4_eq]

def executionCache : Wasm.Module :=
  LeanExeGen.GeneratedR40ee67377869b401.«module»

theorem translation_cache_eq :
    Translation.module Cache.raw = executionCache := by
  unfold Translation.module executionCache
  rw [functions_eq]
  rfl

theorem artifact_correct_of (Property : Wasm.Module → Prop)
    (behavior : Property executionCache) :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Property validated.toTalos := by
  rcases cache_validation_exists with ⟨validated, hvalidate⟩
  have htranslation : validated.toTalos = executionCache := by
    rw [ValidatedModule.toTalos, Proof.validate_raw_eq hvalidate,
      translation_cache_eq]
  refine ⟨Cache.raw, validated, decode_eq_cache, hvalidate,
    Proof.validate_sound hvalidate, ?_⟩
  rw [htranslation]
  exact behavior

theorem artifact_module_eq_cache :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      validated.toTalos = executionCache := by
  exact artifact_correct_of (fun module_ => module_ = executionCache) rfl

end LeanExeGen.GeneratedR40ee67377869b401.Artifact
