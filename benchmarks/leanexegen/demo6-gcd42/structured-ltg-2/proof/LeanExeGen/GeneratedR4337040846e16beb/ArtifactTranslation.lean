import LeanExeGen.GeneratedR4337040846e16beb.ArtifactValidation
import LeanExeGen.GeneratedR4337040846e16beb.Program
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace LeanExeGen.GeneratedR4337040846e16beb.Artifact

open Wasm
open Wasm.Binary

theorem function0_eq :
    Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!) =
      LeanExeGen.GeneratedR4337040846e16beb.func0Def := by
  rfl

theorem function1_eq :
    Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!) =
      LeanExeGen.GeneratedR4337040846e16beb.func1Def := by
  rfl

theorem function2_eq :
    Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!) =
      LeanExeGen.GeneratedR4337040846e16beb.func2Def := by
  rfl

theorem function3_eq :
    Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!) =
      LeanExeGen.GeneratedR4337040846e16beb.func3Def := by
  rfl

theorem function4_eq :
    Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!) =
      LeanExeGen.GeneratedR4337040846e16beb.func4Def := by
  rfl

theorem function5_eq :
    Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!) =
      LeanExeGen.GeneratedR4337040846e16beb.func5Def := by
  rfl

theorem functions_eq : Translation.functions Cache.raw =
    LeanExeGen.GeneratedR4337040846e16beb.«module».funcs := by
  change
    [
     Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!),
     Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!),
     Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!),
     Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!),
     Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!),
     Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!)
    ] =
    [LeanExeGen.GeneratedR4337040846e16beb.func0Def, LeanExeGen.GeneratedR4337040846e16beb.func1Def, LeanExeGen.GeneratedR4337040846e16beb.func2Def, LeanExeGen.GeneratedR4337040846e16beb.func3Def, LeanExeGen.GeneratedR4337040846e16beb.func4Def, LeanExeGen.GeneratedR4337040846e16beb.func5Def]
  rw [function0_eq, function1_eq, function2_eq, function3_eq, function4_eq, function5_eq]

def executionCache : Wasm.Module :=
  LeanExeGen.GeneratedR4337040846e16beb.«module»

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

end LeanExeGen.GeneratedR4337040846e16beb.Artifact
