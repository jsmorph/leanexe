import LeanExeGen.GeneratedRf75664d74ca656b6.ArtifactValidation
import LeanExeGen.GeneratedRf75664d74ca656b6.Program
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace LeanExeGen.GeneratedRf75664d74ca656b6.Artifact

open Wasm
open Wasm.Binary

theorem function0_eq :
    Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!) =
      LeanExeGen.GeneratedRf75664d74ca656b6.func0Def := by
  rfl

theorem function1_eq :
    Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!) =
      LeanExeGen.GeneratedRf75664d74ca656b6.func1Def := by
  rfl

theorem function2_eq :
    Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!) =
      LeanExeGen.GeneratedRf75664d74ca656b6.func2Def := by
  rfl

theorem function3_eq :
    Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!) =
      LeanExeGen.GeneratedRf75664d74ca656b6.func3Def := by
  rfl

theorem function4_eq :
    Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!) =
      LeanExeGen.GeneratedRf75664d74ca656b6.func4Def := by
  rfl

theorem function5_eq :
    Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!) =
      LeanExeGen.GeneratedRf75664d74ca656b6.func5Def := by
  rfl

theorem functions_eq : Translation.functions Cache.raw =
    LeanExeGen.GeneratedRf75664d74ca656b6.«module».funcs := by
  change
    [
     Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!),
     Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!),
     Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!),
     Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!),
     Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!),
     Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!)
    ] =
    [LeanExeGen.GeneratedRf75664d74ca656b6.func0Def, LeanExeGen.GeneratedRf75664d74ca656b6.func1Def, LeanExeGen.GeneratedRf75664d74ca656b6.func2Def, LeanExeGen.GeneratedRf75664d74ca656b6.func3Def, LeanExeGen.GeneratedRf75664d74ca656b6.func4Def, LeanExeGen.GeneratedRf75664d74ca656b6.func5Def]
  rw [function0_eq, function1_eq, function2_eq, function3_eq, function4_eq, function5_eq]

def executionCache : Wasm.Module :=
  LeanExeGen.GeneratedRf75664d74ca656b6.«module»

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

end LeanExeGen.GeneratedRf75664d74ca656b6.Artifact
