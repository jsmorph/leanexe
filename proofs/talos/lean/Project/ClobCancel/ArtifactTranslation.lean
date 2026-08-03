import Project.ClobCancel.ArtifactValidation
import Project.ClobCancel.Program
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace Project.ClobCancel.Artifact

open Wasm
open Wasm.Binary

theorem function0_eq :
    Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!) =
      Project.ClobCancel.func0Def := by
  rfl

theorem function1_eq :
    Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!) =
      Project.ClobCancel.func1Def := by
  rfl

theorem function2_eq :
    Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!) =
      Project.ClobCancel.func2Def := by
  rfl

theorem function3_eq :
    Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!) =
      Project.ClobCancel.func3Def := by
  rfl

theorem function4_eq :
    Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!) =
      Project.ClobCancel.func4Def := by
  rfl

theorem function5_eq :
    Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!) =
      Project.ClobCancel.func5Def := by
  rfl

theorem function6_eq :
    Translation.functionToTalos Cache.raw 6 (Cache.raw.codes[6]!) =
      Project.ClobCancel.func6Def := by
  rfl

theorem function7_eq :
    Translation.functionToTalos Cache.raw 7 (Cache.raw.codes[7]!) =
      Project.ClobCancel.func7Def := by
  rfl

theorem functions_eq : Translation.functions Cache.raw =
    Project.ClobCancel.«module».funcs := by
  change
    [
     Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!),
     Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!),
     Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!),
     Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!),
     Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!),
     Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!),
     Translation.functionToTalos Cache.raw 6 (Cache.raw.codes[6]!),
     Translation.functionToTalos Cache.raw 7 (Cache.raw.codes[7]!)
    ] =
    [Project.ClobCancel.func0Def, Project.ClobCancel.func1Def, Project.ClobCancel.func2Def, Project.ClobCancel.func3Def, Project.ClobCancel.func4Def, Project.ClobCancel.func5Def, Project.ClobCancel.func6Def, Project.ClobCancel.func7Def]
  rw [function0_eq, function1_eq, function2_eq, function3_eq, function4_eq, function5_eq, function6_eq, function7_eq]

def executionCache : Wasm.Module :=
  Project.ClobCancel.«module»

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

end Project.ClobCancel.Artifact
