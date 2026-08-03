import Project.ClobMatchFuel.ArtifactValidation
import Project.ClobMatchFuel.Program
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace Project.ClobMatchFuel.Artifact

open Wasm
open Wasm.Binary

theorem function0_eq :
    Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!) =
      Project.ClobMatchFuel.func0Def := by
  rfl

theorem function1_eq :
    Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!) =
      Project.ClobMatchFuel.func1Def := by
  rfl

theorem function2_eq :
    Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!) =
      Project.ClobMatchFuel.func2Def := by
  rfl

theorem function3_eq :
    Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!) =
      Project.ClobMatchFuel.func3Def := by
  rfl

theorem function4_eq :
    Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!) =
      Project.ClobMatchFuel.func4Def := by
  rfl

theorem function5_eq :
    Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!) =
      Project.ClobMatchFuel.func5Def := by
  rfl

theorem function6_eq :
    Translation.functionToTalos Cache.raw 6 (Cache.raw.codes[6]!) =
      Project.ClobMatchFuel.func6Def := by
  rfl

theorem function7_eq :
    Translation.functionToTalos Cache.raw 7 (Cache.raw.codes[7]!) =
      Project.ClobMatchFuel.func7Def := by
  rfl

theorem function8_eq :
    Translation.functionToTalos Cache.raw 8 (Cache.raw.codes[8]!) =
      Project.ClobMatchFuel.func8Def := by
  rfl

theorem function9_eq :
    Translation.functionToTalos Cache.raw 9 (Cache.raw.codes[9]!) =
      Project.ClobMatchFuel.func9Def := by
  rfl

theorem function10_eq :
    Translation.functionToTalos Cache.raw 10 (Cache.raw.codes[10]!) =
      Project.ClobMatchFuel.func10Def := by
  rfl

theorem function11_eq :
    Translation.functionToTalos Cache.raw 11 (Cache.raw.codes[11]!) =
      Project.ClobMatchFuel.func11Def := by
  rfl

theorem function12_eq :
    Translation.functionToTalos Cache.raw 12 (Cache.raw.codes[12]!) =
      Project.ClobMatchFuel.func12Def := by
  rfl

theorem function13_eq :
    Translation.functionToTalos Cache.raw 13 (Cache.raw.codes[13]!) =
      Project.ClobMatchFuel.func13Def := by
  rfl

theorem function14_eq :
    Translation.functionToTalos Cache.raw 14 (Cache.raw.codes[14]!) =
      Project.ClobMatchFuel.func14Def := by
  rfl

theorem function15_eq :
    Translation.functionToTalos Cache.raw 15 (Cache.raw.codes[15]!) =
      Project.ClobMatchFuel.func15Def := by
  rfl

theorem function16_eq :
    Translation.functionToTalos Cache.raw 16 (Cache.raw.codes[16]!) =
      Project.ClobMatchFuel.func16Def := by
  rfl

theorem function17_eq :
    Translation.functionToTalos Cache.raw 17 (Cache.raw.codes[17]!) =
      Project.ClobMatchFuel.func17Def := by
  rfl

theorem function18_eq :
    Translation.functionToTalos Cache.raw 18 (Cache.raw.codes[18]!) =
      Project.ClobMatchFuel.func18Def := by
  rfl

theorem functions_eq : Translation.functions Cache.raw =
    Project.ClobMatchFuel.«module».funcs := by
  change
    [
     Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!),
     Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!),
     Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!),
     Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!),
     Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!),
     Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!),
     Translation.functionToTalos Cache.raw 6 (Cache.raw.codes[6]!),
     Translation.functionToTalos Cache.raw 7 (Cache.raw.codes[7]!),
     Translation.functionToTalos Cache.raw 8 (Cache.raw.codes[8]!),
     Translation.functionToTalos Cache.raw 9 (Cache.raw.codes[9]!),
     Translation.functionToTalos Cache.raw 10 (Cache.raw.codes[10]!),
     Translation.functionToTalos Cache.raw 11 (Cache.raw.codes[11]!),
     Translation.functionToTalos Cache.raw 12 (Cache.raw.codes[12]!),
     Translation.functionToTalos Cache.raw 13 (Cache.raw.codes[13]!),
     Translation.functionToTalos Cache.raw 14 (Cache.raw.codes[14]!),
     Translation.functionToTalos Cache.raw 15 (Cache.raw.codes[15]!),
     Translation.functionToTalos Cache.raw 16 (Cache.raw.codes[16]!),
     Translation.functionToTalos Cache.raw 17 (Cache.raw.codes[17]!),
     Translation.functionToTalos Cache.raw 18 (Cache.raw.codes[18]!)
    ] =
    [Project.ClobMatchFuel.func0Def, Project.ClobMatchFuel.func1Def, Project.ClobMatchFuel.func2Def, Project.ClobMatchFuel.func3Def, Project.ClobMatchFuel.func4Def, Project.ClobMatchFuel.func5Def, Project.ClobMatchFuel.func6Def, Project.ClobMatchFuel.func7Def, Project.ClobMatchFuel.func8Def, Project.ClobMatchFuel.func9Def, Project.ClobMatchFuel.func10Def, Project.ClobMatchFuel.func11Def, Project.ClobMatchFuel.func12Def, Project.ClobMatchFuel.func13Def, Project.ClobMatchFuel.func14Def, Project.ClobMatchFuel.func15Def, Project.ClobMatchFuel.func16Def, Project.ClobMatchFuel.func17Def, Project.ClobMatchFuel.func18Def]
  rw [function0_eq, function1_eq, function2_eq, function3_eq, function4_eq, function5_eq, function6_eq, function7_eq, function8_eq, function9_eq, function10_eq, function11_eq, function12_eq, function13_eq, function14_eq, function15_eq, function16_eq, function17_eq, function18_eq]

def executionCache : Wasm.Module :=
  Project.ClobMatchFuel.«module»

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

end Project.ClobMatchFuel.Artifact
