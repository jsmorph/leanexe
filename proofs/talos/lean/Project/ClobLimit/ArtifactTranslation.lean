import Project.ClobLimit.ArtifactValidation
import Project.ClobLimit.Program
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace Project.ClobLimit.Artifact

open Wasm
open Wasm.Binary

theorem function0_eq :
    Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!) =
      Project.ClobLimit.func0Def := by
  rfl

theorem function1_eq :
    Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!) =
      Project.ClobLimit.func1Def := by
  rfl

theorem function2_eq :
    Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!) =
      Project.ClobLimit.func2Def := by
  rfl

theorem function3_eq :
    Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!) =
      Project.ClobLimit.func3Def := by
  rfl

theorem function4_eq :
    Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!) =
      Project.ClobLimit.func4Def := by
  rfl

theorem function5_eq :
    Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!) =
      Project.ClobLimit.func5Def := by
  rfl

theorem function6_eq :
    Translation.functionToTalos Cache.raw 6 (Cache.raw.codes[6]!) =
      Project.ClobLimit.func6Def := by
  rfl

theorem function7_eq :
    Translation.functionToTalos Cache.raw 7 (Cache.raw.codes[7]!) =
      Project.ClobLimit.func7Def := by
  rfl

theorem function8_eq :
    Translation.functionToTalos Cache.raw 8 (Cache.raw.codes[8]!) =
      Project.ClobLimit.func8Def := by
  rfl

theorem function9_eq :
    Translation.functionToTalos Cache.raw 9 (Cache.raw.codes[9]!) =
      Project.ClobLimit.func9Def := by
  rfl

theorem function10_eq :
    Translation.functionToTalos Cache.raw 10 (Cache.raw.codes[10]!) =
      Project.ClobLimit.func10Def := by
  rfl

theorem function11_eq :
    Translation.functionToTalos Cache.raw 11 (Cache.raw.codes[11]!) =
      Project.ClobLimit.func11Def := by
  rfl

theorem function12_eq :
    Translation.functionToTalos Cache.raw 12 (Cache.raw.codes[12]!) =
      Project.ClobLimit.func12Def := by
  rfl

theorem function13_eq :
    Translation.functionToTalos Cache.raw 13 (Cache.raw.codes[13]!) =
      Project.ClobLimit.func13Def := by
  rfl

theorem function14_eq :
    Translation.functionToTalos Cache.raw 14 (Cache.raw.codes[14]!) =
      Project.ClobLimit.func14Def := by
  rfl

theorem function15_eq :
    Translation.functionToTalos Cache.raw 15 (Cache.raw.codes[15]!) =
      Project.ClobLimit.func15Def := by
  rfl

theorem function16_eq :
    Translation.functionToTalos Cache.raw 16 (Cache.raw.codes[16]!) =
      Project.ClobLimit.func16Def := by
  rfl

theorem function17_eq :
    Translation.functionToTalos Cache.raw 17 (Cache.raw.codes[17]!) =
      Project.ClobLimit.func17Def := by
  rfl

theorem function18_eq :
    Translation.functionToTalos Cache.raw 18 (Cache.raw.codes[18]!) =
      Project.ClobLimit.func18Def := by
  rfl

theorem function19_eq :
    Translation.functionToTalos Cache.raw 19 (Cache.raw.codes[19]!) =
      Project.ClobLimit.func19Def := by
  rfl

theorem function20_eq :
    Translation.functionToTalos Cache.raw 20 (Cache.raw.codes[20]!) =
      Project.ClobLimit.func20Def := by
  rfl

theorem function21_eq :
    Translation.functionToTalos Cache.raw 21 (Cache.raw.codes[21]!) =
      Project.ClobLimit.func21Def := by
  rfl

theorem function22_eq :
    Translation.functionToTalos Cache.raw 22 (Cache.raw.codes[22]!) =
      Project.ClobLimit.func22Def := by
  rfl

theorem function23_eq :
    Translation.functionToTalos Cache.raw 23 (Cache.raw.codes[23]!) =
      Project.ClobLimit.func23Def := by
  rfl

theorem function24_eq :
    Translation.functionToTalos Cache.raw 24 (Cache.raw.codes[24]!) =
      Project.ClobLimit.func24Def := by
  rfl

theorem function25_eq :
    Translation.functionToTalos Cache.raw 25 (Cache.raw.codes[25]!) =
      Project.ClobLimit.func25Def := by
  rfl

theorem functions_eq : Translation.functions Cache.raw =
    Project.ClobLimit.«module».funcs := by
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
     Translation.functionToTalos Cache.raw 18 (Cache.raw.codes[18]!),
     Translation.functionToTalos Cache.raw 19 (Cache.raw.codes[19]!),
     Translation.functionToTalos Cache.raw 20 (Cache.raw.codes[20]!),
     Translation.functionToTalos Cache.raw 21 (Cache.raw.codes[21]!),
     Translation.functionToTalos Cache.raw 22 (Cache.raw.codes[22]!),
     Translation.functionToTalos Cache.raw 23 (Cache.raw.codes[23]!),
     Translation.functionToTalos Cache.raw 24 (Cache.raw.codes[24]!),
     Translation.functionToTalos Cache.raw 25 (Cache.raw.codes[25]!)
    ] =
    [Project.ClobLimit.func0Def, Project.ClobLimit.func1Def, Project.ClobLimit.func2Def, Project.ClobLimit.func3Def, Project.ClobLimit.func4Def, Project.ClobLimit.func5Def, Project.ClobLimit.func6Def, Project.ClobLimit.func7Def, Project.ClobLimit.func8Def, Project.ClobLimit.func9Def, Project.ClobLimit.func10Def, Project.ClobLimit.func11Def, Project.ClobLimit.func12Def, Project.ClobLimit.func13Def, Project.ClobLimit.func14Def, Project.ClobLimit.func15Def, Project.ClobLimit.func16Def, Project.ClobLimit.func17Def, Project.ClobLimit.func18Def, Project.ClobLimit.func19Def, Project.ClobLimit.func20Def, Project.ClobLimit.func21Def, Project.ClobLimit.func22Def, Project.ClobLimit.func23Def, Project.ClobLimit.func24Def, Project.ClobLimit.func25Def]
  rw [function0_eq, function1_eq, function2_eq, function3_eq, function4_eq, function5_eq, function6_eq, function7_eq, function8_eq, function9_eq, function10_eq, function11_eq, function12_eq, function13_eq, function14_eq, function15_eq, function16_eq, function17_eq, function18_eq, function19_eq, function20_eq, function21_eq, function22_eq, function23_eq, function24_eq, function25_eq]

def executionCache : Wasm.Module :=
  Project.ClobLimit.«module»

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

end Project.ClobLimit.Artifact
