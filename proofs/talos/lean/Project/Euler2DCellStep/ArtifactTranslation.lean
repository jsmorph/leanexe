import Project.Euler2DCellStep.ArtifactValidation
import Project.Euler2DCellStep.Program
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace Project.Euler2DCellStep.Artifact

open Wasm
open Wasm.Binary

theorem function0_eq :
    Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!) =
      Project.Euler2DCellStep.func0Def := by
  rfl

theorem function1_eq :
    Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!) =
      Project.Euler2DCellStep.func1Def := by
  rfl

theorem function2_eq :
    Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!) =
      Project.Euler2DCellStep.func2Def := by
  rfl

theorem function3_eq :
    Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!) =
      Project.Euler2DCellStep.func3Def := by
  rfl

theorem function4_eq :
    Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!) =
      Project.Euler2DCellStep.func4Def := by
  rfl

theorem function5_eq :
    Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!) =
      Project.Euler2DCellStep.func5Def := by
  rfl

theorem function6_eq :
    Translation.functionToTalos Cache.raw 6 (Cache.raw.codes[6]!) =
      Project.Euler2DCellStep.func6Def := by
  rfl

theorem function7_eq :
    Translation.functionToTalos Cache.raw 7 (Cache.raw.codes[7]!) =
      Project.Euler2DCellStep.func7Def := by
  rfl

theorem function8_eq :
    Translation.functionToTalos Cache.raw 8 (Cache.raw.codes[8]!) =
      Project.Euler2DCellStep.func8Def := by
  rfl

theorem function9_eq :
    Translation.functionToTalos Cache.raw 9 (Cache.raw.codes[9]!) =
      Project.Euler2DCellStep.func9Def := by
  rfl

theorem function10_eq :
    Translation.functionToTalos Cache.raw 10 (Cache.raw.codes[10]!) =
      Project.Euler2DCellStep.func10Def := by
  rfl

theorem function11_eq :
    Translation.functionToTalos Cache.raw 11 (Cache.raw.codes[11]!) =
      Project.Euler2DCellStep.func11Def := by
  rfl

theorem function12_eq :
    Translation.functionToTalos Cache.raw 12 (Cache.raw.codes[12]!) =
      Project.Euler2DCellStep.func12Def := by
  rfl

theorem function13_eq :
    Translation.functionToTalos Cache.raw 13 (Cache.raw.codes[13]!) =
      Project.Euler2DCellStep.func13Def := by
  rfl

theorem function14_eq :
    Translation.functionToTalos Cache.raw 14 (Cache.raw.codes[14]!) =
      Project.Euler2DCellStep.func14Def := by
  rfl

theorem function15_eq :
    Translation.functionToTalos Cache.raw 15 (Cache.raw.codes[15]!) =
      Project.Euler2DCellStep.func15Def := by
  rfl

theorem function16_eq :
    Translation.functionToTalos Cache.raw 16 (Cache.raw.codes[16]!) =
      Project.Euler2DCellStep.func16Def := by
  rfl

theorem function17_eq :
    Translation.functionToTalos Cache.raw 17 (Cache.raw.codes[17]!) =
      Project.Euler2DCellStep.func17Def := by
  rfl

theorem function18_eq :
    Translation.functionToTalos Cache.raw 18 (Cache.raw.codes[18]!) =
      Project.Euler2DCellStep.func18Def := by
  rfl

theorem function19_eq :
    Translation.functionToTalos Cache.raw 19 (Cache.raw.codes[19]!) =
      Project.Euler2DCellStep.func19Def := by
  rfl

theorem function20_eq :
    Translation.functionToTalos Cache.raw 20 (Cache.raw.codes[20]!) =
      Project.Euler2DCellStep.func20Def := by
  rfl

theorem function21_eq :
    Translation.functionToTalos Cache.raw 21 (Cache.raw.codes[21]!) =
      Project.Euler2DCellStep.func21Def := by
  rfl

theorem function22_eq :
    Translation.functionToTalos Cache.raw 22 (Cache.raw.codes[22]!) =
      Project.Euler2DCellStep.func22Def := by
  rfl

theorem function23_eq :
    Translation.functionToTalos Cache.raw 23 (Cache.raw.codes[23]!) =
      Project.Euler2DCellStep.func23Def := by
  rfl

theorem function24_eq :
    Translation.functionToTalos Cache.raw 24 (Cache.raw.codes[24]!) =
      Project.Euler2DCellStep.func24Def := by
  rfl

theorem function25_eq :
    Translation.functionToTalos Cache.raw 25 (Cache.raw.codes[25]!) =
      Project.Euler2DCellStep.func25Def := by
  rfl

theorem function26_eq :
    Translation.functionToTalos Cache.raw 26 (Cache.raw.codes[26]!) =
      Project.Euler2DCellStep.func26Def := by
  rfl

theorem function27_eq :
    Translation.functionToTalos Cache.raw 27 (Cache.raw.codes[27]!) =
      Project.Euler2DCellStep.func27Def := by
  rfl

theorem function28_eq :
    Translation.functionToTalos Cache.raw 28 (Cache.raw.codes[28]!) =
      Project.Euler2DCellStep.func28Def := by
  rfl

theorem function29_eq :
    Translation.functionToTalos Cache.raw 29 (Cache.raw.codes[29]!) =
      Project.Euler2DCellStep.func29Def := by
  rfl

theorem function30_eq :
    Translation.functionToTalos Cache.raw 30 (Cache.raw.codes[30]!) =
      Project.Euler2DCellStep.func30Def := by
  rfl

theorem function31_eq :
    Translation.functionToTalos Cache.raw 31 (Cache.raw.codes[31]!) =
      Project.Euler2DCellStep.func31Def := by
  rfl

theorem functions_eq : Translation.functions Cache.raw =
    Project.Euler2DCellStep.«module».funcs := by
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
     Translation.functionToTalos Cache.raw 25 (Cache.raw.codes[25]!),
     Translation.functionToTalos Cache.raw 26 (Cache.raw.codes[26]!),
     Translation.functionToTalos Cache.raw 27 (Cache.raw.codes[27]!),
     Translation.functionToTalos Cache.raw 28 (Cache.raw.codes[28]!),
     Translation.functionToTalos Cache.raw 29 (Cache.raw.codes[29]!),
     Translation.functionToTalos Cache.raw 30 (Cache.raw.codes[30]!),
     Translation.functionToTalos Cache.raw 31 (Cache.raw.codes[31]!)
    ] =
    [Project.Euler2DCellStep.func0Def, Project.Euler2DCellStep.func1Def, Project.Euler2DCellStep.func2Def, Project.Euler2DCellStep.func3Def, Project.Euler2DCellStep.func4Def, Project.Euler2DCellStep.func5Def, Project.Euler2DCellStep.func6Def, Project.Euler2DCellStep.func7Def, Project.Euler2DCellStep.func8Def, Project.Euler2DCellStep.func9Def, Project.Euler2DCellStep.func10Def, Project.Euler2DCellStep.func11Def, Project.Euler2DCellStep.func12Def, Project.Euler2DCellStep.func13Def, Project.Euler2DCellStep.func14Def, Project.Euler2DCellStep.func15Def, Project.Euler2DCellStep.func16Def, Project.Euler2DCellStep.func17Def, Project.Euler2DCellStep.func18Def, Project.Euler2DCellStep.func19Def, Project.Euler2DCellStep.func20Def, Project.Euler2DCellStep.func21Def, Project.Euler2DCellStep.func22Def, Project.Euler2DCellStep.func23Def, Project.Euler2DCellStep.func24Def, Project.Euler2DCellStep.func25Def, Project.Euler2DCellStep.func26Def, Project.Euler2DCellStep.func27Def, Project.Euler2DCellStep.func28Def, Project.Euler2DCellStep.func29Def, Project.Euler2DCellStep.func30Def, Project.Euler2DCellStep.func31Def]
  rw [function0_eq, function1_eq, function2_eq, function3_eq, function4_eq, function5_eq, function6_eq, function7_eq, function8_eq, function9_eq, function10_eq, function11_eq, function12_eq, function13_eq, function14_eq, function15_eq, function16_eq, function17_eq, function18_eq, function19_eq, function20_eq, function21_eq, function22_eq, function23_eq, function24_eq, function25_eq, function26_eq, function27_eq, function28_eq, function29_eq, function30_eq, function31_eq]

def executionCache : Wasm.Module :=
  Project.Euler2DCellStep.«module»

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

end Project.Euler2DCellStep.Artifact
