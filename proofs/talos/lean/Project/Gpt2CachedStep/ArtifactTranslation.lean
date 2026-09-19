import Project.Gpt2CachedStep.ArtifactValidation
import Project.Gpt2CachedStep.Program
import Project.Gpt2CachedStep.Session.Spec
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace Project.Gpt2CachedStep.Artifact

open Wasm
open Wasm.Binary

theorem function0_eq :
    Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!) =
      Project.Gpt2CachedStep.func0Def := by
  rfl

theorem function1_eq :
    Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!) =
      Project.Gpt2CachedStep.func1Def := by
  rfl

theorem function2_eq :
    Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!) =
      Project.Gpt2CachedStep.func2Def := by
  rfl

theorem function3_eq :
    Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!) =
      Project.Gpt2CachedStep.func3Def := by
  rfl

theorem function4_eq :
    Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!) =
      Project.Gpt2CachedStep.func4Def := by
  rfl

theorem function5_eq :
    Translation.functionToTalos Cache.raw 5 (Cache.raw.codes[5]!) =
      Project.Gpt2CachedStep.func5Def := by
  rfl

theorem function6_eq :
    Translation.functionToTalos Cache.raw 6 (Cache.raw.codes[6]!) =
      Project.Gpt2CachedStep.func6Def := by
  rfl

theorem function7_eq :
    Translation.functionToTalos Cache.raw 7 (Cache.raw.codes[7]!) =
      Project.Gpt2CachedStep.func7Def := by
  rfl

theorem function8_eq :
    Translation.functionToTalos Cache.raw 8 (Cache.raw.codes[8]!) =
      Project.Gpt2CachedStep.func8Def := by
  rfl

theorem function9_eq :
    Translation.functionToTalos Cache.raw 9 (Cache.raw.codes[9]!) =
      Project.Gpt2CachedStep.func9Def := by
  rfl

theorem function10_eq :
    Translation.functionToTalos Cache.raw 10 (Cache.raw.codes[10]!) =
      Project.Gpt2CachedStep.func10Def := by
  rfl

theorem function11_eq :
    Translation.functionToTalos Cache.raw 11 (Cache.raw.codes[11]!) =
      Project.Gpt2CachedStep.func11Def := by
  rfl

theorem function12_eq :
    Translation.functionToTalos Cache.raw 12 (Cache.raw.codes[12]!) =
      Project.Gpt2CachedStep.func12Def := by
  rfl

theorem function13_eq :
    Translation.functionToTalos Cache.raw 13 (Cache.raw.codes[13]!) =
      Project.Gpt2CachedStep.func13Def := by
  rfl

theorem function14_eq :
    Translation.functionToTalos Cache.raw 14 (Cache.raw.codes[14]!) =
      Project.Gpt2CachedStep.func14Def := by
  rfl

theorem function15_eq :
    Translation.functionToTalos Cache.raw 15 (Cache.raw.codes[15]!) =
      Project.Gpt2CachedStep.func15Def := by
  rfl

theorem function16_eq :
    Translation.functionToTalos Cache.raw 16 (Cache.raw.codes[16]!) =
      Project.Gpt2CachedStep.func16Def := by
  rfl

theorem function17_eq :
    Translation.functionToTalos Cache.raw 17 (Cache.raw.codes[17]!) =
      Project.Gpt2CachedStep.func17Def := by
  rfl

theorem function18_eq :
    Translation.functionToTalos Cache.raw 18 (Cache.raw.codes[18]!) =
      Project.Gpt2CachedStep.func18Def := by
  rfl

theorem function19_eq :
    Translation.functionToTalos Cache.raw 19 (Cache.raw.codes[19]!) =
      Project.Gpt2CachedStep.func19Def := by
  rfl

theorem function20_eq :
    Translation.functionToTalos Cache.raw 20 (Cache.raw.codes[20]!) =
      Project.Gpt2CachedStep.func20Def := by
  rfl

theorem function21_eq :
    Translation.functionToTalos Cache.raw 21 (Cache.raw.codes[21]!) =
      Project.Gpt2CachedStep.func21Def := by
  rfl

theorem function22_eq :
    Translation.functionToTalos Cache.raw 22 (Cache.raw.codes[22]!) =
      Project.Gpt2CachedStep.func22Def := by
  rfl

theorem function23_eq :
    Translation.functionToTalos Cache.raw 23 (Cache.raw.codes[23]!) =
      Project.Gpt2CachedStep.func23Def := by
  rfl

theorem function24_eq :
    Translation.functionToTalos Cache.raw 24 (Cache.raw.codes[24]!) =
      Project.Gpt2CachedStep.func24Def := by
  rfl

theorem function25_eq :
    Translation.functionToTalos Cache.raw 25 (Cache.raw.codes[25]!) =
      Project.Gpt2CachedStep.func25Def := by
  rfl

theorem function26_eq :
    Translation.functionToTalos Cache.raw 26 (Cache.raw.codes[26]!) =
      Project.Gpt2CachedStep.func26Def := by
  rfl

theorem function27_eq :
    Translation.functionToTalos Cache.raw 27 (Cache.raw.codes[27]!) =
      Project.Gpt2CachedStep.func27Def := by
  rfl

theorem function28_eq :
    Translation.functionToTalos Cache.raw 28 (Cache.raw.codes[28]!) =
      Project.Gpt2CachedStep.func28Def := by
  rfl

theorem function29_eq :
    Translation.functionToTalos Cache.raw 29 (Cache.raw.codes[29]!) =
      Project.Gpt2CachedStep.func29Def := by
  rfl

theorem function30_eq :
    Translation.functionToTalos Cache.raw 30 (Cache.raw.codes[30]!) =
      Project.Gpt2CachedStep.func30Def := by
  rfl

theorem function31_eq :
    Translation.functionToTalos Cache.raw 31 (Cache.raw.codes[31]!) =
      Project.Gpt2CachedStep.func31Def := by
  rfl

theorem function32_eq :
    Translation.functionToTalos Cache.raw 32 (Cache.raw.codes[32]!) =
      Project.Gpt2CachedStep.func32Def := by
  rfl

theorem function33_eq :
    Translation.functionToTalos Cache.raw 33 (Cache.raw.codes[33]!) =
      Project.Gpt2CachedStep.func33Def := by
  rfl

theorem function34_eq :
    Translation.functionToTalos Cache.raw 34 (Cache.raw.codes[34]!) =
      Project.Gpt2CachedStep.func34Def := by
  rfl

theorem function35_eq :
    Translation.functionToTalos Cache.raw 35 (Cache.raw.codes[35]!) =
      Project.Gpt2CachedStep.func35Def := by
  rfl

theorem function36_eq :
    Translation.functionToTalos Cache.raw 36 (Cache.raw.codes[36]!) =
      Project.Gpt2CachedStep.func36Def := by
  rfl

theorem function37_eq :
    Translation.functionToTalos Cache.raw 37 (Cache.raw.codes[37]!) =
      Project.Gpt2CachedStep.func37Def := by
  rfl

theorem function38_eq :
    Translation.functionToTalos Cache.raw 38 (Cache.raw.codes[38]!) =
      Project.Gpt2CachedStep.func38Def := by
  rfl

theorem function39_eq :
    Translation.functionToTalos Cache.raw 39 (Cache.raw.codes[39]!) =
      Project.Gpt2CachedStep.func39Def := by
  rfl

theorem function40_eq :
    Translation.functionToTalos Cache.raw 40 (Cache.raw.codes[40]!) =
      Project.Gpt2CachedStep.func40Def := by
  rfl

theorem function41_eq :
    Translation.functionToTalos Cache.raw 41 (Cache.raw.codes[41]!) =
      Project.Gpt2CachedStep.func41Def := by
  rfl

theorem function42_eq :
    Translation.functionToTalos Cache.raw 42 (Cache.raw.codes[42]!) =
      Project.Gpt2CachedStep.func42Def := by
  rfl

theorem functions_eq : Translation.functions Cache.raw =
    Project.Gpt2CachedStep.«module».funcs := by
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
     Translation.functionToTalos Cache.raw 31 (Cache.raw.codes[31]!),
     Translation.functionToTalos Cache.raw 32 (Cache.raw.codes[32]!),
     Translation.functionToTalos Cache.raw 33 (Cache.raw.codes[33]!),
     Translation.functionToTalos Cache.raw 34 (Cache.raw.codes[34]!),
     Translation.functionToTalos Cache.raw 35 (Cache.raw.codes[35]!),
     Translation.functionToTalos Cache.raw 36 (Cache.raw.codes[36]!),
     Translation.functionToTalos Cache.raw 37 (Cache.raw.codes[37]!),
     Translation.functionToTalos Cache.raw 38 (Cache.raw.codes[38]!),
     Translation.functionToTalos Cache.raw 39 (Cache.raw.codes[39]!),
     Translation.functionToTalos Cache.raw 40 (Cache.raw.codes[40]!),
     Translation.functionToTalos Cache.raw 41 (Cache.raw.codes[41]!),
     Translation.functionToTalos Cache.raw 42 (Cache.raw.codes[42]!)
    ] =
    [Project.Gpt2CachedStep.func0Def, Project.Gpt2CachedStep.func1Def, Project.Gpt2CachedStep.func2Def, Project.Gpt2CachedStep.func3Def, Project.Gpt2CachedStep.func4Def, Project.Gpt2CachedStep.func5Def, Project.Gpt2CachedStep.func6Def, Project.Gpt2CachedStep.func7Def, Project.Gpt2CachedStep.func8Def, Project.Gpt2CachedStep.func9Def, Project.Gpt2CachedStep.func10Def, Project.Gpt2CachedStep.func11Def, Project.Gpt2CachedStep.func12Def, Project.Gpt2CachedStep.func13Def, Project.Gpt2CachedStep.func14Def, Project.Gpt2CachedStep.func15Def, Project.Gpt2CachedStep.func16Def, Project.Gpt2CachedStep.func17Def, Project.Gpt2CachedStep.func18Def, Project.Gpt2CachedStep.func19Def, Project.Gpt2CachedStep.func20Def, Project.Gpt2CachedStep.func21Def, Project.Gpt2CachedStep.func22Def, Project.Gpt2CachedStep.func23Def, Project.Gpt2CachedStep.func24Def, Project.Gpt2CachedStep.func25Def, Project.Gpt2CachedStep.func26Def, Project.Gpt2CachedStep.func27Def, Project.Gpt2CachedStep.func28Def, Project.Gpt2CachedStep.func29Def, Project.Gpt2CachedStep.func30Def, Project.Gpt2CachedStep.func31Def, Project.Gpt2CachedStep.func32Def, Project.Gpt2CachedStep.func33Def, Project.Gpt2CachedStep.func34Def, Project.Gpt2CachedStep.func35Def, Project.Gpt2CachedStep.func36Def, Project.Gpt2CachedStep.func37Def, Project.Gpt2CachedStep.func38Def, Project.Gpt2CachedStep.func39Def, Project.Gpt2CachedStep.func40Def, Project.Gpt2CachedStep.func41Def, Project.Gpt2CachedStep.func42Def]
  rw [function0_eq, function1_eq, function2_eq, function3_eq, function4_eq, function5_eq, function6_eq, function7_eq, function8_eq, function9_eq, function10_eq, function11_eq, function12_eq, function13_eq, function14_eq, function15_eq, function16_eq, function17_eq, function18_eq, function19_eq, function20_eq, function21_eq, function22_eq, function23_eq, function24_eq, function25_eq, function26_eq, function27_eq, function28_eq, function29_eq, function30_eq, function31_eq, function32_eq, function33_eq, function34_eq, function35_eq, function36_eq, function37_eq, function38_eq, function39_eq, function40_eq, function41_eq, function42_eq]

def executionCache : Wasm.Module :=
  Project.Gpt2CachedStep.«module»

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

theorem artifact_gpt2_128_exact :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      Grammar.Encodes artifactBytes raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Project.Gpt2CachedStep.Spec.ExactSpecFor validated.toTalos := by
  obtain ⟨raw, validated, hdecode, hvalidate, hvalid, hbehavior⟩ :=
    artifact_correct_of Project.Gpt2CachedStep.Spec.ExactSpecFor
      Project.Gpt2CachedStep.Spec.gpt2_128_exact_for
  exact ⟨raw, validated, hdecode, Proof.decode_sound hdecode,
    hvalidate, hvalid, hbehavior⟩

#print axioms decode_eq_cache
#print axioms translation_cache_eq
#print axioms artifact_module_eq_cache
#print axioms artifact_gpt2_128_exact

end Project.Gpt2CachedStep.Artifact
