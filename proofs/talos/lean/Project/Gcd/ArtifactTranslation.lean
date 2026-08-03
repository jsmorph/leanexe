import Project.Gcd.Artifact
import Project.Gcd.Spec
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace Project.Gcd.Artifact

open Wasm
open Wasm.Binary

theorem function0_eq :
    Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!) =
      Project.Gcd.func0Def := by
  rfl

theorem function1_eq :
    Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!) =
      Project.Gcd.func1Def := by
  rfl

theorem function2_eq :
    Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!) =
      Project.Gcd.func2Def := by
  rfl

theorem function3_eq :
    Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!) =
      Project.Gcd.func3Def := by
  rfl

theorem function4_eq :
    Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!) =
      Project.Gcd.func4Def := by
  rfl

theorem functions_eq : Translation.functions Cache.raw = Project.Gcd.«module».funcs := by
  change
    [Translation.functionToTalos Cache.raw 0 (Cache.raw.codes[0]!),
     Translation.functionToTalos Cache.raw 1 (Cache.raw.codes[1]!),
     Translation.functionToTalos Cache.raw 2 (Cache.raw.codes[2]!),
     Translation.functionToTalos Cache.raw 3 (Cache.raw.codes[3]!),
     Translation.functionToTalos Cache.raw 4 (Cache.raw.codes[4]!)] =
    [Project.Gcd.func0Def, Project.Gcd.func1Def, Project.Gcd.func2Def,
     Project.Gcd.func3Def, Project.Gcd.func4Def]
  rw [function0_eq, function1_eq, function2_eq, function3_eq, function4_eq]

def executionCache : Wasm.Module :=
  Project.Gcd.«module»

theorem translation_cache_eq : Translation.module Cache.raw = executionCache := by
  unfold Translation.module executionCache
  rw [functions_eq]
  rfl

theorem artifact_module_eq_cache :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      validated.toTalos = executionCache := by
  rcases decode_validate_exists with ⟨raw, validated, hdecode, hvalidate⟩
  have hraw : raw = Cache.raw := by
    rw [decode_eq_cache] at hdecode
    cases hdecode
    rfl
  subst raw
  refine ⟨Cache.raw, validated, decode_eq_cache, hvalidate,
    Proof.validate_sound hvalidate, ?_⟩
  rw [ValidatedModule.toTalos, Proof.validate_raw_eq hvalidate,
    translation_cache_eq]

def GcdSpecFor (module_ : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    TerminatesWith env module_ 0 initial [.i64 b, .i64 a]
      (fun _ results =>
        results = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

theorem executionCache_correct : GcdSpecFor executionCache := by
  simpa [GcdSpecFor, executionCache, Project.Gcd.Spec.GcdSpec] using
    Project.Gcd.Spec.gcd_correct

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      GcdSpecFor validated.toTalos := by
  rcases artifact_module_eq_cache with
    ⟨raw, validated, hdecode, hvalidate, hvalid, htranslation⟩
  refine ⟨raw, validated, hdecode, hvalidate, hvalid, ?_⟩
  rw [htranslation]
  exact executionCache_correct

end Project.Gcd.Artifact
