import LeanExeGen.GeneratedR1b9b2027715ddee5.ArtifactResult
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

open Wasm.Binary

example : decode LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.artifactBytes = .ok LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.Cache.raw :=
  LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.decode_eq_cache

example : Translation.module LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.Cache.raw =
    LeanExeGen.GeneratedR1b9b2027715ddee5.«module» := by
  exact LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.translation_cache_eq

example :
    ∃ raw validated,
      decode LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.ArtifactSpec validated.toTalos :=
  LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.artifact_correct

#print axioms Wasm.Binary.Proof.decode_sound
#print axioms Wasm.Binary.Proof.validate_sound
#print axioms LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.decode_eq_cache
#print axioms LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.translation_cache_eq
#print axioms LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.artifact_module_eq_cache
#print axioms LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior.artifact_behavior
#print axioms LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact.artifact_correct
