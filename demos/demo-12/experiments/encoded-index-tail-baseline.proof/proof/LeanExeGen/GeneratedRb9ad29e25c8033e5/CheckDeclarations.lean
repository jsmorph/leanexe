import LeanExeGen.GeneratedRb9ad29e25c8033e5.ArtifactResult
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

open Wasm.Binary

example : decode LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.artifactBytes = .ok LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.Cache.raw :=
  LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.decode_eq_cache

example : Translation.module LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.Cache.raw =
    LeanExeGen.GeneratedRb9ad29e25c8033e5.«module» := by
  exact LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.translation_cache_eq

example :
    ∃ raw validated,
      decode LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec.ArtifactSpec validated.toTalos :=
  LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.artifact_correct

#print axioms Wasm.Binary.Proof.decode_sound
#print axioms Wasm.Binary.Proof.validate_sound
#print axioms LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.decode_eq_cache
#print axioms LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.translation_cache_eq
#print axioms LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.artifact_module_eq_cache
#print axioms LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior.artifact_behavior
#print axioms LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact.artifact_correct
