import LeanExeGen.GeneratedR23fa7efc3fb0298b.ArtifactResult
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

open Wasm.Binary

example : decode LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.artifactBytes = .ok LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.Cache.raw :=
  LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.decode_eq_cache

example : Translation.module LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.Cache.raw =
    LeanExeGen.GeneratedR23fa7efc3fb0298b.«module» := by
  exact LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.translation_cache_eq

example :
    ∃ raw validated,
      decode LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec.ArtifactSpec validated.toTalos :=
  LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.artifact_correct

#print axioms Wasm.Binary.Proof.decode_sound
#print axioms Wasm.Binary.Proof.validate_sound
#print axioms LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.decode_eq_cache
#print axioms LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.translation_cache_eq
#print axioms LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.artifact_module_eq_cache
#print axioms LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior.artifact_behavior
#print axioms LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact.artifact_correct
