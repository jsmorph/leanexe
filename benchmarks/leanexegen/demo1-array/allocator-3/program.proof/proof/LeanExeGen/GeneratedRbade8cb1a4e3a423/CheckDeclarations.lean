import LeanExeGen.GeneratedRbade8cb1a4e3a423.ArtifactResult
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

open Wasm.Binary

example : decode LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.artifactBytes = .ok LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.Cache.raw :=
  LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.decode_eq_cache

example : Translation.module LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.Cache.raw =
    LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» := by
  exact LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.translation_cache_eq

example :
    ∃ raw validated,
      decode LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.ArtifactSpec validated.toTalos :=
  LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.artifact_correct

#print axioms Wasm.Binary.Proof.decode_sound
#print axioms Wasm.Binary.Proof.validate_sound
#print axioms LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.decode_eq_cache
#print axioms LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.translation_cache_eq
#print axioms LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.artifact_module_eq_cache
#print axioms LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior.artifact_behavior
#print axioms LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.artifact_correct
