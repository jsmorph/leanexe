import LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactResult
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

open Wasm.Binary

example : decode LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.artifactBytes = .ok LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.Cache.raw :=
  LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.decode_eq_cache

example : Translation.module LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.Cache.raw =
    LeanExeGen.GeneratedRa8e90ffc5781d113.«module» := by
  exact LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.translation_cache_eq

example :
    ∃ raw validated,
      decode LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.ArtifactSpec validated.toTalos :=
  LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.artifact_correct

#print axioms Wasm.Binary.Proof.decode_sound
#print axioms Wasm.Binary.Proof.validate_sound
#print axioms LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.decode_eq_cache
#print axioms LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.translation_cache_eq
#print axioms LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.artifact_module_eq_cache
#print axioms LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior.artifact_behavior
#print axioms LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.artifact_correct
