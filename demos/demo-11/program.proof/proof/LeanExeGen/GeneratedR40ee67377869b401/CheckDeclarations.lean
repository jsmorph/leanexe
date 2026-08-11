import LeanExeGen.GeneratedR40ee67377869b401.ArtifactResult
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

open Wasm.Binary

example : decode LeanExeGen.GeneratedR40ee67377869b401.Artifact.artifactBytes = .ok LeanExeGen.GeneratedR40ee67377869b401.Artifact.Cache.raw :=
  LeanExeGen.GeneratedR40ee67377869b401.Artifact.decode_eq_cache

example : Translation.module LeanExeGen.GeneratedR40ee67377869b401.Artifact.Cache.raw =
    LeanExeGen.GeneratedR40ee67377869b401.«module» := by
  exact LeanExeGen.GeneratedR40ee67377869b401.Artifact.translation_cache_eq

example :
    ∃ raw validated,
      decode LeanExeGen.GeneratedR40ee67377869b401.Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedR40ee67377869b401.FormalSpec.ArtifactSpec validated.toTalos :=
  LeanExeGen.GeneratedR40ee67377869b401.Artifact.artifact_correct

#print axioms Wasm.Binary.Proof.decode_sound
#print axioms Wasm.Binary.Proof.validate_sound
#print axioms LeanExeGen.GeneratedR40ee67377869b401.Artifact.decode_eq_cache
#print axioms LeanExeGen.GeneratedR40ee67377869b401.Artifact.translation_cache_eq
#print axioms LeanExeGen.GeneratedR40ee67377869b401.Artifact.artifact_module_eq_cache
#print axioms LeanExeGen.GeneratedR40ee67377869b401.Behavior.artifact_behavior
#print axioms LeanExeGen.GeneratedR40ee67377869b401.Artifact.artifact_correct
