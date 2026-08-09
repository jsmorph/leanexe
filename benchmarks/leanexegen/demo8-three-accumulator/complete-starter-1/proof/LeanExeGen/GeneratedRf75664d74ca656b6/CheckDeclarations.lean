import LeanExeGen.GeneratedRf75664d74ca656b6.ArtifactResult
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

open Wasm.Binary

example : decode LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.artifactBytes = .ok LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.Cache.raw :=
  LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.decode_eq_cache

example : Translation.module LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.Cache.raw =
    LeanExeGen.GeneratedRf75664d74ca656b6.«module» := by
  exact LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.translation_cache_eq

example :
    ∃ raw validated,
      decode LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.ArtifactSpec validated.toTalos :=
  LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.artifact_correct

#print axioms Wasm.Binary.Proof.decode_sound
#print axioms Wasm.Binary.Proof.validate_sound
#print axioms LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.decode_eq_cache
#print axioms LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.translation_cache_eq
#print axioms LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.artifact_module_eq_cache
#print axioms LeanExeGen.GeneratedRf75664d74ca656b6.Behavior.artifact_behavior
#print axioms LeanExeGen.GeneratedRf75664d74ca656b6.Artifact.artifact_correct
