import LeanExeGen.GeneratedR4337040846e16beb.ArtifactResult
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

open Wasm.Binary

example : decode LeanExeGen.GeneratedR4337040846e16beb.Artifact.artifactBytes = .ok LeanExeGen.GeneratedR4337040846e16beb.Artifact.Cache.raw :=
  LeanExeGen.GeneratedR4337040846e16beb.Artifact.decode_eq_cache

example : Translation.module LeanExeGen.GeneratedR4337040846e16beb.Artifact.Cache.raw =
    LeanExeGen.GeneratedR4337040846e16beb.«module» := by
  exact LeanExeGen.GeneratedR4337040846e16beb.Artifact.translation_cache_eq

example :
    ∃ raw validated,
      decode LeanExeGen.GeneratedR4337040846e16beb.Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.ArtifactSpec validated.toTalos :=
  LeanExeGen.GeneratedR4337040846e16beb.Artifact.artifact_correct

#print axioms Wasm.Binary.Proof.decode_sound
#print axioms Wasm.Binary.Proof.validate_sound
#print axioms LeanExeGen.GeneratedR4337040846e16beb.Artifact.decode_eq_cache
#print axioms LeanExeGen.GeneratedR4337040846e16beb.Artifact.translation_cache_eq
#print axioms LeanExeGen.GeneratedR4337040846e16beb.Artifact.artifact_module_eq_cache
#print axioms LeanExeGen.GeneratedR4337040846e16beb.Behavior.artifact_behavior
#print axioms LeanExeGen.GeneratedR4337040846e16beb.Artifact.artifact_correct
