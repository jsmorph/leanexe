import LeanExeGen.GeneratedR4337040846e16beb.ArtifactTranslation
import LeanExeGen.GeneratedR4337040846e16beb.FormalSpec
import LeanExeGen.GeneratedR4337040846e16beb.Behavior

namespace LeanExeGen.GeneratedR4337040846e16beb.Artifact

open Wasm.Binary

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.ArtifactSpec validated.toTalos := by
  apply artifact_correct_of LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.ArtifactSpec
  simpa [executionCache] using LeanExeGen.GeneratedR4337040846e16beb.Behavior.artifact_behavior

end LeanExeGen.GeneratedR4337040846e16beb.Artifact
