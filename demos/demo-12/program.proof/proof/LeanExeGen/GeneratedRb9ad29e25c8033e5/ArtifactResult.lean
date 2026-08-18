import LeanExeGen.GeneratedRb9ad29e25c8033e5.ArtifactTranslation
import LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec
import LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior

namespace LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact

open Wasm.Binary

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec.ArtifactSpec validated.toTalos := by
  apply artifact_correct_of LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec.ArtifactSpec
  simpa [executionCache] using LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior.artifact_behavior

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact
