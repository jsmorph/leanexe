import LeanExeGen.GeneratedRbade8cb1a4e3a423.ArtifactTranslation
import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact

open Wasm.Binary

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.ArtifactSpec validated.toTalos := by
  apply artifact_correct_of LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.ArtifactSpec
  simpa [executionCache] using LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior.artifact_behavior

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact
