import LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactTranslation
import LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec
import LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact

open Wasm.Binary

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.ArtifactSpec validated.toTalos := by
  apply artifact_correct_of LeanExeGen.GeneratedRa8e90ffc5781d113.FormalSpec.ArtifactSpec
  simpa [executionCache] using LeanExeGen.GeneratedRa8e90ffc5781d113.Behavior.artifact_behavior

end LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact
