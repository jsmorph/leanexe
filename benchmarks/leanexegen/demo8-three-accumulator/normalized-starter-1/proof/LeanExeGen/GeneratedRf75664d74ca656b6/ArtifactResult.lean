import LeanExeGen.GeneratedRf75664d74ca656b6.ArtifactTranslation
import LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec
import LeanExeGen.GeneratedRf75664d74ca656b6.Behavior

namespace LeanExeGen.GeneratedRf75664d74ca656b6.Artifact

open Wasm.Binary

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.ArtifactSpec validated.toTalos := by
  apply artifact_correct_of LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.ArtifactSpec
  simpa [executionCache] using LeanExeGen.GeneratedRf75664d74ca656b6.Behavior.artifact_behavior

end LeanExeGen.GeneratedRf75664d74ca656b6.Artifact
