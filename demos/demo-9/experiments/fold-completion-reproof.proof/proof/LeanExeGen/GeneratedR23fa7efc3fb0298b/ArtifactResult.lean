import LeanExeGen.GeneratedR23fa7efc3fb0298b.ArtifactTranslation
import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact

open Wasm.Binary

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec.ArtifactSpec validated.toTalos := by
  apply artifact_correct_of LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec.ArtifactSpec
  simpa [executionCache] using LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior.artifact_behavior

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Artifact
