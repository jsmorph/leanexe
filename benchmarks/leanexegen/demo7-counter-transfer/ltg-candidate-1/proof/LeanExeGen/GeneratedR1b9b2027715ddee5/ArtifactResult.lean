import LeanExeGen.GeneratedR1b9b2027715ddee5.ArtifactTranslation
import LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec
import LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior

namespace LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact

open Wasm.Binary

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.ArtifactSpec validated.toTalos := by
  apply artifact_correct_of LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.ArtifactSpec
  simpa [executionCache] using LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior.artifact_behavior

end LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact
