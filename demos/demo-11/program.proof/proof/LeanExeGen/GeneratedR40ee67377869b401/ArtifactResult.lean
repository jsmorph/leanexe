import LeanExeGen.GeneratedR40ee67377869b401.ArtifactTranslation
import LeanExeGen.GeneratedR40ee67377869b401.FormalSpec
import LeanExeGen.GeneratedR40ee67377869b401.Behavior

namespace LeanExeGen.GeneratedR40ee67377869b401.Artifact

open Wasm.Binary

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.GeneratedR40ee67377869b401.FormalSpec.ArtifactSpec validated.toTalos := by
  apply artifact_correct_of LeanExeGen.GeneratedR40ee67377869b401.FormalSpec.ArtifactSpec
  simpa [executionCache] using LeanExeGen.GeneratedR40ee67377869b401.Behavior.artifact_behavior

end LeanExeGen.GeneratedR40ee67377869b401.Artifact
