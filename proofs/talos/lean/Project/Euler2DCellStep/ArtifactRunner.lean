import Project.Euler2DCellStep.Runner
import Project.Euler2DCellStep.ArtifactTranslation

namespace Project.Euler2DCellStep.Artifact
open Wasm.Binary

/-- The exact embedded cell bytes carry the generic repeated-step contract. -/
theorem artifact_runner_exact_safe :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧ validate raw = .ok validated ∧
      CoreValid raw ∧ Runner.RunnerSpecFor validated.toTalos :=
  artifact_correct_of Runner.RunnerSpecFor Runner.runner_wat_exact_safe

#print axioms artifact_runner_exact_safe
end Project.Euler2DCellStep.Artifact
