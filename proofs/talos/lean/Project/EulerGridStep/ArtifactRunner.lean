import Project.EulerGridStep.FrozenRunnerExecution
import Project.EulerGridStep.ArtifactTranslation

namespace Project.EulerGridStep.Artifact
open Wasm.Binary

/-- The exact embedded grid bytes carry the generic repeated-step contract. -/
theorem artifact_runner_exact_safe :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧ validate raw = .ok validated ∧
      CoreValid raw ∧ Frozen.Runner.RunnerSpecFor validated.toTalos :=
  artifact_correct_of Frozen.Runner.RunnerSpecFor Frozen.Runner.runner_wat_exact_safe

#print axioms artifact_runner_exact_safe
end Project.EulerGridStep.Artifact
