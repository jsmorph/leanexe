import Project.TinyGpt2Hidden.ArtifactTranslation
import Project.TinyGpt2Hidden.Spec
import Project.WGSL.GptHeadCheckpoint

namespace Project.WGSL.GptHiddenArtifact
open Wasm Wasm.Binary Project.ProofKit Project.TinyGpt2 Project.WGSL.GptHeadCheckpoint

theorem interface :
    (Project.TinyGpt2Hidden.Artifact.Cache.raw.exports.any fun entry =>
      entry.name.text == "hidden" && entry.desc == .func 74) = true := by decide +kernel

/-- Exact binary parsing, static validity and execution for the checkpoint's
hidden row. Input memory contains the exact checkpoint words. -/
theorem exact (env : HostEnv Unit) (initial : Store Unit) (pointer : UInt64)
    (tokens : Real.Tokens) (input : UInt64Array.At initial pointer Checkpoint.words) :
    ∃ raw checked,
      decode Project.TinyGpt2Hidden.Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok checked ∧ CoreValid raw ∧
      TerminatesWith env checked.toTalos 74 initial
        [.i64 3, .i64 (GptHeadCheckpoint.tokenWords tokens 3),
          .i64 (GptHeadCheckpoint.tokenWords tokens 2), .i64 (GptHeadCheckpoint.tokenWords tokens 1),
          .i64 (GptHeadCheckpoint.tokenWords tokens 0), .i64 pointer]
        (fun final values => final = initial ∧ values = Project.TinyGpt2Hidden.Spec.rowResults (computedHidden tokens)) := by
  refine Project.TinyGpt2Hidden.Artifact.artifact_correct_of
    (fun module_ => TerminatesWith env module_ 74 initial
      [.i64 3, .i64 (GptHeadCheckpoint.tokenWords tokens 3),
        .i64 (GptHeadCheckpoint.tokenWords tokens 2), .i64 (GptHeadCheckpoint.tokenWords tokens 1),
        .i64 (GptHeadCheckpoint.tokenWords tokens 0), .i64 pointer]
      (fun final values => final = initial ∧
        values = Project.TinyGpt2Hidden.Spec.rowResults (computedHidden tokens))) ?_
  exact Project.TinyGpt2Hidden.Spec.hidden_exact env initial pointer Checkpoint.words
    _ _ _ _ 3 input (by simpa only [Checkpoint.words_size] using (Nat.le_refl 2488))
    (tokens_valid tokens 0) (tokens_valid tokens 1) (tokens_valid tokens 2) (tokens_valid tokens 3)

#print axioms interface
#print axioms exact
end Project.WGSL.GptHiddenArtifact
