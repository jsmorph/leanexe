import Project.Gpt2.Matrix
import Project.WGSL.ArithmeticChoice

namespace Project.Gpt2.Matrix
open LeanExe.WGSL Project.WGSL Project.WGSL.MatrixView

/-- Interpret the same parsed shader with source-ordered fusion choices.
This makes no assertion about the policy selected by a physical GPU. -/
def fusionArtifact {source metadata} (package : Binary32.Package source metadata) :
    DispatchArtifact source Binary32.semantics fusion where
  kernel := package.kernel
  parsed := package.parsed
  execution := Dispatch.execution package.kernel rfl True.intro Binary32.total

theorem fusion_from_dispatch {source metadata} (package : Binary32.Package source metadata)
    (shader : Shader) (shape : package.kernel.ast.config = shader.config)
    (x : WordBuffer) (weights : MatrixView.Matrix) (output : WordBuffer)
    (run : (Dispatch.model Binary32.semantics).Exec fusion package.kernel
      (input shader.config x weights) output)
    {col : Nat} (hc : col < shader.config.cols) :
    ∃ choices, output col = ArithmeticChoice.evaluate choices x weights col shader.config.inner := by
  have valid : (input shader.config x weights).buffers.Valid package.kernel.ast.config := by
    rw [shape]
    exact input_valid _ x weights
  have hr : 0 < package.kernel.ast.config.rows := by rw [shape, shader.one_row]; decide
  have hcol : col < package.kernel.ast.config.cols := by simpa only [shape] using hc
  have h := (fusionArtifact package).execution.corresponds _ output valid run 0 col hr hcol
  have hrun : Dot Binary32.semantics fusion shader.config x (packed shader.config.cols weights)
      0 col shader.config.inner (output col) := by
    simpa only [fusionArtifact, shape, input, Nat.zero_mul, Nat.zero_add] using h
  exact ArithmeticChoice.fusion_iff_choices.mp ((packed_run_iff hc).mp hrun)

/-- Every vocabulary word has its own concrete sequence of arithmetic choices;
the split does not impose a shared sequence on unrelated output invocations. -/
theorem vocabulary_fusion_choices {x embedding left right : WordBuffer}
    (hl : ∀ col, col < 25129 → ColumnRun Binary32.semantics fusion x
      (slice (vocabularyWeights embedding) 0) col 768 (left col))
    (hr : ∀ col, col < 25128 → ColumnRun Binary32.semantics fusion x
      (slice (vocabularyWeights embedding) 25129) col 768 (right col))
    {token : Nat} (ht : token < 50257) :
    ∃ choices, join 25129 left right token =
      ArithmeticChoice.evaluate choices x (vocabularyWeights embedding) token 768 :=
  ArithmeticChoice.fusion_iff_choices.mp
    (join_runs (leftSize := 25129) (rightSize := 25128) hl hr ht)

end Project.Gpt2.Matrix
