import Project.WGSL.ExecutionPackage
import Project.WGSL.ArtifactNumerical

namespace Project.WGSL.Binary32

open LeanExe.WGSL CodeLib.IEEE32

theorem Package.numerical {source metadata} (package : Package source metadata)
    (input : Dispatch.Input) (output : WordBuffer)
    (hb : input.buffers.Valid package.kernel.ast.config)
    (run : (Dispatch.model semantics).Exec package.tag.profile package.kernel input output)
    {row col : Nat} (hr : row < package.kernel.ast.config.rows)
    (hc : col < package.kernel.ast.config.cols) {budget : ℝ}
    (domain : DotDomain package.kernel.ast.config input.buffers.a input.buffers.b row col budget) :
    let word := output (row * package.kernel.ast.config.cols + col)
    Finite word ∧ |value word - realDot package.kernel.ast.config input.buffers.a input.buffers.b
      row col package.kernel.ast.config.inner| ≤
        2 * package.kernel.ast.config.inner * arithmeticEpsilon :=
  artifact_numerical package.artifact input output hb run hr hc domain

theorem Package.numerical_wide {source metadata} (package : Package source metadata)
    (input : Dispatch.Input) (output : WordBuffer)
    (hb : input.buffers.Valid package.kernel.ast.config)
    (run : (Dispatch.model semantics).Exec package.tag.profile package.kernel input output)
    {row col : Nat} (hr : row < package.kernel.ast.config.rows)
    (hc : col < package.kernel.ast.config.cols) {accBudget productBudget : ℝ}
    (domain : WideDotDomain package.kernel.ast.config input.buffers.a input.buffers.b row col accBudget productBudget) :
    let word := output (row * package.kernel.ast.config.cols + col)
    Finite word ∧ |value word - realDot package.kernel.ast.config input.buffers.a input.buffers.b
      row col package.kernel.ast.config.inner| ≤
        package.kernel.ast.config.inner * stepError accBudget productBudget :=
  artifact_numerical_wide package.artifact input output hb run hr hc domain

#print axioms Package.artifact
#print axioms Package.numerical_wide
#print axioms Package.numerical
#print axioms Package.exact

end Project.WGSL.Binary32
