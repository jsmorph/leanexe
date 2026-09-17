import Project.WGSL.AccumulationError

namespace Project.WGSL.Binary32

open LeanExe.WGSL CodeLib.IEEE32

/-- Numerical result for the exact parsed artifact under any profile admitted
by its execution theorem. DotDomain explicitly rules out exceptional results
and reserves the range needed by every separate or fused iteration. -/
theorem artifact_numerical {source p} (artifact : DispatchArtifact source semantics p)
    (input : Dispatch.Input) (output : WordBuffer)
    (hb : input.buffers.Valid artifact.kernel.ast.config)
    (run : (Dispatch.model semantics).Exec p artifact.kernel input output)
    {row col : Nat} (hr : row < artifact.kernel.ast.config.rows)
    (hc : col < artifact.kernel.ast.config.cols) {budget : ℝ}
    (domain : DotDomain artifact.kernel.ast.config input.buffers.a input.buffers.b row col budget) :
    let word := output (row * artifact.kernel.ast.config.cols + col)
    Finite word ∧
      |value word - realDot artifact.kernel.ast.config input.buffers.a input.buffers.b
        row col artifact.kernel.ast.config.inner| ≤
          2 * artifact.kernel.ast.config.inner * arithmeticEpsilon := by
  have computation := artifact.execution.corresponds input output hb run row col hr hc
  have numerical := dot_error domain computation (Nat.le_refl _)
  exact ⟨numerical.1, numerical.2.2⟩

/-- A simple sufficient range budget for up to 2^20 products: each exact
product has magnitude at most 1/(4K), and every input has magnitude at most one.
The main theorem also accepts other budgets through DotDomain. -/
theorem standard_budget (inner : Nat) (positive : 0 < inner) (small : inner ≤ 1048576) :
    (0 : ℝ) ≤ 1 / (4 * inner) ∧
      1 / (4 * (inner : ℝ)) + arithmeticEpsilon ≤ 1 ∧
      inner * (1 / (4 * (inner : ℝ)) + 2 * arithmeticEpsilon) ≤ 1 := by
  have hk : (1 : ℝ) ≤ inner := by exact_mod_cast positive
  have hk' : (inner : ℝ) ≤ 1048576 := by exact_mod_cast small
  have hp : (0 : ℝ) < inner := by linarith
  have hq : 1 / (4 * (inner : ℝ)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  refine ⟨by positivity, ?_, ?_⟩
  · norm_num [arithmeticEpsilon] at *
    linarith
  · have cancel : (inner : ℝ) * (1 / (4 * inner)) = 1 / 4 := by field_simp
    rw [mul_add, cancel]
    norm_num [arithmeticEpsilon]
    linarith

#print axioms artifact_numerical
#print axioms standard_budget

end Project.WGSL.Binary32
