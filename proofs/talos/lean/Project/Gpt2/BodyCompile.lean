import Project.Gpt2.Matrix
import LeanExe.WGSL.Gpt2

/-! Connection between the body-compiled products and the existing GPT-2
matrix specification. No real numbers, tolerances or parameter bounds. -/
namespace Project.Gpt2.Matrix
open LeanExe.WGSL Project.WGSL Project.WGSL.MatrixView

def Shader.body : Shader → Source.Kernel
  | .qkv => LeanExe.WGSL.Gpt2.qkv
  | .attention => LeanExe.WGSL.Gpt2.attention
  | .expansion => LeanExe.WGSL.Gpt2.expansion
  | .projection => LeanExe.WGSL.Gpt2.projection
  | .vocabularyLeft => LeanExe.WGSL.Gpt2.vocabularyLeft
  | .vocabularyRight => LeanExe.WGSL.Gpt2.vocabularyRight

theorem dense_eq_column (ar : ScalarArithmetic) (x : WordBuffer) (weights : MatrixView.Matrix)
    (inner cols row col : Nat) (hc : col < cols) :
    LeanExe.WGSL.Gpt2.dense inner cols ar x (packed cols weights) row col =
      columnAccum ar x weights col inner := by
  unfold LeanExe.WGSL.Gpt2.dense
  induction inner with
  | zero => rfl
  | succ k ih =>
      change ar.add (Source.fold k 0 _) (ar.mul (x k) (packed cols weights (k * cols + col))) = _
      rw [ih, packed_at _ _ _ _ hc]
      rfl

theorem body_eq_product (shader : Shader) (x : WordBuffer) (weights : MatrixView.Matrix)
    (row col : Nat) (hc : col < shader.config.cols) :
    shader.body Binary32.arithmetic x (packed shader.config.cols weights) row col =
      product shader x weights col := by
  have shape : shader.body = LeanExe.WGSL.Gpt2.dense shader.config.inner shader.config.cols := by
    cases shader <;> rfl
  rw [shape]
  exact dense_eq_column Binary32.arithmetic x weights _ _ row col hc

/-- Applying any body-compiler certificate to a named GPT-2 role establishes
its existing packed matrix specification at every active column. -/
theorem from_body_shader (shader : Shader) (text : String)
    (checked : Statement.Implements text
      ⟨1, shader.config.cols, shader.config.inner, shader.config.inner * shader.config.cols⟩ shader.body)
    (x : WordBuffer) (weights : MatrixView.Matrix) (col : UInt32)
    (hc : col.toNat < shader.config.cols) :
    Statement.runShader text Binary32.arithmetic
      ⟨x, packed shader.config.cols weights, shader.config.inner, shader.config.inner * shader.config.cols⟩
      shader.config.cols 0 col = .ok (some ⟨col.toNat, product shader x weights col.toNat⟩) := by
  have result := checked Binary32.arithmetic
    ⟨x, packed shader.config.cols weights, shader.config.inner, shader.config.inner * shader.config.cols⟩
    shader.config.cols 0 col (Nat.le_refl _) (Nat.le_refl _) (by simp)
  simpa [Statement.expected, hc, body_eq_product shader x weights 0 col.toNat hc] using result

/-- Execute the invocation for one product column. This uses the body compiler's
statement semantics, independently of the legacy template dispatch model. -/
def bodyColumn (shader : Shader) (text : String) (x : WordBuffer)
    (weights : MatrixView.Matrix) (col : Nat) : Except Statement.ShaderError (Option Statement.Write) :=
  Statement.runShader text Binary32.arithmetic
    ⟨x, packed shader.config.cols weights, shader.config.inner, shader.config.inner * shader.config.cols⟩
    shader.config.cols 0 (UInt32.ofNat col)

theorem bodyColumn_eq (shader : Shader) (text : String)
    (checked : Statement.Implements text
      ⟨1, shader.config.cols, shader.config.inner, shader.config.inner * shader.config.cols⟩ shader.body)
    (x : WordBuffer) (weights : MatrixView.Matrix) (col : Nat) (hc : col < shader.config.cols) :
    bodyColumn shader text x weights col = .ok (some ⟨col, product shader x weights col⟩) := by
  have hcols : shader.config.cols < 4294967296 := by cases shader <;> decide
  have hword : (UInt32.ofNat col).toNat = col :=
    UInt32.toNat_ofNat_of_lt' (by change col < 4294967296; omega)
  simpa only [bodyColumn, hword] using
    from_body_shader shader text checked x weights (UInt32.ofNat col) (by simpa only [hword] using hc)

/-- Read one column of the concatenated vocabulary outputs. The right shader
uses local column numbering; the returned address is shifted by the left size.
This defines the composition being proved, not the external host's scheduling. -/
def vocabularyBodyRun (leftText rightText : String) (x embedding : WordBuffer) (token : Nat) :
    Except Statement.ShaderError (Option Statement.Write) :=
  if token < 25129 then
    bodyColumn .vocabularyLeft leftText x (slice (vocabularyWeights embedding) 0) token
  else
    (bodyColumn .vocabularyRight rightText x (slice (vocabularyWeights embedding) 25129)
      (token - 25129)).map (Option.map fun w => ⟨25129 + w.address, w.value⟩)

/-- Both body-compiler certificates imply the complete 50,257-column
vocabulary specification, including the split point and output addresses. -/
theorem vocabulary_from_body_shaders (leftText rightText : String)
    (leftChecked : Statement.Implements leftText ⟨1, 25129, 768, 768 * 25129⟩ Shader.vocabularyLeft.body)
    (rightChecked : Statement.Implements rightText ⟨1, 25128, 768, 768 * 25128⟩ Shader.vocabularyRight.body)
    (x embedding : WordBuffer) (token : Nat) (ht : token < 50257) :
    vocabularyBodyRun leftText rightText x embedding token =
      .ok (some ⟨token, vocabulary x embedding token⟩) := by
  by_cases hl : token < 25129
  · rw [vocabularyBodyRun, ite_eq_left hl,
        bodyColumn_eq .vocabularyLeft leftText leftChecked x _ token hl]
    simp only [product, Shader.config, columnAccum_slice, Nat.zero_add, vocabulary]
  · have hr : token - 25129 < 25128 := by omega
    have offset : 25129 + (token - 25129) = token := by omega
    rw [vocabularyBodyRun, ite_eq_right hl,
        bodyColumn_eq .vocabularyRight rightText rightChecked x _ (token - 25129) hr]
    simp only [Except.map, Option.map, product, Shader.config, columnAccum_slice, offset, vocabulary]

end Project.Gpt2.Matrix
