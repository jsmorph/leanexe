import Project.Gpt2.PackedBody

/-! Application of actual body-compiler shader certificates to the parent's
packed functions. The modeled invocations return the parent words at the
correct addresses, and serializing those results returns the parent bytes. -/
namespace Project.Gpt2.PackedBody
open LeanExe.WGSL Project.WGSL LeanExe.Models.Gpt2

def biasedColumn (text : String) (weights input : ByteArray)
    (weightOffset biasOffset inner cols col : Nat) :=
  Statement.runShader text Binary32.arithmetic
    ⟨word input, matrixBiasView weights weightOffset biasOffset inner cols,
      inner, inner * cols + cols⟩ cols 0 (UInt32.ofNat col)

theorem biasedColumn_exact (text : String) (inner cols : Nat)
    (checked : Statement.Implements text ⟨1, cols, inner, inner * cols + cols⟩
      (Gpt2Packed.biased inner cols))
    (weights input : ByteArray) (weightOffset biasOffset col : Nat)
    (hc : col < cols) (hcols : cols < 4294967296) :
    biasedColumn text weights input weightOffset biasOffset inner cols col =
      .ok (some ⟨col, Project.Gpt2LinearRows.value weights input weightOffset biasOffset inner cols 0 col⟩) := by
  have hw : (UInt32.ofNat col).toNat = col :=
    UInt32.toNat_ofNat_of_lt' (by change col < 4294967296; omega)
  have h := checked Binary32.arithmetic
    ⟨word input, matrixBiasView weights weightOffset biasOffset inner cols,
      inner, inner * cols + cols⟩ cols 0 (UInt32.ofNat col) (by rfl) (by rfl) (by simp)
  have source : Gpt2Packed.biased inner cols Binary32.arithmetic (word input)
      (matrixBiasView weights weightOffset biasOffset inner cols) 0 col =
      Project.Gpt2LinearRows.value weights input weightOffset biasOffset inner cols 0 col := by
    simpa only [Nat.zero_mul, Nat.zero_add] using
      biased_eq_value weights input weightOffset biasOffset inner cols 0 col hc
  simpa [biasedColumn, Statement.expected, hw, hc, source] using h

/-- Projection used only after proving each active invocation succeeds. The
default value makes this total; `biasedColumn_exact` rules it out on every
serialized column, rather than assuming successful shader results. -/
def returnedWord : Except Statement.ShaderError (Option Statement.Write) → UInt32
  | .ok (some output) => output.value
  | _ => 0

def biasedBytes (text : String) (weights input : ByteArray)
    (weightOffset biasOffset inner cols : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE cols fun col =>
    returnedWord (biasedColumn text weights input weightOffset biasOffset inner cols col)

theorem biasedBytes_exact (text : String) (inner cols : Nat)
    (checked : Statement.Implements text ⟨1, cols, inner, inner * cols + cols⟩
      (Gpt2Packed.biased inner cols))
    (weights input : ByteArray) (weightOffset biasOffset : Nat) (hcols : cols < 4294967296) :
    biasedBytes text weights input weightOffset biasOffset inner cols =
      linearRows weights input weightOffset biasOffset inner cols 1 := by
  rw [Project.Gpt2LinearRows.linearRows_eq, Nat.one_mul]
  apply generate_congr
  intro col hc
  rw [biasedColumn_exact text inner cols checked weights input weightOffset biasOffset col hc hcols]
  simp only [returnedWord, Nat.div_eq_of_lt hc, Nat.mod_eq_of_lt hc]

def vocabularyBytes (leftText rightText : String) (weights input : ByteArray) : ByteArray :=
  LeanExe.Packed.generateUInt32LE 50257 fun token =>
    returnedWord (Matrix.vocabularyBodyRun leftText rightText (word input) (word weights) token)

theorem vocabularyBytes_exact (leftText rightText : String)
    (leftChecked : Statement.Implements leftText ⟨1, 25129, 768, 768 * 25129⟩ Matrix.Shader.vocabularyLeft.body)
    (rightChecked : Statement.Implements rightText ⟨1, 25128, 768, 768 * 25128⟩ Matrix.Shader.vocabularyRight.body)
    (weights input : ByteArray) :
    vocabularyBytes leftText rightText weights input = vocabularyHead weights input := by
  rw [← vocabulary_packed_eq]
  apply generate_congr
  intro token ht
  rw [Matrix.vocabulary_from_body_shaders leftText rightText leftChecked rightChecked _ _ token ht]
  rfl

#print axioms biasedColumn_exact
#print axioms biasedBytes_exact
#print axioms vocabularyBytes_exact

end Project.Gpt2.PackedBody
