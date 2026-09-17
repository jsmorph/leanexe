import Project.WGSL.MatrixView

/-! The GPT-2 dense products at the binary32 WGSL boundary. The input words
are after conversion to binary32; the output words are before conversion back
to binary64. Neither conversion nor the complete model controller is assumed
to have been verified by these theorems. -/
namespace Project.Gpt2.Matrix
open LeanExe.WGSL Project.WGSL Project.WGSL.MatrixView

inductive Shader where
  | qkv | attention | expansion | projection | vocabularyLeft | vocabularyRight
  deriving DecidableEq, Repr

def Shader.index : Shader → Nat
  | .qkv => 0 | .attention => 1 | .expansion => 2 | .projection => 3
  | .vocabularyLeft => 4 | .vocabularyRight => 5

def Shader.config : Shader → GemmConfig
  | .qkv => { rows := 1, cols := 2304, inner := 768 }
  | .attention => { rows := 1, cols := 768, inner := 768 }
  | .expansion => { rows := 1, cols := 3072, inner := 768 }
  | .projection => { rows := 1, cols := 768, inner := 3072 }
  | .vocabularyLeft => { rows := 1, cols := 25129, inner := 768 }
  | .vocabularyRight => { rows := 1, cols := 25128, inner := 768 }

theorem Shader.one_row (shader : Shader) : shader.config.rows = 1 := by cases shader <;> rfl
theorem Shader.valid (shader : Shader) : shader.config.Valid := by cases shader <;> decide +kernel

/-- The Lean specification of each dense product, before bias/activation. -/
def product (shader : Shader) (x : WordBuffer) (weights : MatrixView.Matrix) (col : Nat) : UInt32 :=
  columnAccum Binary32.arithmetic x weights col shader.config.inner

theorem from_dispatch {source metadata} (package : Binary32.Package source metadata)
    (shader : Shader) (shape : package.kernel.ast.config = shader.config)
    (x : WordBuffer) (weights : MatrixView.Matrix) (output : WordBuffer)
    (run : (Dispatch.model Binary32.semantics).Exec package.tag.profile package.kernel
      (input shader.config x weights) output)
    {col : Nat} (hc : col < shader.config.cols) :
    ColumnRun Binary32.semantics package.tag.profile x weights col shader.config.inner (output col) := by
  have hrun : (Dispatch.model Binary32.semantics).Exec package.tag.profile package.kernel
      (input package.kernel.ast.config x weights) output := by simpa only [shape] using run
  have h := MatrixView.from_dispatch package (by rw [shape]; exact shader.one_row)
    x weights output hrun (by simpa only [shape] using hc)
  simpa only [shape] using h

theorem exact_from_dispatch {source metadata} (package : Binary32.Package source metadata)
    (shader : Shader) (shape : package.kernel.ast.config = shader.config)
    (separate : package.tag = .separate)
    (x : WordBuffer) (weights : MatrixView.Matrix) (output : WordBuffer)
    (run : (Dispatch.model Binary32.semantics).Exec package.tag.profile package.kernel
      (input shader.config x weights) output)
    {col : Nat} (hc : col < shader.config.cols) : output col = product shader x weights col := by
  have h := from_dispatch package shader shape x weights output run hc
  rw [separate] at h
  exact h.exact Binary32.separate

/-- Embedding storage is vocabulary-major; projection storage is its transpose. -/
def vocabularyWeights (embedding : WordBuffer) : MatrixView.Matrix :=
  fun k token => embedding (token * 768 + k)

def vocabulary (x embedding : WordBuffer) (token : Nat) : UInt32 :=
  columnAccum Binary32.arithmetic x (vocabularyWeights embedding) token 768

theorem vocabulary_left_layout (embedding : WordBuffer) {k col : Nat} (hc : col < 25129) :
    packed 25129 (slice (vocabularyWeights embedding) 0) (k * 25129 + col) =
      embedding (col * 768 + k) := by
  rw [packed_at _ _ _ _ hc]
  simp [slice, vocabularyWeights]

theorem vocabulary_right_layout (embedding : WordBuffer) {k col : Nat} (hc : col < 25128) :
    packed 25128 (slice (vocabularyWeights embedding) 25129) (k * 25128 + col) =
      embedding ((25129 + col) * 768 + k) := by
  rw [packed_at _ _ _ _ hc]
  rfl

/-- The two dispatches may make different allowed arithmetic choices. Joining
their outputs still gives the declared vocabulary algorithm under that profile. -/
theorem vocabulary_from_dispatch {sourceL metadataL sourceR metadataR}
    (leftPackage : Binary32.Package sourceL metadataL)
    (rightPackage : Binary32.Package sourceR metadataR)
    (leftShape : leftPackage.kernel.ast.config = Shader.vocabularyLeft.config)
    (rightShape : rightPackage.kernel.ast.config = Shader.vocabularyRight.config)
    (profile : rightPackage.tag = leftPackage.tag)
    (x embedding left right : WordBuffer)
    (leftRun : (Dispatch.model Binary32.semantics).Exec leftPackage.tag.profile leftPackage.kernel
      (input Shader.vocabularyLeft.config x (slice (vocabularyWeights embedding) 0)) left)
    (rightRun : (Dispatch.model Binary32.semantics).Exec rightPackage.tag.profile rightPackage.kernel
      (input Shader.vocabularyRight.config x (slice (vocabularyWeights embedding) 25129)) right)
    {token : Nat} (ht : token < 50257) :
    ColumnRun Binary32.semantics leftPackage.tag.profile x (vocabularyWeights embedding)
      token 768 (join 25129 left right token) := by
  apply join_runs (leftSize := 25129) (rightSize := 25128) (inner := 768) ?_ ?_ ht
  · intro col hc
    exact from_dispatch leftPackage .vocabularyLeft leftShape x _ left leftRun hc
  · intro col hc
    have h := from_dispatch rightPackage .vocabularyRight rightShape x _ right rightRun hc
    simpa only [profile, Shader.config] using h

theorem vocabulary_exact {sourceL metadataL sourceR metadataR}
    (leftPackage : Binary32.Package sourceL metadataL)
    (rightPackage : Binary32.Package sourceR metadataR)
    (leftShape : leftPackage.kernel.ast.config = Shader.vocabularyLeft.config)
    (rightShape : rightPackage.kernel.ast.config = Shader.vocabularyRight.config)
    (leftSeparate : leftPackage.tag = .separate) (rightSeparate : rightPackage.tag = .separate)
    (x embedding left right : WordBuffer)
    (leftRun : (Dispatch.model Binary32.semantics).Exec leftPackage.tag.profile leftPackage.kernel
      (input Shader.vocabularyLeft.config x (slice (vocabularyWeights embedding) 0)) left)
    (rightRun : (Dispatch.model Binary32.semantics).Exec rightPackage.tag.profile rightPackage.kernel
      (input Shader.vocabularyRight.config x (slice (vocabularyWeights embedding) 25129)) right)
    {token : Nat} (ht : token < 50257) :
    join 25129 left right token = vocabulary x embedding token := by
  have h := vocabulary_from_dispatch leftPackage rightPackage leftShape rightShape
    (rightSeparate.trans leftSeparate.symm) x embedding left right leftRun rightRun ht
  rw [leftSeparate] at h
  exact h.exact Binary32.separate

/-- Matrix-buffer numbering shared by the layer schedule and native runner. -/
def layerMatrix (layer : Fin 12) (slot : Fin 4) : Nat := layer.val * 4 + slot.val

def nativeShape (matrix : Nat) : Nat := if matrix < 48 then matrix % 4 else matrix - 44

theorem layer_shape (layer : Fin 12) (slot : Fin 4) :
    nativeShape (layerMatrix layer slot) = slot.val := by
  have hl := layer.isLt
  have hs := slot.isLt
  have h : layerMatrix layer slot < 48 := by unfold layerMatrix; omega
  unfold nativeShape
  rw [ite_eq_left h]
  simp [layerMatrix, Nat.mod_eq_of_lt hs]

theorem layer_matrix_injective (l₁ l₂ : Fin 12) (s₁ s₂ : Fin 4)
    (h : layerMatrix l₁ s₁ = layerMatrix l₂ s₂) : l₁ = l₂ ∧ s₁ = s₂ := by
  have hi := Index.linear_injective s₁.isLt s₂.isLt h
  exact ⟨Fin.ext hi.1, Fin.ext hi.2⟩

theorem head_shapes : nativeShape 48 = Shader.vocabularyLeft.index ∧
    nativeShape 49 = Shader.vocabularyRight.index := by decide +kernel

theorem fifty_matrices (matrix : Fin 50) :
    (∃ (layer : Fin 12) (slot : Fin 4), matrix.val = layerMatrix layer slot) ∨
      matrix.val = 48 ∨ matrix.val = 49 := by
  by_cases h : matrix.val < 48
  · have hl : matrix.val / 4 < 12 := by omega
    have hs : matrix.val % 4 < 4 := Nat.mod_lt _ (by decide)
    refine Or.inl ⟨⟨matrix.val / 4, hl⟩, ⟨matrix.val % 4, hs⟩, ?_⟩
    simpa only [layerMatrix, Nat.mul_comm] using (Nat.div_add_mod matrix.val 4).symm
  · have hm := matrix.isLt
    omega

/-- The attention result stores K, then V, then the projected input vector. -/
def attentionInput (attended : WordBuffer) : WordBuffer := fun i => attended (1536 + i)

theorem attention_input_range (i : Fin 768) : 1536 ≤ 1536 + i.val ∧
    1536 + i.val < 2304 := by have h := i.isLt; omega

structure Binding where
  file : String
  shape : Nat
  deriving Lean.ToJson, Lean.FromJson, BEq, Repr

def bindings : List Binding := (List.range 50).map fun index =>
  { file := "matrix-" ++ (if index < 10 then "0" else "") ++ toString index ++ ".bin"
    shape := nativeShape index }

end Project.Gpt2.Matrix
