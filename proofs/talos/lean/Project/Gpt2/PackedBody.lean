import Project.Gpt2.BodyCompile
import LeanExe.WGSL.Gpt2Packed
import Project.Gpt2LinearRows.Source
import Project.Gpt2CachedStep.Vocabulary.Source
import Project.ProofKit.PackedSource

/-! Exact connection to the parent's public packed FP32 source. No magnitude
assumptions and no real-number approximation are used. These source/view
lemmas do not claim correctness of an external host or a changed Wasm module. -/
namespace Project.Gpt2.PackedBody
open LeanExe.WGSL Project.WGSL Project.ProofKit LeanExe.Models.Gpt2

def sourceArithmetic : ScalarArithmetic :=
  ⟨LeanExe.Float32.addBits, LeanExe.Float32.mulBits⟩

theorem sourceArithmetic_eq : sourceArithmetic = Binary32.arithmetic := by
  have ha : LeanExe.Float32.addBits = Wasm.IEEE32.add := funext fun a => funext fun b => F32Add.add_eq a b
  have hm : LeanExe.Float32.mulBits = Wasm.IEEE32.mul := funext fun a => funext fun b => F32Mul.mul_eq a b
  simp only [sourceArithmetic, Binary32.arithmetic, ha, hm]

theorem fold_eq_range (count : Nat) (initial : UInt32) (step : Nat → UInt32 → UInt32) :
    Source.fold count initial step = (List.range count).foldl (fun acc k => step k acc) initial := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih]
    rfl

/-- Matrix words followed by bias words, including the actual parent offsets. -/
def matrixBiasView (weights : ByteArray) (weightOffset biasOffset inner cols : Nat) : WordBuffer :=
  fun index => if index < inner * cols then word weights (weightOffset + index)
    else word weights (biasOffset + (index - inner * cols))

theorem matrixBiasView_matrix (weights : ByteArray) (weightOffset biasOffset inner cols k col : Nat)
    (hk : k < inner) (hc : col < cols) :
    matrixBiasView weights weightOffset biasOffset inner cols (k * cols + col) =
      word weights (weightOffset + k * cols + col) := by
  have hi : k * cols + col < inner * cols := calc
    _ < k * cols + cols := Nat.add_lt_add_left hc _
    _ = (k + 1) * cols := by simp [Nat.add_mul]
    _ ≤ inner * cols := Nat.mul_le_mul_right cols (by omega)
  simp [matrixBiasView, hi, Nat.add_assoc]

theorem matrixBiasView_bias (weights : ByteArray) (weightOffset biasOffset inner cols col : Nat) :
    matrixBiasView weights weightOffset biasOffset inner cols (inner * cols + col) =
      word weights (biasOffset + col) := by
  simp [matrixBiasView]

/-- In every parent block the bias follows its matrix immediately, so the
GPU B buffer can be one contiguous slice of the parent weight bytes. -/
theorem matrixBiasView_contiguous (weights : ByteArray) (weightOffset inner cols index : Nat) :
    matrixBiasView weights weightOffset (weightOffset + inner * cols) inner cols index =
      word weights (weightOffset + index) := by
  unfold matrixBiasView
  split
  · rfl
  · congr 1
    omega

theorem fold_eq_dotPrefix (weights input : ByteArray)
    (weightOffset biasOffset inner cols row col count : Nat) (hn : count ≤ inner) (hc : col < cols) :
    Source.fold count 0 (fun k acc => Binary32.arithmetic.add acc
      (Binary32.arithmetic.mul (word input (row * inner + k))
        (matrixBiasView weights weightOffset biasOffset inner cols (k * cols + col)))) =
      Project.Gpt2LinearRows.dotPrefix weights input weightOffset inner cols row col count := by
  induction count with
  | zero => rfl
  | succ k ih =>
    change Wasm.IEEE32.add
      (Source.fold k 0 (fun k acc => Binary32.arithmetic.add acc
        (Binary32.arithmetic.mul (word input (row * inner + k))
          (matrixBiasView weights weightOffset biasOffset inner cols (k * cols + col))))) _ = _
    rw [ih (by omega), matrixBiasView_matrix weights weightOffset biasOffset inner cols k col (by omega) hc,
      Project.Gpt2LinearRows.dotPrefix_succ]
    rfl

theorem biased_eq_value (weights input : ByteArray)
    (weightOffset biasOffset inner cols row col : Nat) (hc : col < cols) :
    Gpt2Packed.biased inner cols Binary32.arithmetic
      (fun k => word input (row * inner + k))
      (matrixBiasView weights weightOffset biasOffset inner cols) 0 col =
      Project.Gpt2LinearRows.value weights input weightOffset biasOffset inner cols row col := by
  unfold Gpt2Packed.biased LeanExe.WGSL.Gpt2.dense
  rw [fold_eq_dotPrefix weights input weightOffset biasOffset inner cols row col inner (by rfl) hc,
    matrixBiasView_bias]
  rfl

/-- Only the values at emitted indices matter to a packed generator. -/
theorem generate_congr (count : Nat) (f g : Nat → UInt32) (h : ∀ i, i < count → f i = g i) :
    LeanExe.Packed.generateUInt32LE count f = LeanExe.Packed.generateUInt32LE count g := by
  rw [PackedSource.generate_eq_wordPrefix, PackedSource.generate_eq_wordPrefix]
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [PackedSource.wordPrefix_succ, PackedSource.wordPrefix_succ,
      ih (fun i hi => h i (by omega)), h n (by omega)]

theorem biased_packed_eq_linearRows (weights input : ByteArray)
    (weightOffset biasOffset inner cols : Nat) :
    LeanExe.Packed.generateUInt32LE cols (fun col =>
      Gpt2Packed.biased inner cols Binary32.arithmetic (word input)
        (matrixBiasView weights weightOffset biasOffset inner cols) 0 col) =
      linearRows weights input weightOffset biasOffset inner cols 1 := by
  rw [Project.Gpt2LinearRows.linearRows_eq, Nat.one_mul]
  apply generate_congr
  intro col hc
  simpa only [Nat.div_eq_of_lt hc, Nat.mod_eq_of_lt hc, Nat.zero_mul, Nat.zero_add] using
    biased_eq_value weights input weightOffset biasOffset inner cols 0 col hc

theorem vocabulary_column_eq (weights input : ByteArray) (token count : Nat) :
    MatrixView.columnAccum Binary32.arithmetic (word input) (Matrix.vocabularyWeights (word weights)) token count =
      Project.Gpt2CachedStep.Vocabulary.dotPrefix weights input token count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [Project.Gpt2CachedStep.Vocabulary.dotPrefix_succ]
    change Wasm.IEEE32.add _ _ = _
    rw [ih]
    rfl

theorem vocabulary_packed_eq (weights input : ByteArray) :
    LeanExe.Packed.generateUInt32LE 50257 (Matrix.vocabulary (word input) (word weights)) =
      vocabularyHead weights input := by
  rw [Project.Gpt2CachedStep.Vocabulary.vocabularyHead_eq]
  apply generate_congr
  intro token _
  unfold Matrix.vocabulary
  exact vocabulary_column_eq weights input token 768

def matrixBiasBytes (weights : ByteArray) (weightOffset biasOffset inner cols : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (inner * cols + cols)
    (matrixBiasView weights weightOffset biasOffset inner cols)

theorem matrixBiasBytes_read (weights : ByteArray) (weightOffset biasOffset inner cols index : Nat)
    (hi : index < inner * cols + cols) :
    word (matrixBiasBytes weights weightOffset biasOffset inner cols) index =
      matrixBiasView weights weightOffset biasOffset inner cols index := by
  simpa only [word, matrixBiasBytes, Nat.mul_comm index 4] using
    PackedSource.generate_read (inner * cols + cols) _ index hi

/-- The two vocabulary inputs are packed transposed column slices of the
same vocabulary-major embedding bytes used by the parent. -/
def vocabularyInput (weights : ByteArray) (start cols : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (768 * cols)
    (MatrixView.packed cols (MatrixView.slice (Matrix.vocabularyWeights (word weights)) start))

theorem vocabularyInput_read (weights : ByteArray) (start cols k col : Nat)
    (hk : k < 768) (hc : col < cols) :
    word (vocabularyInput weights start cols) (k * cols + col) =
      word weights ((start + col) * 768 + k) := by
  have hi : k * cols + col < 768 * cols := calc
    _ < k * cols + cols := Nat.add_lt_add_left hc _
    _ = (k + 1) * cols := by simp [Nat.add_mul]
    _ ≤ 768 * cols := Nat.mul_le_mul_right cols (by omega)
  unfold word vocabularyInput
  rw [Nat.mul_comm (k * cols + col) 4, PackedSource.generate_read _ _ _ hi,
    MatrixView.packed_at _ _ k col hc]
  rfl

#print axioms sourceArithmetic_eq
#print axioms fold_eq_range
#print axioms biased_packed_eq_linearRows
#print axioms vocabulary_packed_eq
#print axioms matrixBiasBytes_read
#print axioms vocabularyInput_read

end Project.Gpt2.PackedBody
