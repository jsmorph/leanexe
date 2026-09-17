import Project.TinyGpt2.CheckpointBounds
import Project.TinyGpt2.Decoding
import Project.ProofKit.F64Rational

namespace Project.TinyGpt2.Checkpoint
open Project.ProofKit CodeLib.IEEE64

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem norm1_scale (i : Fin 4) : |(decodeNorm words 2464).scale i| ≤ 13/10 := by
  have h : |F64Rational.decode words[2464+i.val]!| ≤ 13/10 := by
    fin_cases i <;> decide +kernel
  simpa [decodeNorm, decodeRow, loadRow_words] using F64Rational.magnitude _ _ h

theorem norm1_bias (i : Fin 4) : |(decodeNorm words 2464).bias i| ≤ 1/5 := by
  have h : |F64Rational.decode words[2468+i.val]!| ≤ 1/5 := by
    fin_cases i <;> decide +kernel
  simpa [decodeNorm, decodeRow, loadRow_words] using F64Rational.magnitude _ _ h

theorem query_bound (i j : Fin 4) : |decodeMatrix words 1040 4 4 i j| ≤ 6/5 := by
  have h : |F64Rational.decode (matrixWords words 1040 4 4 i j)| ≤ 6/5 := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  simpa [decodeMatrix] using F64Rational.magnitude _ _ h

theorem key_bound (i j : Fin 4) : |decodeMatrix words 1056 4 4 i j| ≤ 6/5 := by
  have h : |F64Rational.decode (matrixWords words 1056 4 4 i j)| ≤ 6/5 := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  simpa [decodeMatrix] using F64Rational.magnitude _ _ h

theorem value_bound (i j : Fin 4) : |decodeMatrix words 1072 4 4 i j| ≤ 6/5 := by
  have h : |F64Rational.decode (matrixWords words 1072 4 4 i j)| ≤ 6/5 := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  simpa [decodeMatrix] using F64Rational.magnitude _ _ h

theorem attention_bound (i j : Fin 4) : |decodeMatrix words 1088 4 4 i j| ≤ 1 := by
  have h : |F64Rational.decode (matrixWords words 1088 4 4 i j)| ≤ 1 := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  simpa [decodeMatrix] using F64Rational.magnitude _ _ h

theorem loaded_valid (offset : Nat) (ho : offset+3 < words.size) :
    LayerNorm.ValidRow (rowWords (loadRow words offset)) := by
  intro i
  rw [loadRow_words]
  have hi : offset+i.val < words.size := by omega
  simpa only [getElem!_pos, hi] using word_bounded _ hi

#print axioms norm1_scale
#print axioms query_bound
end Project.TinyGpt2.Checkpoint
