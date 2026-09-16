import Project.TinyGpt2.CheckpointWords
import Project.TinyGpt2.CenteredProjection
import Project.TinyGpt2.Decoding
import Project.ProofKit.F64Rational

namespace Project.TinyGpt2.Checkpoint
open Project.ProofKit Project.ProofKit.RealNormalization

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def rational (offset : Nat) : ℚ := F64Rational.decode words[offset]!

def scale (i : Fin 4) : ℚ := rational (2464+i.val)
def bias (i : Fin 4) : ℚ := rational (2468+i.val)

def matrix (offset : Nat) (i : Fin 4) (head k : Fin 2) : ℚ :=
  rational (offset+i.val*4+(Real.coordinate head k).val)

def centered (offset : Nat) (head : Fin 2) (i : Fin 4) (k : Fin 2) : ℚ :=
  scale i*matrix offset i head k-(∑ j, scale j*matrix offset j head k)/4

def queryBias (head k : Fin 2) : ℚ := ∑ i, bias i*matrix 1040 i head k

def scoreMatrix (head : Fin 2) (i j : Fin 4) : ℚ :=
  ∑ k, centered 1040 head i k*centered 1056 head j k

def scoreLinear (head : Fin 2) (j : Fin 4) : ℚ :=
  ∑ k, queryBias head k*centered 1056 head j k

theorem matrix_norm (head : Fin 2) : (∑ i, ∑ j, (scoreMatrix head i j)^2) ≤ 144/25 := by
  fin_cases head <;> decide +kernel

theorem linear_norm (head : Fin 2) : (∑ j, (scoreLinear head j)^2) ≤ 49/400 := by
  fin_cases head <;> decide +kernel

theorem centered_cast (offset : Nat) (head : Fin 2) (i : Fin 4) (k : Fin 2) :
    (centered offset head i k : ℝ) =
      Real.centeredHead (decodeNorm words 2464) (decodeMatrix words offset 4 4) head i k := by
  simp [centered, scale, matrix, rational, F64Rational.decode_cast,
    Real.centeredHead, Real.centeredColumn, decodeNorm, decodeRow, decodeMatrix,
    matrixWords, loadRow_words]

theorem queryBias_cast (head k : Fin 2) :
    (queryBias head k : ℝ) = Real.projectedBias (decodeNorm words 2464)
      (decodeMatrix words 1040 4 4) head k := by
  simp [queryBias, bias, matrix, rational, F64Rational.decode_cast,
    Real.projectedBias, decodeNorm, decodeRow, decodeMatrix, matrixWords, loadRow_words]

theorem scoreMatrix_cast (head : Fin 2) (i j : Fin 4) :
    (scoreMatrix head i j : ℝ) = Real.scoreMatrix (parameters words) head i j := by
  simp [scoreMatrix, Real.scoreMatrix, centered_cast, parameters, Layout.norm1, Layout.query, Layout.key]

theorem scoreLinear_cast (head : Fin 2) (j : Fin 4) :
    (scoreLinear head j : ℝ) = Real.scoreLinear (parameters words) head j := by
  simp [scoreLinear, Real.scoreLinear, queryBias_cast, centered_cast,
    parameters, Layout.norm1, Layout.query, Layout.key]

theorem matrix_norm_real (head : Fin 2) :
    (∑ i, sumSquares (Real.scoreMatrix (parameters words) head i)) ≤ 144/25 := by
  have hc : ((∑ i, ∑ j, (scoreMatrix head i j)^2 : ℚ):ℝ) ≤ ((144/25:ℚ):ℝ) :=
    Rat.cast_le.mpr (matrix_norm head)
  simpa [sumSquares, scoreMatrix_cast] using hc

theorem linear_norm_real (head : Fin 2) :
    sumSquares (Real.scoreLinear (parameters words) head) ≤ 49/400 := by
  have hc : ((∑ j, (scoreLinear head j)^2 : ℚ):ℝ) ≤ ((49/400:ℚ):ℝ) :=
    Rat.cast_le.mpr (linear_norm head)
  simpa [sumSquares, scoreLinear_cast] using hc

theorem row_attention_spread (x y v : Real.Row) (head : Fin 2) :
    |Real.rowScore (parameters words) x y head-
      Real.rowScore (parameters words) x v head| ≤ 103/7 :=
  Real.row_score_spread_bound _ x y v head (matrix_norm_real head) (linear_norm_real head)

theorem attention_spread (tokens : Real.Tokens) (i : Fin 4) (head : Fin 2) (j l : Fin 4) :
    |Real.score (parameters words) tokens i head j-
      Real.score (parameters words) tokens i head l| ≤ 103/7 :=
  Real.score_spread_bound _ tokens i head (matrix_norm_real head) (linear_norm_real head) j l

#print axioms row_attention_spread
#print axioms attention_spread
end Project.TinyGpt2.Checkpoint
