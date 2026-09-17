import Project.WGSL.Precision
import Project.WGSL.WideAccumulationError
import Project.ProofKit.F64AddBounds

namespace Project.WGSL.HeadNumerical
open LeanExe.WGSL Project.ProofKit Binary32

set_option exponentiation.threshold 4096

abbrev Buffer64 := Nat → UInt64

def converted (a : Buffer64) : WordBuffer := fun i => Precision.demote (a i)

def finish (result : UInt32) (bias : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Precision.promote result) bias

noncomputable def realDot64 (config : GemmConfig) (a b : Buffer64) (row col : Nat) : Nat → ℝ
  | 0 => 0
  | k+1 => realDot64 config a b row col k +
      CodeLib.IEEE64.value (a (row*config.inner+k)) * CodeLib.IEEE64.value (b (k*config.cols+col))

structure Inputs (config : GemmConfig) (a b : Buffer64) (row col : Nat) : Prop where
  inner : config.inner = 4
  a : ∀ k, k < 4 → CodeLib.IEEE64.Finite (a (row*config.inner+k)) ∧
    |CodeLib.IEEE64.value (a (row*config.inner+k))| ≤ 7
  b : ∀ k, k < 4 → CodeLib.IEEE64.Finite (b (k*config.cols+col)) ∧
    |CodeLib.IEEE64.value (b (k*config.cols+col))| ≤ 4

theorem demote_bounded {a : UInt64} {bound : ℝ} (ha : CodeLib.IEEE64.Finite a)
    (hb : |CodeLib.IEEE64.value a| ≤ bound) (hmax : bound ≤ 7) :
    CodeLib.IEEE32.Finite (Precision.demote a) ∧
    |CodeLib.IEEE32.value (Precision.demote a)| ≤ bound + 1/2000000 ∧
    |CodeLib.IEEE32.value (Precision.demote a) - CodeLib.IEEE64.value a| ≤ 1/2000000 := by
  have hs := Precision.demote_error a ha (by norm_num at *; linarith)
  have hu : 0 ≤ F32AddBounds.unitRoundoff := by norm_num [F32AddBounds.unitRoundoff]
  have he : |CodeLib.IEEE32.value (Precision.demote a) - CodeLib.IEEE64.value a| ≤ 1/2000000 := by
    have h := mul_le_mul_of_nonneg_left (hb.trans hmax) hu
    norm_num [F32AddBounds.unitRoundoff, F32MulBounds.multiplicationUnderflowEpsilon] at hs h
    linarith [hs.2]
  refine ⟨hs.1, ?_, he⟩
  have ht := abs_sub_le (CodeLib.IEEE32.value (Precision.demote a)) (CodeLib.IEEE64.value a) 0
  simp only [sub_zero] at ht
  linarith

theorem converted_domain {config a b row col} (inputs : Inputs config a b row col) :
    WideDotDomain config (converted a) (converted b) row col 161 40 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · norm_num [F32AddBounds.unitRoundoff, F32MulBounds.multiplicationUnderflowEpsilon]
  · rw [inputs.inner]
    norm_num [stepError, F32AddBounds.unitRoundoff, F32MulBounds.multiplicationUnderflowEpsilon]
  · intro k hk
    have hk' : k < 4 := by simpa [inputs.inner] using hk
    have ha := demote_bounded (inputs.a k hk').1 (inputs.a k hk').2 (by norm_num)
    have hb := demote_bounded (inputs.b k hk').1 (inputs.b k hk').2 (by norm_num)
    refine ⟨ha.1, hb.1, ?_⟩
    change |CodeLib.IEEE32.value (Precision.demote _) * CodeLib.IEEE32.value (Precision.demote _)| ≤ _
    rw [abs_mul]
    have ha8 : |CodeLib.IEEE32.value (Precision.demote (a (row*config.inner+k)))| ≤ 8 := by linarith [ha.2.1]
    have hb5 : |CodeLib.IEEE32.value (Precision.demote (b (k*config.cols+col)))| ≤ 5 := by linarith [hb.2.1]
    nlinarith [mul_le_mul ha8 hb5 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 8)]

theorem product_conversion_error {a b : UInt64}
    (ha : CodeLib.IEEE64.Finite a) (hb : CodeLib.IEEE64.Finite b)
    (ha7 : |CodeLib.IEEE64.value a| ≤ 7) (hb4 : |CodeLib.IEEE64.value b| ≤ 4) :
    |CodeLib.IEEE32.value (Precision.demote a) * CodeLib.IEEE32.value (Precision.demote b) -
      CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| ≤ 6/1000000 := by
  have hca := demote_bounded ha ha7 (by norm_num)
  have hcb := demote_bounded hb hb4 (by norm_num)
  have hb5 : |CodeLib.IEEE32.value (Precision.demote b)| ≤ 5 := by linarith [hcb.2.1]
  have hsplit : CodeLib.IEEE32.value (Precision.demote a) * CodeLib.IEEE32.value (Precision.demote b) -
      CodeLib.IEEE64.value a * CodeLib.IEEE64.value b =
      (CodeLib.IEEE32.value (Precision.demote a) - CodeLib.IEEE64.value a) *
        CodeLib.IEEE32.value (Precision.demote b) + CodeLib.IEEE64.value a *
        (CodeLib.IEEE32.value (Precision.demote b) - CodeLib.IEEE64.value b) := by ring
  rw [hsplit]
  have ht := abs_add_le
    ((CodeLib.IEEE32.value (Precision.demote a) - CodeLib.IEEE64.value a) * CodeLib.IEEE32.value (Precision.demote b))
    (CodeLib.IEEE64.value a * (CodeLib.IEEE32.value (Precision.demote b) - CodeLib.IEEE64.value b))
  simp only [abs_mul] at ht
  have hp1 := mul_le_mul hca.2.2 hb5 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2000000)
  have hp2 := mul_le_mul ha7 hcb.2.2 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 7)
  linarith

theorem dot_conversion_error {config a b row col} (inputs : Inputs config a b row col)
    (k : Nat) (hk : k ≤ 4) :
    |realDot config (converted a) (converted b) row col k - realDot64 config a b row col k| ≤
      k * (6/1000000) := by
  induction k with
  | zero => simp [realDot, realDot64]
  | succ k ih =>
      have hp := product_conversion_error (inputs.a k (by omega)).1 (inputs.b k (by omega)).1
        (inputs.a k (by omega)).2 (inputs.b k (by omega)).2
      have hi := ih (by omega)
      have heq : realDot config (converted a) (converted b) row col (k+1) -
          realDot64 config a b row col (k+1) =
          (realDot config (converted a) (converted b) row col k - realDot64 config a b row col k) +
          (CodeLib.IEEE32.value (Precision.demote (a (row*config.inner+k))) *
            CodeLib.IEEE32.value (Precision.demote (b (k*config.cols+col))) -
            CodeLib.IEEE64.value (a (row*config.inner+k)) * CodeLib.IEEE64.value (b (k*config.cols+col))) := by
        simp only [realDot, realDot64, converted]
        ring
      rw [heq]
      have ht := abs_add_le
        (realDot config (converted a) (converted b) row col k - realDot64 config a b row col k)
        (CodeLib.IEEE32.value (Precision.demote (a (row*config.inner+k))) *
          CodeLib.IEEE32.value (Precision.demote (b (k*config.cols+col))) -
          CodeLib.IEEE64.value (a (row*config.inner+k)) * CodeLib.IEEE64.value (b (k*config.cols+col)))
      push_cast
      linarith

theorem dot_numerical {p config a b row col result} (inputs : Inputs config a b row col)
    (run : Dot semantics p config (converted a) (converted b) row col 4 result) :
    CodeLib.IEEE32.Finite result ∧ |CodeLib.IEEE32.value result| ≤ 161 ∧
    |CodeLib.IEEE32.value result - realDot64 config a b row col 4| ≤ 1/12000 := by
  have hs := dot_error_wide (converted_domain inputs) run (by rw [inputs.inner])
  have hc := dot_conversion_error inputs 4 (by decide)
  have ht := abs_sub_le (CodeLib.IEEE32.value result)
    (realDot config (converted a) (converted b) row col 4) (realDot64 config a b row col 4)
  norm_num [stepError, F32AddBounds.unitRoundoff, F32MulBounds.multiplicationUnderflowEpsilon] at hs hc
  exact ⟨hs.1, by linarith [hs.2.1], by linarith [hs.2.2]⟩

theorem finish_numerical {p config a b row col result bias} (inputs : Inputs config a b row col)
    (run : Dot semantics p config (converted a) (converted b) row col 4 result)
    (hb : CodeLib.IEEE64.Finite bias) (hb4 : |CodeLib.IEEE64.value bias| ≤ 4) :
    CodeLib.IEEE64.Finite (finish result bias) ∧ |CodeLib.IEEE64.value (finish result bias)| ≤ 166 ∧
    |CodeLib.IEEE64.value (finish result bias) - (realDot64 config a b row col 4 + CodeLib.IEEE64.value bias)| ≤
      1/10000 := by
  have hd := dot_numerical inputs run
  have hp := Precision.promote_spec result hd.1
  have hv := Precision.promote_value result hd.1
  have ht := abs_add_le (CodeLib.IEEE64.value (Precision.promote result)) (CodeLib.IEEE64.value bias)
  have hsum : |CodeLib.IEEE64.value (Precision.promote result) + CodeLib.IEEE64.value bias| ≤ 165 := by
    rw [hv] at ht ⊢
    linarith [hd.2.1]
  have ha := F64AddBounds.add_real_relative (Precision.promote result) bias hp.1 hb (by norm_num at *; linarith)
  have hu : 0 ≤ CodeLib.IEEE64.unitRoundoff64 := by norm_num [CodeLib.IEEE64.unitRoundoff64]
  have hround := mul_le_mul_of_nonneg_left hsum hu
  have herr : |CodeLib.IEEE64.value (finish result bias) -
      (CodeLib.IEEE32.value result + CodeLib.IEEE64.value bias)| ≤ 1/1000000000000 := by
    rw [hv] at ha hround
    norm_num [CodeLib.IEEE64.unitRoundoff64] at ha hround
    change |CodeLib.IEEE64.value (Wasm.IEEE64.add _ _) - _| ≤ _
    linarith [ha.2]
  refine ⟨ha.1, ?_, ?_⟩
  · have ht := abs_sub_le (CodeLib.IEEE64.value (finish result bias))
      (CodeLib.IEEE32.value result + CodeLib.IEEE64.value bias) 0
    simp only [sub_zero] at ht
    rw [hv] at hsum
    linarith
  · have ht := abs_sub_le (CodeLib.IEEE64.value (finish result bias))
      (CodeLib.IEEE32.value result + CodeLib.IEEE64.value bias)
      (realDot64 config a b row col 4 + CodeLib.IEEE64.value bias)
    have heq : CodeLib.IEEE32.value result + CodeLib.IEEE64.value bias -
        (realDot64 config a b row col 4 + CodeLib.IEEE64.value bias) =
        CodeLib.IEEE32.value result - realDot64 config a b row col 4 := by ring
    rw [heq] at ht
    linarith [hd.2.2]

#print axioms dot_numerical
#print axioms finish_numerical
end Project.WGSL.HeadNumerical
