import Project.Gpt2CachedStep.CachedAttention.Source
import Project.Gpt2CachedStep.CachedAttention.SoftmaxError
import Project.Gpt2CachedStep.CachedRowSum.Source
import Project.Gpt2CachedStep.LayerNorm.Numerical

namespace Project.Gpt2CachedStep.CachedAttention.NumericalSource
open LeanExe.Models.Gpt2 Project.ProofKit
open LayerNorm.Numerical (word_generate)

def rowScores (scoreValues : ByteArray) (head size : Nat) : Nat → UInt32 :=
  fun i => word scoreValues (head * size + i)

def rowMaximum (scoreValues : ByteArray) (head size : Nat) : UInt32 :=
  cachedRowMaximum scoreValues head size

theorem row_index (head size i : Nat) (hh : head < 12) (hi : i < size) :
    head * size + i < 12 * size := by
  have hm := Nat.mul_le_mul_right size (show head + 1 ≤ 12 by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem row_div (head size i : Nat) (hi : i < size) : (head * size + i) / size = head := by
  have hn : 0 < size := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right i head hn, Nat.div_eq_of_lt hi, Nat.zero_add]

theorem exponential_word (scoreValues : ByteArray) (head size i : Nat)
    (hh : head < 12) (hi : i < size) :
    word (exponentials scoreValues (maxima scoreValues size) size) (head * size + i) =
      SoftmaxError.exponential (rowScores scoreValues head size) (rowMaximum scoreValues head size) i := by
  rw [exponentials, word_generate _ _ _ (row_index head size i hh hi), row_div head size i hi]
  rw [maxima, word_generate _ _ head hh]
  rfl

theorem sum_prefix (scoreValues : ByteArray) (head size count : Nat) (hh : head < 12) (hc : count ≤ size) :
    CachedRowSum.sumPrefix (exponentials scoreValues (maxima scoreValues size) size) head size count =
      SoftmaxError.denominator (rowScores scoreValues head size) (rowMaximum scoreValues head size) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [CachedRowSum.sumPrefix_succ, ih (by omega)]
    change _ = F32SumError.sumPrefix _ (count + 1)
    rw [F32SumError.sumPrefix_succ, exponential_word scoreValues head size count hh (by omega), F32Add.add_eq]
    rfl

theorem sum_word (scoreValues : ByteArray) (head size : Nat) (hh : head < 12) :
    word (sums (exponentials scoreValues (maxima scoreValues size) size) size) head =
      SoftmaxError.denominator (rowScores scoreValues head size) (rowMaximum scoreValues head size) size := by
  rw [sums, word_generate _ _ head hh, CachedRowSum.cachedRowSum_eq]
  exact sum_prefix scoreValues head size size hh le_rfl

theorem probability_word (scoreValues : ByteArray) (head size i : Nat) (hh : head < 12) (hi : i < size) :
    let es := exponentials scoreValues (maxima scoreValues size) size
    word (probabilities es (sums es size) size) (head * size + i) =
      SoftmaxError.probability (rowScores scoreValues head size) (rowMaximum scoreValues head size) size i := by
  dsimp only
  rw [probabilities, word_generate _ _ _ (row_index head size i hh hi), row_div head size i hi,
    exponential_word scoreValues head size i hh hi, sum_word scoreValues head size hh]
  rfl

def probabilityValues (cache qkv : ByteArray) (layer position : Nat) : ByteArray :=
  let ss := scores cache qkv layer position
  let es := exponentials ss (maxima ss (position + 1)) (position + 1)
  probabilities es (sums es (position + 1)) (position + 1)

theorem attention_word (cache qkv : ByteArray) (layer position i : Nat) (hi : i < 768) :
    word (cachedAttention cache qkv layer position) i =
      mixedPrefix cache qkv (probabilityValues cache qkv layer position) layer position i (position + 1) := by
  rw [cachedAttention_eq]
  exact word_generate 768 _ i hi

#print axioms probability_word
#print axioms attention_word
end Project.Gpt2CachedStep.CachedAttention.NumericalSource
