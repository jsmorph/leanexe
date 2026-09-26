import Project.Gpt2QuantizedCached.Numerical.TensorBounds
import Project.ProofKit.PackedAppendSource

namespace Project.Gpt2QuantizedCached.Numerical.AppendError
open LeanExe.Models.Gpt2 Project.ProofKit

theorem word_left (a b : ByteArray) (n i : Nat) (ha : a.size = 4 * n) (hi : i < n) :
    word (a ++ b) i = word a i := by
  exact PackedAppendSource.read_left a b (i * 4) (by omega)

theorem word_right (a b : ByteArray) (n m i : Nat) (ha : a.size = 4 * n) (hb : b.size = 4 * m) (hi : i < m) :
    word (a ++ b) (n + i) = word b i := by
  unfold word
  have hoff : (n + i) * 4 = a.size + i * 4 := by omega
  rw [hoff]
  exact PackedAppendSource.read_right a b (i * 4) (by omega)

theorem close (qa qb ra rb : ByteArray) (n m : Nat) (leftError rightError : ℝ)
    (hqa : qa.size = 4 * n) (hra : ra.size = 4 * n) (hqb : qb.size = 4 * m) (hrb : rb.size = 4 * m)
    (hl : Close qa ra n leftError) (hr : Close qb rb m rightError) :
    Close (qa ++ qb) (ra ++ rb) (n + m) (max leftError rightError) := by
  intro i hi
  by_cases hn : i < n
  · rw [word_left qa qb n i hqa hn, word_left ra rb n i hra hn]
    exact (hl i hn).trans (le_max_left _ _)
  · have he : i = n + (i - n) := by omega
    have hm : i - n < m := by omega
    rw [he, word_right qa qb n m (i - n) hqa hqb hm, word_right ra rb n m (i - n) hra hrb hm]
    exact (hr _ hm).trans (le_max_right _ _)

#print axioms close
end Project.Gpt2QuantizedCached.Numerical.AppendError
