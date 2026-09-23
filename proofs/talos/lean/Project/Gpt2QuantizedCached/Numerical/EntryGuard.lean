import Project.Gpt2QuantizedCached.Entry.Source

namespace Project.Gpt2QuantizedCached.Numerical.EntrySource
open LeanExe.Models.Gpt2

theorem finish_success (hidden : Quantized.HiddenResult) (normalized logits : ByteArray) (position : Nat)
    (h : (Entry.finishStep hidden normalized logits position).status = 0) :
    (Entry.finishStep hidden normalized logits position).cache = hidden.cache ∧
      (Entry.finishStep hidden normalized logits position).logits = logits := by
  by_cases hs : (hidden.status != 0) = true
  · simp only [Entry.finishStep, hs, ite_true] at h
    have hn : hidden.status ≠ 0 := by simpa only [bne_iff_ne] using hs
    exact (hn h).elim
  · by_cases hn : (!Quantized.finiteWords normalized 0 768) = true
    · simp only [Entry.finishStep, hs, hn, ite_false, ite_true] at h
      exact (show (4 : UInt64) ≠ 0 by decide) h |>.elim
    · by_cases ho : (!Quantized.finiteWords hidden.cache 0 ((position + 1) * cachePositionWords) ||
          !Quantized.finiteWords logits 0 50257) = true
      · simp only [Entry.finishStep, hs, hn, ho, ite_false, ite_true] at h
        exact (show (4 : UInt64) ≠ 0 by decide) h |>.elim
      · simp only [Entry.finishStep, hs, hn, ho, Bool.false_eq_true, ite_false, and_self]


def gated (badHeader badInput badCache : Bool) (hidden : Quantized.HiddenResult)
    (normalized logits : ByteArray) (position : Nat) : Quantized.CachedResult :=
  if badHeader then ⟨1, .empty, .empty⟩
  else if badInput then ⟨3, .empty, .empty⟩
  else if badCache then ⟨3, .empty, .empty⟩
  else Entry.finishStep hidden normalized logits position

theorem gated_success (badHeader badInput badCache : Bool) (hidden : Quantized.HiddenResult)
    (normalized logits : ByteArray) (position : Nat)
    (h : (gated badHeader badInput badCache hidden normalized logits position).status = 0) :
    (gated badHeader badInput badCache hidden normalized logits position).cache = hidden.cache ∧
      (gated badHeader badInput badCache hidden normalized logits position).logits = logits := by
  cases badHeader <;> cases badInput <;> cases badCache
  all_goals simp only [gated, Bool.false_eq_true, ite_false, ite_true] at h ⊢
  all_goals first | exact finish_success hidden normalized logits position h | contradiction

#print axioms gated_success
end Project.Gpt2QuantizedCached.Numerical.EntrySource
