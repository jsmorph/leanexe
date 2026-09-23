import Project.Gpt2QuantizedCached.Entry.HiddenStage

namespace Project.Gpt2QuantizedCached.Entry
open LeanExe.Models.Gpt2.Quantized

theorem hiddenStageResult_eq (weights : ByteArray) (hidden : HiddenResult) (position : Nat) :
    hiddenStageResult weights hidden position =
      finishStep hidden (normalizedBytes weights hidden.hidden)
        (vocabulary weights (normalizedBytes weights hidden.hidden)) position := by
  by_cases hZero : hidden.status = 0
  · cases hFinite : finiteWords (normalizedBytes weights hidden.hidden) 0 768 <;>
      simp [hiddenStageResult, normalizedResult, outputResult, outputRejected, finishStep, hZero, hFinite]
  · simp [hiddenStageResult, finishStep, hZero]

theorem hiddenSizes_success (cacheSize : Nat) (hidden : HiddenResult)
    (hSizes : CachedHidden.SizedResult cacheSize hidden) (hZero : hidden.status = 0) :
    hidden.hidden.size = 3072 ∧ hidden.cache.size = cacheSize + 73728 := by
  rcases hSizes with h | h
  · exact h.2
  · rw [hZero] at h
    exact False.elim ((by decide : (0 : UInt64) ≠ 4) h.1)

#print axioms hiddenStageResult_eq
#print axioms hiddenSizes_success
end Project.Gpt2QuantizedCached.Entry
