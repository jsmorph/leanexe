import Project.Gpt2QuantizedCached.Entry.AcceptedSource

namespace Project.Gpt2QuantizedCached.Entry
open LeanExe.Models.Gpt2.Quantized

structure SizedResult (cacheSize : Nat) (result : CachedResult) : Prop where
  success : result.status = 0 → result.cache.size = cacheSize + 73728 ∧ result.logits.size = 201028
  failure : result.status ≠ 0 → result.cache = .empty ∧ result.logits = .empty

theorem finishStep_sizes (cacheSize : Nat) (hidden : HiddenResult) (normalized logits : ByteArray)
    (position : Nat) (hHidden : CachedHidden.SizedResult cacheSize hidden) (hLogits : logits.size = 201028) :
    SizedResult cacheSize (finishStep hidden normalized logits position) := by
  unfold finishStep
  split
  · rename_i hStatus
    have hNonzero : hidden.status ≠ 0 := by simpa using hStatus
    exact ⟨fun h => False.elim (hNonzero h), fun _ => ⟨rfl, rfl⟩⟩
  · rename_i hStatus
    have hZero : hidden.status = 0 := by simpa using hStatus
    split
    · exact ⟨fun h => False.elim ((by decide : (4 : UInt64) ≠ 0) h), fun _ => ⟨rfl, rfl⟩⟩
    · split
      · exact ⟨fun h => False.elim ((by decide : (4 : UInt64) ≠ 0) h), fun _ => ⟨rfl, rfl⟩⟩
      · exact ⟨fun _ => ⟨(hiddenSizes_success cacheSize hidden hHidden hZero).2, hLogits⟩,
          fun h => False.elim (h rfl)⟩

theorem cachedStep_sizes (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    SizedResult cache.size (cachedStep weights cache token position) := by
  rw [cachedStep_eq]
  split
  · exact ⟨fun h => False.elim ((by decide : (1 : UInt64) ≠ 0) h), fun _ => ⟨rfl, rfl⟩⟩
  · split
    · exact ⟨fun h => False.elim ((by decide : (3 : UInt64) ≠ 0) h), fun _ => ⟨rfl, rfl⟩⟩
    · split
      · exact ⟨fun h => False.elim ((by decide : (3 : UInt64) ≠ 0) h), fun _ => ⟨rfl, rfl⟩⟩
      · exact finishStep_sizes cache.size _ _ _ position (CachedHidden.cachedHidden_sizes weights cache token position)
          (by unfold vocabulary; rw [GroupedProjection.linearGroupedRows_size])

#print axioms finishStep_sizes
#print axioms cachedStep_sizes
end Project.Gpt2QuantizedCached.Entry
