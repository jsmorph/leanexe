import Project.Gpt2QuantizedCached.Numerical.HiddenBounds

namespace Project.Gpt2QuantizedCached.Numerical.Hidden
open LeanExe.Models.Gpt2 Project.ProofKit

theorem result_bound (q : Gpt2QuantizedCached.CachedHidden.LayerState) (r : ByteArray × ByteArray)
    (qr : Quantized.HiddenResult) (rr : CachedHidden) (count : Nat)
    (hiddenError updateError nextHiddenError nextCacheError : ℝ)
    (hp : StateBound q r count hiddenError updateError)
    (hStatus : qr.status = 0) (hqHidden : qr.hidden.size = 3072) (hqCache : qr.cache.size = 6144)
    (hrHidden : rr.hidden.size = 3072) (hrCache : rr.cache.size = 6144)
    (hHidden : Close qr.hidden rr.hidden 768 nextHiddenError) (hCache : Close qr.cache rr.cache 1536 nextCacheError) :
    StateBound (qr.hidden, q.2.1 ++ qr.cache, qr.status) (rr.hidden, r.2 ++ rr.cache) (count + 1)
      nextHiddenError (max updateError nextCacheError) := by
  have ha := AppendError.close q.2.1 qr.cache r.2 rr.cache (count * 1536) 1536 updateError nextCacheError
    (by rw [hp.updateSize]; omega) (by rw [hp.referenceUpdateSize]; omega) (by rw [hqCache]) (by rw [hrCache])
    hp.updateError hCache
  refine ⟨hStatus, hqHidden, ?_, hrHidden, ?_, hHidden, ?_⟩
  · simp only [ByteArray.size_append, hp.updateSize, hqCache]
    omega
  · simp only [ByteArray.size_append, hp.referenceUpdateSize, hrCache]
    omega
  · have he : (count + 1) * 1536 = count * 1536 + 1536 := by omega
    rw [he]
    exact ha

#print axioms result_bound
end Project.Gpt2QuantizedCached.Numerical.Hidden
