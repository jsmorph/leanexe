import Project.Gpt2QuantizedCached.Numerical.HiddenBounds

namespace Project.Gpt2QuantizedCached.Numerical.Hidden
open LeanExe.Models.Gpt2 Project.ProofKit

def finishQuantized (cache : ByteArray) (state : Gpt2QuantizedCached.CachedHidden.LayerState) : Quantized.HiddenResult :=
  if state.2.2 != 0 then { status := state.2.2, hidden := .empty, cache := .empty }
  else { status := 0, hidden := state.1, cache := cache ++ state.2.1 }

def finishReference (cache : ByteArray) (state : ByteArray × ByteArray) : CachedHidden :=
  { hidden := state.1, cache := cache ++ state.2 }

theorem finish_error (qc rc : ByteArray) (q : Gpt2QuantizedCached.CachedHidden.LayerState)
    (r : ByteArray × ByteArray) (position : Nat) (hiddenError updateError cacheError : ℝ)
    (hp : StateBound q r 12 hiddenError updateError)
    (hqc : qc.size = 4 * (position * 18432)) (hrc : rc.size = 4 * (position * 18432))
    (hc : Close qc rc (position * 18432) cacheError) :
    (finishQuantized qc q).status = 0 ∧
      Close (finishQuantized qc q).hidden (finishReference rc r).hidden 768 hiddenError ∧
      Close (finishQuantized qc q).cache (finishReference rc r).cache ((position + 1) * 18432)
        (max cacheError updateError) := by
  have ha := AppendError.close qc q.2.1 rc r.2 (position * 18432) 18432 cacheError updateError
    hqc hrc (by rw [hp.updateSize]) (by rw [hp.referenceUpdateSize]) hc hp.updateError
  simp only [finishQuantized, finishReference, hp.status, bne_self_eq_false, Bool.false_eq_true, ite_false]
  refine ⟨True.intro, hp.hiddenError, ?_⟩
  have he : (position + 1) * 18432 = position * 18432 + 18432 := by omega
  rw [he]
  exact ha

#print axioms finish_error
end Project.Gpt2QuantizedCached.Numerical.Hidden
