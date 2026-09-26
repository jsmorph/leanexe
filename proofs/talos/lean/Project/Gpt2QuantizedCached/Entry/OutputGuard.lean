import Project.Gpt2QuantizedCached.Entry.OutputCacheTest
import Project.Gpt2QuantizedCached.Entry.FiniteGuard

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def outputTestCode : Program := outputCacheTestCode ++ ReadOnlyDisjunction.negateProgram ++
  ReadOnlyDisjunction.program (finiteTestCode 68 76 50257) ++ ReadOnlyDisjunction.canonicalProgram

theorem emitted_outputTest : (normalizedBody.drop 53).take 45 = outputTestCode := rfl

theorem outputGuard_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr cacheOwner cachePtr hiddenPtr outputCachePtr normalizedPtr logitsPtr : UInt64)
    (weights cache outputCache logits : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hCache : ByteArrayAt initial.mem outputCachePtr.toNat outputCache)
    (hLogits : ByteArrayAt initial.mem logitsPtr.toNat logits)
    (hSize : (position + 1) * cachePositionWords * 4 ≤ outputCache.size)
    (hLogitsSize : logits.size = 201028) (hPosition : position < 128)
    (hState : LogitsState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      hiddenPtr outputCachePtr normalizedPtr logitsPtr outputCache.size frame)
    (Q : Assertion Unit) (failure success rest : Program)
    (hNext : ∀ result,
      LogitsState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        hiddenPtr outputCachePtr normalizedPtr logitsPtr outputCache.size result →
      wp «module» (if !finiteWords outputCache 0 ((position + 1) * cachePositionWords) ||
        !finiteWords logits 0 50257 then failure else success)
        (PackedReleaseFilter.afterAction «module» env rest Q) initial result env) :
    wp «module» (outputTestCode ++ [.iff 0 0 failure success] ++ rest) Q initial frame env := by
  have done : ∀ result,
      LogitsState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        hiddenPtr outputCachePtr normalizedPtr logitsPtr outputCache.size { result with values := [] } →
      result.values = [.i32 (if !finiteWords outputCache 0 ((position + 1) * cachePositionWords) ||
        !finiteWords logits 0 50257 then 1 else 0)] →
      wp «module» (ReadOnlyDisjunction.canonicalProgram ++ [.iff 0 0 failure success] ++ rest)
        Q initial result env := by
    intro result hResult hValues
    rw [List.append_assoc]
    apply ReadOnlyDisjunction.canonical_spec _ _ _ _ _ hValues
    apply boolBranch_spec env initial result _ hValues
    exact hNext _ hResult
  simp only [outputTestCode, List.append_assoc]
  apply outputCacheTest_spec env initial weightsOwner weightsPtr cacheOwner cachePtr hiddenPtr outputCachePtr
    normalizedPtr logitsPtr weights cache outputCache token position frame hCache hSize hPosition hState
  intro checked hParams hLength hTyped hPrefix hValues
  have hChecked := hState.transfer (after := { checked with values := [] })
    hParams hLength rfl hTyped hPrefix (by decide)
  apply ReadOnlyDisjunction.negate_spec _ _ _ _ _ hValues
  simp only [ReadOnlyDisjunction.program, List.cons_append, List.nil_append, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  cases hFinite : finiteWords outputCache 0 ((position + 1) * cachePositionWords)
  · rw [ite_eq_left (by simp [hFinite])]
    wp_packed_frame []
    apply done
    · exact hChecked
    · simp [hFinite]
  · rw [ite_eq_right (by simp [hFinite])]
    apply finiteTest_spec env initial logitsPtr logitsPtr logits 50257 68 76 hLogits
      (by rw [hLogitsSize]) (Or.inr ⟨rfl, rfl⟩)
      { checked with values := [] }
      (by rw [hChecked.paramsEq]; rfl) hLength rfl hChecked.logitsOwner hChecked.logitsPtr
      (by simpa only [hLogitsSize, Nat.reduceAdd, show UInt64.ofNat 201028 = 201028 from rfl] using hChecked.logitsSize) hTyped
    intro result hResultParams hResultLength hResultTyped hResultPrefix hResultValues
    change wp «module» (ReadOnlyDisjunction.negateProgram ++ []) _ initial result env
    apply ReadOnlyDisjunction.negate_spec _ _ _ _ _ hResultValues
    wp_packed_frame []
    apply done
    · exact hChecked.transfer hResultParams hResultLength rfl hResultTyped hResultPrefix (by decide)
    · simp [hFinite]

#print axioms outputGuard_spec
end Project.Gpt2QuantizedCached.Entry
