import Project.Gpt2QuantizedCached.Entry.CacheTest
import Project.Gpt2QuantizedCached.Entry.StateTransfer
import Project.ProofKit.CheckedNatAddArithmetic

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def outputCacheTestCode : Program :=
  [.localGet 35,
   .localSet 79,
   .localGet 36,
   .localSet 80,
   .localGet 37,
   .localSet 81,
   .constI64 0,
   .localSet 82,
   .localGet 7,
   .localSet 98,
   .constI64 1,
   .localSet 99,
   .localGet 98,
   .localGet 99,
   .addI64,
   .localTee 100,
   .localGet 98,
   .ltUI64,
   .iff 0 1 [
        .unreachable
       ] [
        .localGet 100
       ] [] [.i64],
   .localSet 96,
   .call 29,
   .localSet 97,
   .localGet 97,
   .constI64 0,
   .eqI64,
   .iff 0 1 [
        .constI64 0
       ] [
        .constI64 (-1),
        .localGet 97,
        .divUI64,
        .localGet 96,
        .ltUI64,
        .iff 0 1 [
         .unreachable
        ] [
         .localGet 96,
         .localGet 97,
         .mulI64
        ] [] [.i64]
       ] [] [.i64],
   .localSet 83,
   .localGet 79,
   .localGet 80,
   .localGet 81,
   .localGet 82,
   .localGet 83,
   .call 26]

theorem emitted_outputCacheTest : (normalizedBody.drop 53).take 33 = outputCacheTestCode := rfl

theorem outputCacheTest_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr cacheOwner cachePtr hiddenPtr outputCachePtr normalizedPtr logitsPtr : UInt64)
    (weights cache outputCache : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hCache : ByteArrayAt initial.mem outputCachePtr.toNat outputCache)
    (hSize : (position + 1) * cachePositionWords * 4 ≤ outputCache.size)
    (hPosition : position < 128)
    (hState : LogitsState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      hiddenPtr outputCachePtr normalizedPtr logitsPtr outputCache.size frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = frame.params → result.locals.length = 93 →
      I64Values result.locals → result.locals.take 71 = frame.locals.take 71 →
      result.values = [.i64 (if finiteWords outputCache 0 ((position + 1) * cachePositionWords) then 1 else 0)] →
      wp «module» rest Q initial result env) :
    wp «module» (outputCacheTestCode ++ rest) Q initial frame env := by
  have hAdd : ¬UInt64.ofNat position + 1 < UInt64.ofNat position :=
    CheckedNatAdd.guard_of_fits position 1 (by change position + 1 < 18446744073709551616; omega)
  have hSum : UInt64.ofNat position + 1 = UInt64.ofNat (position + 1) := by
    rw [UInt64.ofNat_add]
    rfl
  have hMulPosition : ¬(-1 : UInt64) / 18432 < UInt64.ofNat (position + 1) := by
    change ¬(1000799917193443 : UInt64) < UInt64.ofNat (position + 1)
    u64_omega
  have hProduct : UInt64.ofNat (position + 1) * 18432 = UInt64.ofNat ((position + 1) * cachePositionWords) := by
    rw [UInt64.ofNat_mul]
    rfl
  simp only [outputCacheTestCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hState.values,
    hState.cacheOwner, hState.cachePtr, hState.cacheSize]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simp only [hAdd, ite_false]; decide)]
  wp_packed_frame [hState.length]
  refine wp_call_tw (Layout.cachePositionWords_exact env initial) ?_
  rintro final returned ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hState.length, show UInt64.ofNat cachePositionWords = 18432 from rfl]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hState.length]
  try simp only [hSum, hMulPosition, ite_false]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hState.length, hProduct]
  refine wp_call_tw (FiniteWords.exact env initial outputCachePtr outputCachePtr outputCache 0
    ((position + 1) * cachePositionWords) hCache (by simpa using hSize)) ?_
  rintro final returned ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · exact hState.paramsEq.symm
  · simpa only [List.length_set] using hState.length
  · simp (config := { maxDischargeDepth := 32 }) only [I64Values.set, hState.typed]
  · simp only [List.take_set_of_le, Nat.reduceLeDiff]
  · rfl

#print axioms outputCacheTest_spec
end Project.Gpt2QuantizedCached.Entry
