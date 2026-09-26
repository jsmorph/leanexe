import Project.Gpt2QuantizedCached.Entry.InputTest

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def cacheTestCode : Program :=
  [.localGet 3,
   .localSet 11,
   .localGet 4,
   .localSet 12,
   .localGet 5,
   .localSet 13,
   .constI64 0,
   .localSet 14,
   .localGet 7,
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
   .localSet 15,
   .localGet 11,
   .localGet 12,
   .localGet 13,
   .localGet 14,
   .localGet 15,
   .call 26] ++ ReadOnlyDisjunction.negateProgram ++ ReadOnlyDisjunction.canonicalProgram

theorem emitted_cacheTest : cacheBody.take 34 = cacheTestCode := rfl

theorem cacheTest_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hInput : invalidInput cache token position = false)
    (hState : State (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = frame.params → result.locals.length = 93 →
      I64Values result.locals → result.values = [.i32 (if !finiteWords cache 0 (position * cachePositionWords) then 1 else 0)] →
      wp «module» rest Q initial result env) :
    wp «module» (cacheTestCode ++ rest) Q initial frame env := by
  rcases (invalidInput_false cache token position).mp hInput with ⟨_, hp, hc⟩
  have hMulPosition : ¬(-1 : UInt64) / 18432 < UInt64.ofNat position := by
    change ¬(1000799917193443 : UInt64) < UInt64.ofNat position
    u64_omega
  have hProduct : UInt64.ofNat position * 18432 = UInt64.ofNat (position * cachePositionWords) := by
    rw [UInt64.ofNat_mul]
    rfl
  simp only [cacheTestCode, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hState.values]
  refine wp_call_tw (Layout.cachePositionWords_exact env initial) ?_
  rintro final returned ⟨hFinal, rfl⟩
  subst final
  repeat' first
    | wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length,
        hMulPosition, hProduct, show UInt64.ofNat cachePositionWords = 18432 from rfl]
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  refine wp_call_tw (FiniteWords.exact env initial cacheOwner cachePtr cache 0 (position * cachePositionWords)
    hCache (by rw [hc]; simp [cachePositionWords, Nat.mul_assoc])) ?_
  rintro final returned ⟨hFinal, rfl⟩
  subst final
  apply ReadOnlyDisjunction.negate_spec _ _ _ _ _ rfl
  apply ReadOnlyDisjunction.canonical_spec _ _ _ _ _ rfl
  apply hNext
  · exact hState.paramsEq.symm
  · simpa only [List.length_set] using hState.length
  · simp (config := { maxDischargeDepth := 32 }) only [I64Values.set, hState.typed]
  · rfl

#print axioms cacheTest_spec
end Project.Gpt2QuantizedCached.Entry
