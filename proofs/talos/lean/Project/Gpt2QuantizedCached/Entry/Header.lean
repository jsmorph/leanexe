import Project.Gpt2QuantizedCached.Entry.FiniteTest
import Project.Gpt2QuantizedCached.Header

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def headerCode : Program :=
  [.localGet 0, .localSet 8, .localGet 1, .localSet 9, .localGet 2, .localSet 10,
   .localGet 8, .localGet 9, .localGet 10, .call 22] ++
   ReadOnlyDisjunction.negateProgram ++ ReadOnlyDisjunction.canonicalProgram

set_option maxRecDepth 32768 in
theorem emitted_header : func59.take 21 = headerCode := rfl

theorem header_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hState : State (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = frame.params → result.locals.length = 93 →
      I64Values result.locals → result.values = [.i32 (if !validHeader weights then 1 else 0)] →
      wp «module» rest Q initial result env) :
    wp «module» (headerCode ++ rest) Q initial frame env := by
  simp only [headerCode, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hState.values]
  refine wp_call_tw (Header.exact env initial weightsOwner weightsPtr weights hWeights) ?_
  rintro final returned ⟨hFinal, rfl⟩
  subst final
  apply ReadOnlyDisjunction.negate_spec _ _ _ _ _ rfl
  apply ReadOnlyDisjunction.canonical_spec _ _ _ _ _ rfl
  apply hNext
  · exact hState.paramsEq.symm
  · simpa only [List.length_set] using hState.length
  · simp (config := { maxDischargeDepth := 16 }) only [I64Values.set, hState.typed, and_self]
  · rfl

#print axioms header_spec
end Project.Gpt2QuantizedCached.Entry
