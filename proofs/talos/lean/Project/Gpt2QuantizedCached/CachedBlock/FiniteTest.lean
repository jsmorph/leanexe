import Project.Gpt2QuantizedCached.CachedBlock.Structure
import Project.Gpt2QuantizedCached.FiniteWords
import Project.ProofKit.ReadOnlyDisjunction
import Project.ProofKit.LocalPrefix

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def finiteTestCode (source count : Nat) : Program :=
  [.localGet (11 + source), .localSet (14 + source),
   .localGet (12 + source), .localSet (15 + source),
   .localGet (13 + source), .localSet (16 + source),
   .constI64 0, .localSet (17 + source), .constI64 (UInt64.ofNat count), .localSet (18 + source),
   .localGet (14 + source), .localGet (15 + source), .localGet (16 + source),
   .localGet (17 + source), .localGet (18 + source), .call 26] ++
   ReadOnlyDisjunction.negateProgram ++ ReadOnlyDisjunction.canonicalProgram

theorem normalized_test_code : (func54.drop 80).take 27 = finiteTestCode 13 768 := rfl
theorem attention_test_code : (normalizedSuccess.drop 113).take 27 = finiteTestCode 51 768 := rfl
theorem normalized2_test_code : (attentionSuccess.drop 178).take 27 = finiteTestCode 102 768 := rfl
theorem activated_test_code : (normalized2Success.drop 98).take 27 = finiteTestCode 135 3072 := rfl

theorem finiteTest_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (count source : Nat)
    (hInput : ByteArrayAt initial.mem ptr.toNat input) (hExtent : count * 4 ≤ input.size)
    (hSource : source = 13 ∨ source = 51 ∨ source = 102 ∨ source = 135)
    (frame : Locals) (hParams : frame.params.length = 11)
    (hLength : frame.locals.length = 193) (hValues : frame.values = [])
    (hOwner : frame.locals[source]? = some (.i64 owner))
    (hPtr : frame.locals[source + 1]? = some (.i64 ptr))
    (hBytes : frame.locals[source + 2]? = some (.i64 (UInt64.ofNat input.size)))
    (hTyped : I64Values frame.locals) (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = frame.params → result.locals.length = 193 →
      I64Values result.locals → result.locals.take (source + 3) = frame.locals.take (source + 3) →
      result.values = [.i32 (if !finiteWords input 0 count then 1 else 0)] →
      wp «module» rest Q initial result env) :
    wp «module» (finiteTestCode source count ++ rest) Q initial frame env := by
  rcases hSource with rfl | rfl | rfl | rfl
  all_goals
    simp only [finiteTestCode, List.append_assoc, List.cons_append, List.nil_append]
    wp_packed_frame [hParams, hLength, hValues, hOwner, hPtr, hBytes]
    refine wp_call_tw (FiniteWords.exact env initial owner ptr input 0 count hInput (by simpa using hExtent)) ?_
    rintro final values ⟨hFinal, rfl⟩
    subst final
    apply ReadOnlyDisjunction.negate_spec _ _ _ _ _ rfl
    apply ReadOnlyDisjunction.canonical_spec _ _ _ _ _ rfl
    apply hNext
    · rfl
    · simpa only [List.length_set] using hLength
    · simp (config := { maxDischargeDepth := 16 }) only [I64Values.set, hTyped, and_self]
    · simp only [List.take_set_of_le, Nat.reduceLeDiff, Nat.reduceAdd]
    · rfl

#print axioms finiteTest_spec
end Project.Gpt2QuantizedCached.CachedBlock
