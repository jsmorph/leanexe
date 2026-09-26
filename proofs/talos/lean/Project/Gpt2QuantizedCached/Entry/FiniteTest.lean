import Project.Gpt2QuantizedCached.Entry.Code
import Project.ProofKit.ReadOnlyDisjunction
import Project.ProofKit.LocalPrefix

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def finiteTestCode (source target count : Nat) : Program :=
  [.localGet (8 + source), .localSet (8 + target),
   .localGet (9 + source), .localSet (9 + target),
   .localGet (10 + source), .localSet (10 + target),
   .constI64 0, .localSet (11 + target), .constI64 (UInt64.ofNat count), .localSet (12 + target),
   .localGet (8 + target), .localGet (9 + target), .localGet (10 + target),
   .localGet (11 + target), .localGet (12 + target), .call 26]

theorem emitted_normalizedTest : (hiddenBody.drop 61).take 27 =
    finiteTestCode 42 45 768 ++ ReadOnlyDisjunction.negateProgram ++
      ReadOnlyDisjunction.canonicalProgram := rfl

theorem finiteTest_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (count source target : Nat)
    (hInput : ByteArrayAt initial.mem ptr.toNat input) (hExtent : count * 4 ≤ input.size)
    (hSource : (source = 42 ∧ target = 45) ∨ (source = 68 ∧ target = 76))
    (frame : Locals) (hParams : frame.params.length = 8)
    (hLength : frame.locals.length = 93) (hValues : frame.values = [])
    (hOwner : frame.locals[source]? = some (.i64 owner))
    (hPtr : frame.locals[source + 1]? = some (.i64 ptr))
    (hBytes : frame.locals[source + 2]? = some (.i64 (UInt64.ofNat input.size)))
    (hTyped : I64Values frame.locals) (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = frame.params → result.locals.length = 93 →
      I64Values result.locals → result.locals.take target = frame.locals.take target →
      result.values = [.i64 (if finiteWords input 0 count then 1 else 0)] →
      wp «module» rest Q initial result env) :
    wp «module» (finiteTestCode source target count ++ rest) Q initial frame env := by
  rcases hSource with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [finiteTestCode, List.cons_append, List.nil_append]
    wp_packed_frame [hParams, hLength, hValues, hOwner, hPtr, hBytes]
    refine wp_call_tw (FiniteWords.exact env initial owner ptr input 0 count hInput (by simpa using hExtent)) ?_
    rintro final values ⟨hFinal, rfl⟩
    subst final
    apply hNext
    · rfl
    · simpa only [List.length_set] using hLength
    · simp (config := { maxDischargeDepth := 16 }) only [I64Values.set, hTyped, and_self]
    · simp only [List.take_set_of_le, Nat.reduceLeDiff, Nat.reduceAdd]
    · rfl

#print axioms finiteTest_spec
end Project.Gpt2QuantizedCached.Entry
