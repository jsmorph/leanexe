import Project.Gpt2CachedStep.Program
import Project.Gpt2CachedStep.CachedAttention.Source
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.PackedWordRead
import Project.ProofKit.PackedFloatFrame
import Project.ProofKit.F32Div
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.CachedAttention
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def probabilitiesBody : Wasm.Program :=
  match (func29[271]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def probabilitiesWord : Wasm.Program := (probabilitiesBody.drop 12).take (probabilitiesBody.length - 19)

set_option maxRecDepth 32768 in
theorem emitted_probabilities : (func29.drop 271).take 1 =
    PackedGenerateLoop.program 63 109 110 probabilitiesWord := rfl

def ProbabilitiesState (params saved : List Wasm.Value) (exponentialPtr sumPtr : UInt64)
    (exponentialValues sumValues : ByteArray) (position : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.params.length = 8 ∧ frame.locals.length = 114 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (position + 1))) ∧
  frame.locals[40]? = some (.i64 exponentialPtr) ∧ frame.locals[41]? = some (.i64 exponentialPtr) ∧
  frame.locals[42]? = some (.i64 (UInt64.ofNat exponentialValues.size)) ∧
  frame.locals[51]? = some (.i64 sumPtr) ∧ frame.locals[52]? = some (.i64 sumPtr) ∧
  frame.locals[53]? = some (.i64 (UInt64.ofNat sumValues.size)) ∧
  frame.locals[54]? = some (.i64 (UInt64.ofNat (4 * (12 * (position + 1))))) ∧ I64Values frame.locals ∧ frame.locals.take 54 = saved

set_option maxRecDepth 32768 in
theorem probabilitiesWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved : List Wasm.Value) (exponentialPtr sumPtr outputPtr : UInt64)
    (exponentialValues sumValues : ByteArray) (position index : Nat) (frame : Locals)
    (hExponentials : ByteArrayAt initial.mem exponentialPtr.toNat exponentialValues)
    (hSums : ByteArrayAt initial.mem sumPtr.toNat sumValues)
    (hExponentialSize : 4 * (12 * (position + 1)) ≤ exponentialValues.size) (hSumSize : 48 ≤ sumValues.size)
    (hPosition : position < 128) (hIndex : index < 12 * (position + 1))
    (hReady : PackedGenerateLoop.Ready 63 109 110 (12 * (position + 1)) index outputPtr frame)
    (hState : ProbabilitiesState params saved exponentialPtr sumPtr exponentialValues sumValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 63 109 110 (12 * (position + 1)) index outputPtr result →
      ProbabilitiesState params saved exponentialPtr sumPtr exponentialValues sumValues position result →
      wp «module» rest Q initial { result with values :=
        [.i64 (LeanExe.Float32.divBits (word exponentialValues index)
          (word sumValues (index / (position + 1)))).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (probabilitiesWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hParamLength, hLength, hSize, hExponentialOwner, hExponentialPtr, hExponentialBytes,
    hSumOwner, hSumPtr, hSumBytes, hBytes, hTyped, hPrefix⟩
  have hParamsLength : params.length = 8 := by rw [← hParams]; exact hParamLength
  have hCounter : frame.locals[55]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[101]? = some (.i64 (UInt64.ofNat (4 * (12 * (position + 1))))) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.1
  have hPointer : frame.locals[102]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.2.1
  have hSize64 : position + 1 < 2^64 := by omega
  have hIndex64 : index < 2^64 := by omega
  have hNonzero : UInt64.ofNat (position + 1) ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hSize64] at this
    change position + 1 = 0 at this
    omega
  have hDiv : UInt64.ofNat index / UInt64.ofNat (position + 1) = UInt64.ofNat (index / (position + 1)) := by
    symm
    exact UInt64.ofNat_div hIndex64 hSize64
  have hHead : index / (position + 1) < 12 :=
    (Nat.div_lt_iff_lt_mul (Nat.succ_pos position)).mpr hIndex
  simp only [probabilitiesWord, probabilitiesBody, func29, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParamLength, hLength, hCounter, hExponentialOwner, hExponentialPtr, hExponentialBytes]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial
    exponentialPtr exponentialPtr exponentialValues index hExponentials (by omega)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParamLength, hLength, hCounter, hSize, hSumOwner, hSumPtr, hSumBytes, hNonzero, hDiv]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParamLength, hLength, hCounter, hSize, hNonzero, hDiv]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env final
    sumPtr sumPtr sumValues (index / (position + 1)) hSums (by omega)).append_args
    rfl rfl rfl [.f32 (word exponentialValues index), .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParamLength, hLength]
  simp only [F32Div.div_eq] at hNext
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 63 109 110 (12 * (position + 1)) index outputPtr result ∧
      ProbabilitiesState params saved exponentialPtr sumPtr exponentialValues sumValues position result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (Wasm.IEEE32.div (word exponentialValues index)
      (word sumValues (index / (position + 1)))).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hParamLength, hLength, List.length_set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        reduceIte, List.getElem?_set, Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
    · simp (config := { maxDischargeDepth := 64 }) only [ProbabilitiesState, hParams, hParamsLength, hLength,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte, hSize,
        hExponentialOwner, hExponentialPtr, hExponentialBytes, hSumOwner, hSumPtr, hSumBytes,
        hBytes, I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem probabilitiesState_advance (params saved : List Wasm.Value) (exponentialPtr sumPtr : UInt64)
    (exponentialValues sumValues : ByteArray) (position : Nat) (frame : Locals) (index : Nat)
    (hValid : frame.validIndex 63)
    (hState : ProbabilitiesState params saved exponentialPtr sumPtr exponentialValues sumValues position frame) :
    ProbabilitiesState params saved exponentialPtr sumPtr exponentialValues sumValues position
      (FixedArrayCopy.counterFrame frame 63 index hValid) := by
  rcases hState with ⟨hParams, hParamLength, hLength, hSize, hExponentialOwner, hExponentialPtr, hExponentialBytes,
    hSumOwner, hSumPtr, hSumBytes, hBytes, hTyped, hPrefix⟩
  have hParamsLength : params.length = 8 := by rw [← hParams]; exact hParamLength
  simp (config := { maxDischargeDepth := 64 }) only [ProbabilitiesState, FixedArrayCopy.counterFrame, Locals.set,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hParams, hParamsLength, hSize,
    hExponentialOwner, hExponentialPtr, hExponentialBytes, hSumOwner, hSumPtr, hSumBytes,
    hBytes, I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]

set_option maxRecDepth 32768 in
theorem probabilitiesLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved : List Wasm.Value) (exponentialPtr sumPtr outputPtr : UInt64)
    (exponentialValues sumValues : ByteArray) (position : Nat) (frame : Locals)
    (hExponentials : ByteArrayAt initial.mem exponentialPtr.toNat exponentialValues)
    (hSums : ByteArrayAt initial.mem sumPtr.toNat sumValues)
    (hExponentialSize : 4 * (12 * (position + 1)) ≤ exponentialValues.size) (hSumSize : 48 ≤ sumValues.size)
    (hPosition : position < 128)
    (hFit : outputPtr.toNat + 4 * (12 * (position + 1)) ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * (12 * (position + 1)) ≤ initial.mem.pages * 65536)
    (hExponentialSep : exponentialPtr.toNat + exponentialValues.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (12 * (position + 1)) ≤ exponentialPtr.toNat)
    (hSumSep : sumPtr.toNat + sumValues.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (12 * (position + 1)) ≤ sumPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 63 109 110 (12 * (position + 1)) 0 outputPtr frame)
    (hState : ProbabilitiesState params saved exponentialPtr sumPtr exponentialValues sumValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 63 109 110 (12 * (position + 1)) (12 * (position + 1)) outputPtr result →
      ProbabilitiesState params saved exponentialPtr sumPtr exponentialValues sumValues position result →
      ByteArrayAt final.mem outputPtr.toNat (probabilities exponentialValues sumValues (position + 1)) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * (12 * (position + 1))) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 271).take 1 ++ rest) Q initial frame env := by
  rw [emitted_probabilities]
  apply PackedGenerateLoop.program_spec
    (value := fun index => LeanExe.Float32.divBits (word exponentialValues index)
      (word sumValues (index / (position + 1))))
    (P := ProbabilitiesState params saved exponentialPtr sumPtr exponentialValues sumValues position)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact probabilitiesState_advance params saved exponentialPtr sumPtr exponentialValues sumValues position next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact probabilitiesWord_spec env current params saved exponentialPtr sumPtr outputPtr exponentialValues sumValues position index next
      (hExponentials.writesRange hWrites hExponentialSep) (hSums.writesRange hWrites hSumSep)
      hExponentialSize hSumSize hPosition hIndex hReady hState Q rest hNext
  · exact hDone

#print axioms probabilitiesWord_spec
#print axioms probabilitiesLoop_spec

end Project.Gpt2CachedStep.CachedAttention
