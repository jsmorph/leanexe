import Project.Gpt2CachedStep.Program
import Project.Gpt2CachedStep.CachedBlock.Source
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.PackedWordRead
import Project.ProofKit.PackedFloatFrame
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def cacheWord : Wasm.Program :=
  [.localGet 41, .localSet 156, .localGet 42, .localSet 157, .localGet 43, .localSet 158,
   .constI64 768, .localSet 169, .localGet 155, .localSet 170,
   .localGet 169, .localGet 170, .addI64, .localTee 171, .localGet 169, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 171] [] [.i64], .localSet 159,
   .localGet 156, .localGet 157, .localGet 158, .localGet 159, .call 17]

set_option maxRecDepth 32768 in
theorem emitted_cache : (func33.drop 526).take 1 =
    PackedGenerateLoop.program 155 167 168 cacheWord := rfl

def CacheState (params saved : List Wasm.Value) (qkvOwner qkvPtr hiddenPtr : UInt64)
    (qkv : ByteArray) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.params.length = 11 ∧ frame.locals.length = 164 ∧
  frame.locals[30]? = some (.i64 qkvOwner) ∧ frame.locals[31]? = some (.i64 qkvPtr) ∧
  frame.locals[32]? = some (.i64 (UInt64.ofNat qkv.size)) ∧
  frame.locals[150]? = some (.i64 hiddenPtr) ∧ frame.locals[151]? = some (.i64 hiddenPtr) ∧
  frame.locals[152]? = some (.i64 3072) ∧ frame.locals[143]? = some (.i64 6144) ∧
  I64Values frame.locals ∧ frame.locals.take 143 = saved

set_option maxRecDepth 32768 in
theorem cacheWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved : List Wasm.Value) (qkvOwner qkvPtr hiddenPtr outputPtr : UInt64)
    (qkv : ByteArray) (index : Nat) (frame : Locals)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv) (hQkvSize : 9216 ≤ qkv.size)
    (hIndex : index < 1536)
    (hReady : PackedGenerateLoop.Ready 155 167 168 1536 index outputPtr frame)
    (hState : CacheState params saved qkvOwner qkvPtr hiddenPtr qkv frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 155 167 168 1536 index outputPtr result →
      CacheState params saved qkvOwner qkvPtr hiddenPtr qkv result →
      wp «module» rest Q initial { result with values :=
        [.i64 (word qkv (768 + index)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (cacheWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hParamLength, hLength, hQkvOwner, hQkvPtr, hQkvBytes,
    hHiddenOwner, hHiddenPtr, hHiddenBytes, hBytes, hTyped, hPrefix⟩
  have hParamsLength : params.length = 11 := by rw [← hParams]; exact hParamLength
  have hCounter : frame.locals[144]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[156]? = some (.i64 6144) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.1
  have hPointer : frame.locals[157]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.2.1
  have hSafe : ¬ (768 : UInt64) + UInt64.ofNat index < 768 := by
    exact CheckedNatAdd.guard_of_fits 768 index (by change _ < 18446744073709551616; omega)
  have hAdd : (768 : UInt64) + UInt64.ofNat index = UInt64.ofNat (768 + index) := by simp
  simp only [cacheWord, List.cons_append, List.nil_append]
  wp_packed_frame [hParamLength, hLength, hCounter, hQkvOwner, hQkvPtr, hQkvBytes]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hSafe)]
  wp_packed_frame [hParamLength, hLength, hAdd]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial
    qkvOwner qkvPtr qkv (768 + index) hQkv (by omega)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 155 167 168 1536 index outputPtr result ∧
      CacheState params saved qkvOwner qkvPtr hiddenPtr qkv result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (word qkv (768 + index)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hParamLength, hLength, List.length_set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        reduceIte, List.getElem?_set, Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and,
        show UInt64.ofNat (4 * 1536) = 6144 from rfl]
    · simp (config := { maxDischargeDepth := 64 }) only [CacheState, hParams, hParamsLength, hLength,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte,
        hQkvOwner, hQkvPtr, hQkvBytes, hHiddenOwner, hHiddenPtr, hHiddenBytes,
        hBytes, I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem cacheState_advance (params saved : List Wasm.Value) (qkvOwner qkvPtr hiddenPtr : UInt64)
    (qkv : ByteArray) (frame : Locals) (index : Nat) (hValid : frame.validIndex 155)
    (hState : CacheState params saved qkvOwner qkvPtr hiddenPtr qkv frame) :
    CacheState params saved qkvOwner qkvPtr hiddenPtr qkv
      (FixedArrayCopy.counterFrame frame 155 index hValid) := by
  rcases hState with ⟨hParams, hParamLength, hLength, hQkvOwner, hQkvPtr, hQkvBytes,
    hHiddenOwner, hHiddenPtr, hHiddenBytes, hBytes, hTyped, hPrefix⟩
  have hParamsLength : params.length = 11 := by rw [← hParams]; exact hParamLength
  simp (config := { maxDischargeDepth := 64 }) only [CacheState, FixedArrayCopy.counterFrame, Locals.set,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hParams, hParamsLength,
    hQkvOwner, hQkvPtr, hQkvBytes, hHiddenOwner, hHiddenPtr, hHiddenBytes,
    hBytes, I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]

set_option maxRecDepth 32768 in
theorem cacheLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved : List Wasm.Value) (qkvOwner qkvPtr hiddenPtr outputPtr : UInt64)
    (qkv : ByteArray) (frame : Locals)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv) (hQkvSize : 9216 ≤ qkv.size)
    (hFit : outputPtr.toNat + 6144 ≤ 2^32)
    (hMemory : outputPtr.toNat + 6144 ≤ initial.mem.pages * 65536)
    (hSep : qkvPtr.toNat + qkv.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 6144 ≤ qkvPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 155 167 168 1536 0 outputPtr frame)
    (hState : CacheState params saved qkvOwner qkvPtr hiddenPtr qkv frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 155 167 168 1536 1536 outputPtr result →
      CacheState params saved qkvOwner qkvPtr hiddenPtr qkv result →
      ByteArrayAt final.mem outputPtr.toNat (cacheUpdate qkv) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 6144) →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 526).take 1 ++ rest) Q initial frame env := by
  rw [emitted_cache]
  apply PackedGenerateLoop.program_spec (value := fun index => word qkv (768 + index))
    (P := CacheState params saved qkvOwner qkvPtr hiddenPtr qkv)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact cacheState_advance params saved qkvOwner qkvPtr hiddenPtr qkv next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact cacheWord_spec env current params saved qkvOwner qkvPtr hiddenPtr outputPtr qkv index next
      (hQkv.writesRange hWrites hSep) hQkvSize hIndex hReady hState Q rest hNext
  · exact hDone

#print axioms cacheWord_spec
#print axioms cacheLoop_spec

end Project.Gpt2CachedStep.CachedBlock
