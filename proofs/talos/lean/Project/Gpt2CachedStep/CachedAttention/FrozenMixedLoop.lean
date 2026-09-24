import Project.Gpt2CachedStep.CachedAttention.FrozenMixedStep

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def mixedWord : Wasm.Program := (mixedBody.drop 12).take 27

set_option maxRecDepth 32768 in
theorem emitted_mixed_fold : mixedWord = mixedWord.take 21 ++
    RangeFoldLoop.program 111 112 mixedStep ++ mixedWord.drop 22 := rfl

set_option maxRecDepth 32768 in
theorem emitted_mixed : (func29.drop 320).take 1 = PackedGenerateLoop.program 77 109 110 mixedWord := rfl

set_option maxRecDepth 32768 in
theorem mixedWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (cacheOwner qkvOwner cachePtr qkvPtr probabilityPtr outputPtr : UInt64)
    (cache qkv probabilityValues : ByteArray) (saved : List Wasm.Value)
    (layer position index : Nat) (frame : Locals)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hProbabilities : ByteArrayAt initial.mem probabilityPtr.toNat probabilityValues)
    (hLayer : layer < 12) (hPosition : position < 128) (hIndex : index < 768)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hProbabilitySize : 4 * (12 * (position + 1)) ≤ probabilityValues.size)
    (hReady : PackedGenerateLoop.Ready 77 109 110 768 index outputPtr frame)
    (hState : MixedState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
      saved probabilityPtr probabilityValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 77 109 110 768 index outputPtr result →
      MixedState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
        saved probabilityPtr probabilityValues position result →
      wp «module» rest Q initial { result with values :=
        [.i64 (mixedPrefix cache qkv probabilityValues layer position index (position + 1)).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (mixedWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hSize, hProbabilityOwner, hProbabilityPtr, hProbabilityBytes,
    hBytes, hTyped, hPrefix⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[69]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[101]? = some (.i64 3072) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[102]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  have hDiv : UInt64.ofNat index / 64 = UInt64.ofNat (index / 64) :=
    (UInt64.ofNat_div (by change index < 18446744073709551616; omega) (by decide)).symm
  rw [emitted_mixed_fold]
  simp only [List.append_assoc, mixedWord, mixedBody, func29,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop,
    List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength, hCounter, hSize, hDiv]
  apply RangeFoldLoop.program_spec_with_stack
    (values := [.i32 (PackedGenerateLoop.address outputPtr index)]) (count := position + 1)
    (P := fun source => MixedFoldState
      (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
      saved cache qkv probabilityValues probabilityPtr outputPtr layer position index source)
  · change position + 1 < 18446744073709551616
    omega
  · simp [RangeFoldLoop.Ready, Locals.get, hLength]
  · simp (config := { maxDischargeDepth := 64 }) only [MixedFoldState, MixedState, parameters,
      hLength, List.length_set, List.getElem?_set, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
      hSize, hProbabilityOwner, hProbabilityPtr, hProbabilityBytes, hBytes, hCounter,
      hLengthLocal, hPointer, mixedPrefix_zero, I64Values.set, hTyped,
      List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]
    decide
  · intro source next hSource hReady hState Q rest hNext
    exact mixedStep_spec env initial cacheOwner qkvOwner cachePtr qkvPtr probabilityPtr outputPtr
      cache qkv probabilityValues saved layer position index source next
      [.i32 (PackedGenerateLoop.address outputPtr index)] hCache hQkv hProbabilities hLayer hPosition hIndex hSource
      hCacheSize hQkvSize hProbabilitySize hReady hState Q rest hNext
  · intro result hReady hState
    rcases hState with ⟨⟨hResultParams, hResultLength, hResultSize, hProbabilityOwner, hProbabilityPtr, hProbabilityBytes,
      hByteLength, hResultTyped, hResultPrefix⟩, hIndexLocal, _, hTotal, hSizeLocal, hPtr, _⟩
    simp only [parameters] at hResultParams
    wp_packed_frame [hResultParams, hResultLength, hTotal, hReady.1]
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 77 109 110 768 index outputPtr result ∧
        MixedState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
          saved probabilityPtr probabilityValues position result)
      (R := fun result => wp «module» rest Q initial result env)
      (values := [.i64 (mixedPrefix cache qkv probabilityValues layer position index (position + 1)).toUInt64,
        .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
    · constructor
      · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
          hResultLength, List.length_set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
          Nat.reduceEqDiff, hIndexLocal, hSizeLocal, hPtr, true_and,
          show UInt64.ofNat (4 * 768) = 3072 from rfl]
      · simp (config := { maxDischargeDepth := 64 }) only [MixedState, parameters, hResultLength,
          List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte,
          hResultSize, hProbabilityOwner, hProbabilityPtr, hProbabilityBytes, hByteLength,
          I64Values.set, hResultTyped, List.take_set_of_le, Nat.reduceLeDiff, hResultPrefix, and_self]
    · intro next h
      exact hNext next h.1 h.2

theorem mixedState_advance (params saved : List Wasm.Value) (probabilityPtr : UInt64)
    (probabilityValues : ByteArray) (position : Nat) (hParams : params.length = 8)
    (frame : Locals) (index : Nat) (hValid : frame.validIndex 77)
    (hState : MixedState params saved probabilityPtr probabilityValues position frame) :
    MixedState params saved probabilityPtr probabilityValues position (FixedArrayCopy.counterFrame frame 77 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hSize, hOwner, hPtr, hInputBytes, hBytes, hTyped, hPrefix⟩
  simp (config := { maxDischargeDepth := 64 }) only [MixedState, FixedArrayCopy.counterFrame, Locals.set,
    hFrameParams, hParams, hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hSize, hOwner, hPtr, hInputBytes, hBytes,
    I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]

set_option maxRecDepth 32768 in
theorem mixedLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (cacheOwner qkvOwner cachePtr qkvPtr probabilityPtr outputPtr : UInt64)
    (cache qkv probabilityValues : ByteArray) (saved : List Wasm.Value) (layer position : Nat) (frame : Locals)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hProbabilities : ByteArrayAt initial.mem probabilityPtr.toNat probabilityValues)
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hProbabilitySize : 4 * (12 * (position + 1)) ≤ probabilityValues.size)
    (hFit : outputPtr.toNat + 3072 ≤ 2^32)
    (hMemory : outputPtr.toNat + 3072 ≤ initial.mem.pages * 65536)
    (hCacheSep : cachePtr.toNat + cache.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 3072 ≤ cachePtr.toNat)
    (hQkvSep : qkvPtr.toNat + qkv.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 3072 ≤ qkvPtr.toNat)
    (hProbabilitySep : probabilityPtr.toNat + probabilityValues.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 3072 ≤ probabilityPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 77 109 110 768 0 outputPtr frame)
    (hState : MixedState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
      saved probabilityPtr probabilityValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 77 109 110 768 768 outputPtr result →
      MixedState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
        saved probabilityPtr probabilityValues position result →
      ByteArrayAt final.mem outputPtr.toNat (mixed cache qkv probabilityValues layer position) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 3072) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 320).take 1 ++ rest) Q initial frame env := by
  rw [emitted_mixed]
  apply PackedGenerateLoop.program_spec
    (value := fun index => mixedPrefix cache qkv probabilityValues layer position index (position + 1))
    (P := MixedState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
      saved probabilityPtr probabilityValues position)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact mixedState_advance _ saved probabilityPtr probabilityValues position rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact mixedWord_spec env current cacheOwner qkvOwner cachePtr qkvPtr probabilityPtr outputPtr
      cache qkv probabilityValues saved layer position index next
      (hCache.writesRange hWrites hCacheSep) (hQkv.writesRange hWrites hQkvSep)
      (hProbabilities.writesRange hWrites hProbabilitySep)
      hLayer hPosition hIndex hCacheSize hQkvSize hProbabilitySize hReady hState Q rest hNext
  · exact hDone

#print axioms mixedWord_spec
#print axioms mixedLoop_spec

end Project.Gpt2CachedStep.Frozen.CachedAttention
