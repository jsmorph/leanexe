import Project.Gpt2CachedStep.CachedAttention.Source
import Project.Gpt2CachedStep.CachedScore.Spec
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.CachedAttention
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def parameters (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position : Nat) : List Wasm.Value :=
  [.i64 cacheOwner, .i64 cachePtr, .i64 (UInt64.ofNat cache.size),
    .i64 qkvOwner, .i64 qkvPtr, .i64 (UInt64.ofNat qkv.size),
    .i64 (UInt64.ofNat layer), .i64 (UInt64.ofNat position)]

def scoresBody : Wasm.Program :=
  match (func29[61]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def scoresWord : Wasm.Program := (scoresBody.drop 12).take (scoresBody.length - 19)

set_option maxRecDepth 32768 in
theorem emitted_scores : (func29.drop 61).take 1 = PackedGenerateLoop.program 10 109 110 scoresWord := rfl

def ScoresState (params : List Wasm.Value) (position : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 114 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (position + 1))) ∧
  frame.locals[1]? = some (.i64 (UInt64.ofNat (4 * (12 * (position + 1))))) ∧ I64Values frame.locals

set_option maxRecDepth 32768 in
theorem scoresWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (cacheOwner qkvOwner cachePtr qkvPtr outputPtr : UInt64) (cache qkv : ByteArray)
    (layer position index : Nat) (frame : Locals)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hIndex : index < 12 * (position + 1))
    (hReady : PackedGenerateLoop.Ready 10 109 110 (12 * (position + 1)) index outputPtr frame)
    (hState : ScoresState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position) position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 10 109 110 (12 * (position + 1)) index outputPtr result →
      ScoresState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position) position result →
      wp «module» rest Q initial { result with values :=
        [.i64 (cachedScore cache qkv layer position (index % (position + 1)) (index / (position + 1))).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (scoresWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hSize, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[2]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[101]? = some (.i64 (UInt64.ofNat (4 * (12 * (position + 1))))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[102]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  have hSize64 : position + 1 < 2^64 := by omega
  have hIndex64 : index < 2^64 := by omega
  have hNonzero : UInt64.ofNat (position + 1) ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hSize64] at this
    change position + 1 = 0 at this
    omega
  have hDiv : UInt64.ofNat index / UInt64.ofNat (position + 1) =
      UInt64.ofNat (index / (position + 1)) := (UInt64.ofNat_div hIndex64 hSize64).symm
  have hRem : UInt64.ofNat index % UInt64.ofNat (position + 1) =
      UInt64.ofNat (index % (position + 1)) := (UInt64.ofNat_mod hIndex64 hSize64).symm
  simp only [scoresWord, scoresBody, func29, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter, hSize]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hNonzero)]
  wp_packed_frame [hParams, hLength, hCounter, hSize, hNonzero, hRem]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength, hCounter, hSize, hNonzero, hDiv]
  refine wp_call_tw ((CachedScore.Spec.cachedScore_exact env initial cacheOwner qkvOwner cachePtr qkvPtr
    cache qkv layer position (index % (position + 1)) (index / (position + 1))
    hCache hQkv hLayer (Nat.le_of_lt_succ (Nat.mod_lt index (Nat.succ_pos position)))
    ((Nat.div_lt_iff_lt_mul (Nat.succ_pos position)).mpr hIndex) hCacheSize hQkvSize).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 10 109 110 (12 * (position + 1)) index outputPtr result ∧
      ScoresState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position) position result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (cachedScore cache qkv layer position (index % (position + 1)) (index / (position + 1))).toUInt64,
      .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
    · simp (config := { maxDischargeDepth := 64 }) only [ScoresState, parameters, hLength, List.length_set,
        List.getElem?_set, Nat.reduceEqDiff, reduceIte, hSize, hBytes, I64Values.set, hTyped, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem scoresState_advance (params : List Wasm.Value) (position : Nat) (hParams : params.length = 8)
    (frame : Locals) (index : Nat) (hValid : frame.validIndex 10)
    (hState : ScoresState params position frame) :
    ScoresState params position (FixedArrayCopy.counterFrame frame 10 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hSize, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [ScoresState, FixedArrayCopy.counterFrame, Locals.set,
    hFrameParams, hParams, hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hSize, hBytes, I64Values.set, hTyped, and_self]

set_option maxRecDepth 32768 in
theorem scoresLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (cacheOwner qkvOwner cachePtr qkvPtr outputPtr : UInt64) (cache qkv : ByteArray)
    (layer position : Nat) (frame : Locals)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hFit : outputPtr.toNat + 4 * (12 * (position + 1)) ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * (12 * (position + 1)) ≤ initial.mem.pages * 65536)
    (hCacheSep : cachePtr.toNat + cache.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (12 * (position + 1)) ≤ cachePtr.toNat)
    (hQkvSep : qkvPtr.toNat + qkv.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (12 * (position + 1)) ≤ qkvPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 10 109 110 (12 * (position + 1)) 0 outputPtr frame)
    (hState : ScoresState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position) position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 10 109 110 (12 * (position + 1)) (12 * (position + 1)) outputPtr result →
      ScoresState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position) position result →
      ByteArrayAt final.mem outputPtr.toNat (scores cache qkv layer position) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * (12 * (position + 1))) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 61).take 1 ++ rest) Q initial frame env := by
  rw [emitted_scores]
  apply PackedGenerateLoop.program_spec
    (value := fun index => cachedScore cache qkv layer position (index % (position + 1)) (index / (position + 1)))
    (P := ScoresState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position) position)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact scoresState_advance _ position rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact scoresWord_spec env current cacheOwner qkvOwner cachePtr qkvPtr outputPtr cache qkv
      layer position index next (hCache.writesRange hWrites hCacheSep) (hQkv.writesRange hWrites hQkvSep)
      hLayer hPosition hCacheSize hQkvSize hIndex hReady hState Q rest hNext
  · exact hDone

#print axioms scoresWord_spec
#print axioms scoresLoop_spec

end Project.Gpt2CachedStep.CachedAttention
