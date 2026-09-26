import Project.Gpt2QuantizedCached.CachedHidden.Code
import Project.Gpt2QuantizedCached.Embedding.Spec

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def parameters (weightsOwner weightsPtr cacheOwner cachePtr : UInt64)
    (weights cache : ByteArray) (token : UInt32) (position : Nat) : List Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
   .i64 cacheOwner, .i64 cachePtr, .i64 (UInt64.ofNat cache.size),
   .i64 token.toUInt64, .i64 (UInt64.ofNat position)]

structure LayerFrame (params : List Value) (embedding hidden updates : UInt64)
    (hiddenSize updatesSize : Nat) (status : UInt64) (layer : Nat) (frame : Locals) : Prop where
  paramsEq : frame.params = params
  length : frame.locals.length = 141
  values : frame.values = []
  typed : I64Values frame.locals
  embeddingOwner : frame.locals[5]? = some (.i64 (embedding))
  embeddingPtr : frame.locals[6]? = some (.i64 (embedding))
  embeddingSize : frame.locals[7]? = some (.i64 (3072))
  protectedEmbedding : frame.locals[134]? = some (.i64 (embedding))
  protectedUpdates : frame.locals[137]? = some (.i64 (0))
  hiddenOwner : frame.locals[15]? = some (.i64 (hidden))
  hiddenPtr : frame.locals[16]? = some (.i64 (hidden))
  hiddenSize : frame.locals[17]? = some (.i64 (UInt64.ofNat hiddenSize))
  updatesOwner : frame.locals[18]? = some (.i64 (updates))
  updatesPtr : frame.locals[19]? = some (.i64 (updates))
  updatesSize : frame.locals[20]? = some (.i64 (UInt64.ofNat updatesSize))
  status : frame.locals[21]? = some (.i64 (status))
  counter : frame.locals[110]? = some (.i64 (UInt64.ofNat layer))
  limit : frame.locals[111]? = some (.i64 (12))
  step : frame.locals[112]? = some (.i64 (1))

theorem embedding_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hScaleSize : tokenScaleOffset + token.toNat * 4 + 4 ≤ weights.size)
    (hTokenSize : tokenWeightOffset + token.toNat * 768 + 768 ≤ weights.size)
    (hPositionSize : positionOffset + (position * 768 + 768) * 4 ≤ weights.size)
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hBump : takeFirstFitFrom 0 Embedding.need heap.nodes = none →
      heap.top.toNat + 48 + Embedding.need.toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top Embedding.need ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
    (hLocals : frame.locals.length = 141) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      let node := allocatedNode heap.top Embedding.need heap.nodes
      LayerFrame (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        node.root node.root 0 3072 0 0 0 result →
      (heap.allocate Embedding.need).At final →
      (heap.allocate Embedding.need).OwnsPacked final node (embedding weights token position) →
      heap.Frame initial (heap.allocate Embedding.need) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» (embeddingCode ++ rest) Q initial frame env := by
  simp only [embeddingCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues]
  refine wp_call_tw (Embedding.Spec.embedding_exact env initial heap weightsOwner weightsPtr
    weights token position hHeap hWeights hScaleSize hTokenSize hPositionSize hToken hPosition
    hWeightsProtected hBump hPages) ?_
  rintro final returned ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  have hSize : (embedding weights token position).size = 3072 := by
    rw [embedding, PackedSource.generate_size]
  rw [hSize] at hReturned
  subst returned
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · constructor <;>
      simp (config := { maxDischargeDepth := 64 }) only [parameters, hLocals, List.length_set,
        List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, I64Values.set, hTyped,
        show UInt64.ofNat 3072 = 3072 from rfl, show UInt64.ofNat 0 = 0 from rfl]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms embedding_spec
end Project.Gpt2QuantizedCached.CachedHidden
