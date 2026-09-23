import Project.Gpt2QuantizedCached.CachedBlock.FiniteGuard
import Project.Gpt2QuantizedCached.CachedBlock.Release
import Project.Gpt2QuantizedCached.CachedBlock.ResultTransfer

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open PackedReleaseMany (Owners Bindings)

theorem guardedRelease_spec (env : HostEnv Unit) (before heap successHeap : Heap)
    (original initial : Store Unit) (params : List Value) (frame : Locals)
    (items : List PackedReleaseMany.Item) (hidden cache : FreeNode) (hiddenBytes cacheBytes : ByteArray)
    (owner ptr : UInt64) (input : ByteArray) (count source : Nat) (success : Program) (successAccepted : Bool)
    (hHeap : heap.At initial) (hFrame : before.Frame original heap initial)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hOwners : Owners before heap initial items) (hBindings : Bindings items frame)
    (hIndices : ∀ item ∈ items, item.ownerLocal < 11 + (source + 3))
    (hInput : ByteArrayAt initial.mem ptr.toNat input) (hExtent : count * 4 ≤ input.size)
    (hSource : source = 13 ∨ source = 51 ∨ source = 102 ∨ source = 135)
    (hParams : frame.params = params) (hParamLength : params.length = 11)
    (hLength : frame.locals.length = 193) (hValues : frame.values = [])
    (hOwner : frame.locals[source]? = some (.i64 owner))
    (hPtr : frame.locals[source + 1]? = some (.i64 ptr))
    (hBytes : frame.locals[source + 2]? = some (.i64 (UInt64.ofNat input.size)))
    (hTyped : I64Values frame.locals)
    (hSuccess : ∀ prepared, prepared.params = frame.params → prepared.locals.length = 193 →
      I64Values prepared.locals → prepared.locals.take (source + 3) = frame.locals.take (source + 3) →
      prepared.values = [] → ∀ R : Assertion Unit,
      (∀ final result, ResultState params (frame.locals.take (source + 3)) (source + 3) successAccepted
        hidden.root cache.root result →
        Completion heap initial successHeap final successAccepted hidden cache hiddenBytes cacheBytes →
        R (.Fallthrough final result)) → wp «module» success R initial prepared env)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      ResultState params (frame.locals.take (source + 3)) (source + 3) (finiteWords input 0 count && successAccepted)
        hidden.root cache.root result →
      Completion before original
        (PackedReleaseMany.finalHeap (if finiteWords input 0 count then successHeap else heap) items)
        final (finiteWords input 0 count && successAccepted) hidden cache hiddenBytes cacheBytes →
      wp «module» rest Q final result env) :
    wp «module» (finiteTestCode source count ++ [.iff 0 0 failureCode success] ++
      releaseCode (items.map (·.ownerLocal)) ++ rest) Q initial frame env := by
  have hBound : source + 3 ≤ 178 := by rcases hSource with rfl | rfl | rfl | rfl <;> decide
  have finish (next : Heap) (final : Store Unit) (result : Locals) (accepted : Bool)
      (hState : ResultState params (frame.locals.take (source + 3)) (source + 3) accepted hidden.root cache.root result)
      (hOutput : Completion heap initial next final accepted hidden cache hiddenBytes cacheBytes)
      (hNext' : Completion before original (PackedReleaseMany.finalHeap next items)
          (PackedReleaseMany.finalStore next final items) accepted hidden cache hiddenBytes cacheBytes →
        wp «module» rest Q (PackedReleaseMany.finalStore next final items) result env) :
      wp «module» (releaseCode (items.map (·.ownerLocal)) ++ rest) Q final result env := by
    apply release_spec env before next original final params (frame.locals.take (source + 3))
      (source + 3) accepted hidden cache hiddenBytes cacheBytes result items
      (hOutput.trans hFrame hCap) (hOwners.frame hOutput.frame hOutput.heapAt)
      (hState.bindings rfl hBindings hParams hLength (by omega) (by simpa only [hParamLength] using hIndices))
      (fun ha => hOwners.disjoint_fresh (hOutput.outputs ha).1 (hOutput.fresh ha).1)
      (fun ha => hOwners.disjoint_fresh (hOutput.outputs ha).2 (hOutput.fresh ha).2)
      hState hParamLength _ _ hNext'
  simp only [List.append_assoc]
  apply finiteGuard_spec env initial owner ptr input count source hInput hExtent hSource
    frame (by rw [hParams, hParamLength]) hLength hValues hOwner hPtr hBytes hTyped
  intro prepared hPreparedParams hPreparedLength hPreparedTyped hPrefix hPreparedValues
  cases hFinite : finiteWords input 0 count
  · simp only [hFinite, Bool.false_eq_true, ite_false, Bool.false_and] at hNext ⊢
    rw [← List.append_nil failureCode]
    apply failure_spec env initial prepared params (source + 3) hidden.root cache.root
      (hPreparedParams.trans hParams) hParamLength hPreparedLength hPreparedValues hPreparedTyped hBound
    intro result hState
    rw [hPrefix] at hState
    simp only [wp_nil]
    have hRun := finish heap initial result false hState
      (Completion.failure heap initial hidden cache hiddenBytes cacheBytes hHeap hPages)
      (hNext _ _ hState)
    simpa only [← hState.values] using hRun
  · simp only [hFinite, ite_true, Bool.true_and] at hNext ⊢
    apply hSuccess prepared hPreparedParams hPreparedLength hPreparedTyped hPrefix hPreparedValues
    intro final result hState hOutput
    have hRun := finish successHeap final result successAccepted hState hOutput
      (hNext _ _ hState)
    simpa only [← hState.values] using hRun

#print axioms guardedRelease_spec
end Project.Gpt2QuantizedCached.CachedBlock
