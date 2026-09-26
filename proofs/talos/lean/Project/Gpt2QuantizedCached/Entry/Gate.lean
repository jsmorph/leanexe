import Project.Gpt2QuantizedCached.Entry.Accepted

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def selectResult (rejected : Bool) (status : UInt64) (result : CachedResult) : CachedResult :=
  if rejected then ⟨status, .empty, .empty⟩ else result

def selectHeap (rejected : Bool) (before after : Heap) : Heap := if rejected then before else after

theorem gate_spec (env : HostEnv Unit) (initial : Store Unit) (heap successHeap : Heap)
    (params : List Value) (cache logits : FreeNode) (output : CachedResult)
    (test success : Program) (rejected : Bool) (status : UInt64) (frame : Locals)
    (hHeap : heap.At initial) (hPages : initial.mem.pages ≤ 65536)
    (hParams : params.length = 8) (hStatus : status ≠ 0)
    (hTest : ∀ (R : Assertion Unit) (tail : Program),
      (∀ checked, State params { checked with values := [] } →
        checked.values = [.i32 (if rejected then 1 else 0)] → wp «module» tail R initial checked env) →
      wp «module» (test ++ tail) R initial frame env)
    (hSuccess : rejected = false → ∀ prepared, State params prepared → ∀ R : Assertion Unit,
      (∀ final result, ResultState params output.status (statusRoot output.status cache) (statusRoot output.status logits)
        output.cache.size output.logits.size result →
        Completion heap initial successHeap final output.status cache logits output.cache output.logits →
        R (.Fallthrough final result)) → wp «module» success R initial prepared env)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let selected := selectResult rejected status output
      ResultState params selected.status (statusRoot selected.status cache) (statusRoot selected.status logits)
        selected.cache.size selected.logits.size result →
      Completion heap initial (selectHeap rejected heap successHeap) final selected.status cache logits selected.cache selected.logits →
      wp «module» rest Q final result env) :
    wp «module» (test ++ [.iff 0 0 (failureResultCode (.constI64 status)) success] ++ rest) Q initial frame env := by
  rw [List.append_assoc]
  apply hTest
  intro checked hChecked hValues
  apply boolBranch_spec env initial checked rejected hValues
  cases hRejected : rejected
  · simp only [hRejected, Bool.false_eq_true, ite_false]
    apply hSuccess hRejected _ hChecked
    intro final result hResult hMemory
    simp only [PackedReleaseFilter.afterAction]
    have hRun := hNext final result
    simp only [selectResult, selectHeap, hRejected, Bool.false_eq_true, ite_false] at hRun
    simpa only [← hResult.values] using hRun hResult hMemory
  · simp only [hRejected, ite_true]
    rw [← List.append_nil (failureResultCode (.constI64 status))]
    apply failureResult_spec env initial params status (.constI64 status) { checked with values := [] }
      hParams hChecked (Or.inl rfl)
    intro result hResult _
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hRun := hNext initial result
    simp only [selectResult, selectHeap, hRejected, ite_true, statusRoot, hStatus, ite_false, ByteArray.size_empty] at hRun
    simpa only [← hResult.values] using hRun hResult
      (Completion.failure heap heap initial initial status cache logits hStatus hHeap (Heap.Frame.refl _ _) hPages rfl)

#print axioms gate_spec
end Project.Gpt2QuantizedCached.Entry
