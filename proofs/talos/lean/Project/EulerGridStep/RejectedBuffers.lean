import Project.EulerGridStep.AdvanceRejected
import Project.EulerGridStep.BufferResults

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A rejected advance consumes one free node and leaves the fresh heap unchanged. -/
theorem advanceAt_rejected_reuse_buffers {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused source root allocs releases frees : UInt64)
    (input output : Array UInt64) (index : Nat) (rest : List UInt64)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hRejected : (Model.cellAt ratio input index).status ≠ 0) (hNonempty : 0 < output.size)
    (hState : BufferState initial output.size [⟨source, output⟩] (root :: rest) allocs releases frees)
    (hSource : ObjectsSeparate root output.size source output.size)
    (hFree : ∀ other ∈ rest, ObjectsSeparate root output.size other output.size)
    (hSeparate : ObjectsSeparate root output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 source, .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 root, .i64 root] ∧
        BufferState final output.size [⟨root, Model.advanceAt ratio input output index⟩, ⟨source, output⟩]
          rest (allocs + 1) releases frees ∧
        final.globals.globals[0]? = initial.globals.globals[0]? ∧
        final.mem.pages = initial.mem.pages ∧
        FieldResult (.reuse root (fieldRequest output.size) (rest.headD 0) allocs) initial final source output 0 1 ∧
        UInt64Array.At final pointer input) := by
  have hOutput := hState.liveAt ⟨source, output⟩ (by simp)
  have hValid := freeChain_allocation_valid initial source root allocs output rest hState.chain
    hState.freeHead hState.allocations hSource
  apply (advanceAt_rejected layout (.reuse root (fieldRequest output.size) (rest.headD 0) allocs)
    env initial ratio inputUnused pointer unused source input output index hInput hi hRejected hOutput.2.2
    hNonempty hValid hState.pages hSeparate).mono
  rintro final values ⟨hValues, _, hResult, hInputFinal⟩
  have hLive : ∀ (buffer : LiveBuffer), buffer ∈ [⟨source, output⟩] → ObjectsSeparate root output.size buffer.root output.size := by
    intro buffer hb
    obtain rfl := List.mem_singleton.mp hb
    exact hSource
  obtain ⟨hBuffers, hHeap⟩ := hResult.reused_buffers hState hLive hFree
  exact ⟨hValues, by simpa [Model.advanceAt, hRejected] using hBuffers,
    hHeap, hResult.pages, hResult, hInputFinal⟩

/-- A first rejected advance allocates one fresh status clone with no intermediate releases. -/
theorem advanceAt_rejected_fresh_buffers {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused source heapTop allocs releases frees : UInt64)
    (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hRejected : (Model.cellAt ratio input index).status ≠ 0) (hNonempty : 0 < output.size)
    (hState : BufferState initial output.size [⟨source, output⟩] [] allocs releases frees)
    (hValid : (FieldAllocation.fresh heapTop allocs).Valid initial source output)
    (hSource : ObjectsSeparate (heapTop + 48) output.size source output.size)
    (hSeparate : ObjectsSeparate (heapTop + 48) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 source, .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 (heapTop + 48), .i64 (heapTop + 48)] ∧
        BufferState final output.size
          [⟨heapTop + 48, Model.advanceAt ratio input output index⟩, ⟨source, output⟩]
          [] (allocs + 1) releases frees ∧
        final.globals.globals[0]? = some (.i64 (heapTop + 48 + fieldRequest output.size)) ∧
        final.mem.pages = initial.mem.pages ∧
        FieldResult (.fresh heapTop allocs) initial final source output 0 1 ∧ UInt64Array.At final pointer input) := by
  have hOutput := hState.liveAt ⟨source, output⟩ (by simp)
  apply (advanceAt_rejected layout (.fresh heapTop allocs) env initial ratio inputUnused pointer unused source
    input output index hInput hi hRejected hOutput.2.2 hNonempty hValid hState.pages hSeparate).mono
  rintro final values ⟨hValues, _, hResult, hInputFinal⟩
  have hLive : ∀ (buffer : LiveBuffer), buffer ∈ [⟨source, output⟩] →
      ObjectsSeparate (heapTop + 48) output.size buffer.root output.size := by
    intro buffer hb
    obtain rfl := List.mem_singleton.mp hb
    exact hSource
  obtain ⟨hBuffers, hHeap⟩ := hResult.fresh_buffers hState hLive
  exact ⟨hValues, by simpa [Model.advanceAt, hRejected] using hBuffers,
    hHeap, hResult.pages, hResult, hInputFinal⟩

#print axioms advanceAt_rejected_reuse_buffers
#print axioms advanceAt_rejected_fresh_buffers
end Project.EulerGridStep.Execution
