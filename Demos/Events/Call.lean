import Demos.Events.Verified
import Verified.Call

/-! The call of the compiled event-window program (C1).  `events_callSpec` states that function
85, the export `events`, returns `events xs` without a trap from every ready store in which the
allocator's `top` can rise by `compiled.events.bound xs` bytes within the memory cap.
`events_call` states it for a host: the module's bytes decode to the module, its start store is
ready, and from a ready store with the input's bit patterns borrowed, the export returns a new
array that holds the bit patterns of `events xs`, to which the theorems of `Soundness.lean`
apply. -/

namespace Demos.Events

open Wasm LeanExe.Pipeline

theorem events_export :
    ({ name := "events", funcIdx := 85 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- **C1.**  Function 85 returns `events xs` from every ready store in which `top` can rise by
`compiled.events.bound xs` bytes within the memory cap, and `top` rises by at most that much. -/
theorem events_callSpec :
    _root_.Verified.CallSpec compiled.module compiled.tables 85 events compiled.events.bound :=
  _root_.Verified.ImplementsTables.call compiled.events.trapFree compiled.tables
    (_root_.Verified.tables_at [0, 1] (by decide) rfl)

/-- C1 over the bit patterns: an `Array Float` is represented by the array of its elements' bit
patterns, so function 85 returns the bit patterns of `events xs`. -/
theorem events_callBits :
    _root_.Verified.CallSpec compiled.module compiled.tables 85
      (fun xs : Array Float => (events xs).map Float.toBits) compiled.events.bound :=
  events_callSpec

/-- The bytes of `compiled.module` decode to the module, whose export `events` is function 85
and whose start store is ready.  Called from a ready store with the bit patterns of an input
`xs` borrowed at `ptr` and room for `top` to rise by `compiled.events.bound xs` bytes, function
85 returns without a trap the address of a new array that holds the bit patterns of
`events xs`, and it leaves a ready store in which the input stays borrowed. -/
theorem events_call :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
    ({ name := "events", funcIdx := 85 } : Wasm.Export) ∈ compiled.module.exports ∧
    _root_.Verified.Ready compiled.module compiled.tables
      (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore ∧
    ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (xs : Array Float) (ptr : UInt64),
      _root_.Verified.Ready compiled.module compiled.tables heap store →
      heap.Borrowed store ptr (xs.map Float.toBits) →
      heap.Within store compiled.module (compiled.events.bound xs) →
      Runs false env compiled.module 85 store [.i64 ptr] fun final values =>
        ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap,
          heap'.Owned final optr ((events xs).map Float.toBits) ∧
          _root_.Verified.Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr (xs.map Float.toBits) ∧
          heap'.top.toNat ≤ heap.top.toNat + compiled.events.bound xs := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  refine ⟨⟨bytes, henc, hdec⟩, events_export, _root_.Verified.Ready.initial rfl compiled.initial,
    fun env heap store xs ptr hR hb hroom => ?_⟩
  exact (_root_.Verified.Call.array events_callBits env heap store [.i64 ptr] xs hR
    ⟨ptr, rfl, hb⟩ rfl hroom).mono fun _ _ ⟨optr, hv, heap', hown, hR', hkept, _, hrise⟩ =>
      ⟨optr, hv, heap', hown, hR', hkept _ _ hb, hrise⟩

end Demos.Events
