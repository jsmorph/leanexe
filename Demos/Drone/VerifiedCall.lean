import Demos.Drone.Verified
import Verified.Call

/-! The call of the verified drone planner from a ready store.  `drone_trapFree` states that entry
18 computes `compute` without a trap when `top` can rise by 2,251,064 bytes within the memory cap,
the constant of `compute_bound`.  `drone_compute_call` states it for a host: the store in which
the module starts is ready, and from a ready store with the terrain borrowed below address 8192
and a memory cap of at least 35 pages, the export `compute` returns a new array that holds
`compute terrain`. -/

namespace Demos.Drone.Verified

open Wasm LeanExe.Pipeline _root_.Demos.Drone

/-- Entry 18 computes `compute` from every ready store in which `top` can rise by 2,251,064 bytes
within the memory cap, and `top` rises by at most that much. -/
theorem compute_callSpec :
    _root_.Verified.CallSpec compiled.module compiled.tables 18 compute fun _ => 2251064 :=
  _root_.Verified.ImplementsTables.call (_root_.Verified.ImplementsTables.ofA drone_trapFree)
    compiled.tables nofun

theorem compute_export :
    ({ name := "compute", funcIdx := 18 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The store in which the module starts, with the memory cap set to `cap` pages, is ready.  The
module has no tables. -/
theorem ready_initial (cap : Nat) (hcap : cap ≤ 65535) :
    _root_.Verified.Ready compiled.module compiled.tables
      (_root_.Verified.initialHeap compiled.tables)
      { (compiled.module.initialStore : Store Unit) with memoryCaps := [cap] } := by
  obtain ⟨hAt, -, -⟩ := _root_.Verified.Ready.initial rfl compiled.initial
  exact ⟨⟨hAt.globals, hAt.freeList, hAt.base, hAt.top, hAt.pages, hAt.above, hAt.below⟩,
    hcap, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

/-- The bytes of `compiled.module` decode to the module, whose export `compute` is entry 18.  The
store in which the module starts, with a memory cap of at most 65,535 pages, is ready.  Called
from a ready store with a terrain borrowed below address 8192 and a memory cap of at least 35
pages, entry 18 returns without a trap the address of a new array that holds `compute terrain`.
It leaves a ready store in which the terrain stays borrowed and `top` has risen by at most
2,251,064 bytes. -/
theorem drone_compute_call :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
    ({ name := "compute", funcIdx := 18 } : Wasm.Export) ∈ compiled.module.exports ∧
    (∀ cap, cap ≤ 65535 → _root_.Verified.Ready compiled.module compiled.tables
      (_root_.Verified.initialHeap compiled.tables)
      { (compiled.module.initialStore : Store Unit) with memoryCaps := [cap] }) ∧
    ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (terrain : Array UInt64)
      (ptr : UInt64), _root_.Verified.Ready compiled.module compiled.tables heap store →
      heap.Borrowed store ptr terrain → heap.top.toNat ≤ 8192 →
      35 ≤ store.memoryCap compiled.module 0 →
      Runs false env compiled.module 18 store [.i64 ptr] fun final values =>
        ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap,
          heap'.Owned final optr (compute terrain) ∧
          _root_.Verified.Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr terrain ∧ heap'.top.toNat ≤ heap.top.toNat + 2251064 := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  refine ⟨⟨bytes, henc, hdec⟩, compute_export, ready_initial,
    fun env heap store terrain ptr hR hb htop hcap => ?_⟩
  refine (_root_.Verified.Call.array compute_callSpec env heap store [.i64 ptr] terrain hR
    ⟨ptr, rfl, hb⟩ rfl ?_).mono fun _ _ ⟨optr, hv, heap', hown, hR', hkept, _, hrise⟩ =>
      ⟨optr, hv, heap', hown, hR', hkept _ _ hb, hrise⟩
  show heap.top.toNat + 2251064 ≤ 65536 * store.memoryCap compiled.module 0
  omega

#print axioms compute_callSpec
#print axioms compute_export
#print axioms ready_initial
#print axioms drone_compute_call

end Demos.Drone.Verified
