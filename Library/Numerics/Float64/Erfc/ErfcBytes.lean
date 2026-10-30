import Library.Numerics.Float64.Erfc.ErfcTheorem
import Verified.Call

/-!
The byte theorem for `erfc` in the module of `Erfc.lean`, whose export `erfc` is function 49.
The module writes seven tables from address 4096, all of which `erfc` reads: `Erfc.fastTable` at
4096, `Erfc.accTable` at 13880, `Erfc.expTable` at 24040, `Erfc.asymTable` at 26096,
`Erfc.asymAccTable` at 26728, `Erfc.expAccTable` at 29136, and `Erfc.excTable` at 29368.  A store
is ready when the allocator invariant holds, the seven tables are borrowed arrays at their
addresses, and the memory cap is at most 65,535 pages.  A call of the entry from a ready store
returns without a trap the bits of `Erfc.erfc x` and leaves a ready store, so the theorem covers
every sequence of calls from the initial store.  The bound is that of
`ErfcTheorem.erfc_within_one`: one step of the nearest-even rounding of `erfc x` for finite `x`.
-/

namespace Library.Numerics.Float64.Erfc.ErfcBytes
open Verified (Ready)
open CodeLib.IEEE64
open LeanExe.ProofKit

/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready Erfc.compiled.module Erfc.compiled.tables (Verified.initialHeap Erfc.compiled.tables)
      Erfc.compiled.module.initialStore :=
  Verified.Ready.initial rfl Erfc.compiled.initial

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- A call of the module's `erfc` entry from a ready store. -/
theorem erfc_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Erfc.compiled.module Erfc.compiled.tables heap store) :
    Runs false env Erfc.compiled.module 49 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Erfc.erfc x).toBits] ∧ ∃ heap' : Heap,
        Ready Erfc.compiled.module Erfc.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call Erfc.compiled.erfc.implements Erfc.compiled.tables
    (Verified.tables_at [0, 1, 2, 3, 4, 5, 6] (by decide) rfl)
    env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

/-- Function 49 of the module is its export `erfc`. -/
theorem erfc_export :
    ({ name := "erfc", funcIdx := 49 } : Wasm.Export) ∈ Erfc.compiled.module.exports := by
  decide +kernel

/-- **The accuracy theorem for the compiled `erfc`**: the bytes decode to the module, whose
function 49 is exported as `erfc`, and the initial store is ready.  A call of that entry from a
ready store returns without a trap the bits of `Erfc.erfc x` and leaves a ready store in which every
region of the heap before the call keeps its bytes.  For finite `x` the value lies within one step
of the nearest-even rounding of `erfc x`. -/
theorem erfc_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Erfc.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Erfc.compiled.module ∧
      ({ name := "erfc", funcIdx := 49 } : Wasm.Export) ∈ Erfc.compiled.module.exports ∧
      Ready Erfc.compiled.module Erfc.compiled.tables
        (Verified.initialHeap Erfc.compiled.tables) Erfc.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Erfc.compiled.module Erfc.compiled.tables heap store →
        Wasm.Runs false env Erfc.compiled.module 49 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Erfc.erfc x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (RealErf.erfc (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Erfc.compiled.module Erfc.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Erfc.compiled.bytes
  refine ⟨bytes, henc, hdec, erfc_export, ready_initial,
    fun env heap store x h => (erfc_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Erfc.erfc x).toBits, hv, rfl, ErfcTheorem.erfc_within_one x, hrest⟩

#print axioms ready_initial
#print axioms erfc_entry_call
#print axioms erfc_export
#print axioms erfc_bytes_accuracy

end Library.Numerics.Float64.Erfc.ErfcBytes
