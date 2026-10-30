import Library.Numerics.Float64.Tanh.Expm1Special
import Library.Numerics.Float64.Tanh.TanhSpecial
import Verified.Call

/-!
The byte theorems for the module of `Tanh.lean`, whose exports `expm1` (function 3) and `tanh`
(function 4) read no tables.  A store is ready when the allocator invariant holds and the memory
cap is at most 65,535 pages.  A call of either entry from a ready store returns without a trap the
bits of the Lean function and leaves a ready store, so the theorems cover every sequence of calls
to the two entries from the initial store.  `tanh_module_accuracy` states both, for the file
theorem's axiom report.
-/

namespace Library.Numerics.Float64.Tanh.TanhBytes
open Verified (Ready)
open CodeLib.IEEE64
open LeanExe.ProofKit

/-- The store in which the module starts is ready. -/
theorem ready_initial :
    Ready Tanh.compiled.module Tanh.compiled.tables (Verified.initialHeap Tanh.compiled.tables)
      Tanh.compiled.module.initialStore :=
  Verified.Ready.initial rfl Tanh.compiled.initial

open Wasm LeanExe.Pipeline in
/-- A call of the module's `expm1` entry from a ready store. -/
theorem expm1_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Tanh.compiled.module Tanh.compiled.tables heap store) :
    Runs false env Tanh.compiled.module 3 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Tanh.expm1 x).toBits] ∧ ∃ heap' : Heap,
        Ready Tanh.compiled.module Tanh.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA Tanh.compiled.expm1.implements) Tanh.compiled.tables
    nofun env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `tanh` entry from a ready store. -/
theorem tanh_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Tanh.compiled.module Tanh.compiled.tables heap store) :
    Runs false env Tanh.compiled.module 4 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Tanh.tanh x).toBits] ∧ ∃ heap' : Heap,
        Ready Tanh.compiled.module Tanh.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA Tanh.compiled.tanh.implements) Tanh.compiled.tables
    nofun env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

/-- Function 3 of the module is its export `expm1`. -/
theorem expm1_export :
    ({ name := "expm1", funcIdx := 3 } : Wasm.Export) ∈ Tanh.compiled.module.exports := by
  decide +kernel

/-- Function 4 of the module is its export `tanh`. -/
theorem tanh_export :
    ({ name := "tanh", funcIdx := 4 } : Wasm.Export) ∈ Tanh.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `expm1`: the bytes decode to the module, whose function
3 is exported as `expm1`, and the initial store is ready.  A call of that entry from a ready store
returns without a trap the bits of `Tanh.expm1 x` and leaves a ready store in which every region
of the heap before the call keeps its bytes.  For finite `x` the bits lie within one
representable step of the nearest-even rounding of `exp x - 1`. -/
theorem expm1_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Tanh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Tanh.compiled.module ∧
      ({ name := "expm1", funcIdx := 3 } : Wasm.Export) ∈ Tanh.compiled.module.exports ∧
      Ready Tanh.compiled.module Tanh.compiled.tables
        (Verified.initialHeap Tanh.compiled.tables) Tanh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Tanh.compiled.module Tanh.compiled.tables heap store →
        Wasm.Runs false env Tanh.compiled.module 3 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Tanh.expm1 x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.exp (value x.toBits) - 1) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Tanh.compiled.module Tanh.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Tanh.compiled.bytes
  refine ⟨bytes, henc, hdec, expm1_export, ready_initial,
    fun env heap store x h => (expm1_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Tanh.expm1 x).toBits, hv, rfl, Expm1Theorem.expm1_within_one x, hrest⟩

/-- The accuracy theorem for the compiled `tanh`, as `expm1_bytes_accuracy` for function 4 and
`tanh x`, within three representable steps. -/
theorem tanh_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Tanh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Tanh.compiled.module ∧
      ({ name := "tanh", funcIdx := 4 } : Wasm.Export) ∈ Tanh.compiled.module.exports ∧
      Ready Tanh.compiled.module Tanh.compiled.tables
        (Verified.initialHeap Tanh.compiled.tables) Tanh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Tanh.compiled.module Tanh.compiled.tables heap store →
        Wasm.Runs false env Tanh.compiled.module 4 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Tanh.tanh x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 3 (Real.tanh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Tanh.compiled.module Tanh.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Tanh.compiled.bytes
  refine ⟨bytes, henc, hdec, tanh_export, ready_initial,
    fun env heap store x h => (tanh_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Tanh.tanh x).toBits, hv, rfl, TanhMain.tanh_within_three x, hrest⟩

/-- Both byte theorems of the module. -/
theorem tanh_module_accuracy :
    (∃ bytes, Wasm.Encoding.encode Tanh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Tanh.compiled.module ∧
      ({ name := "expm1", funcIdx := 3 } : Wasm.Export) ∈ Tanh.compiled.module.exports ∧
      Ready Tanh.compiled.module Tanh.compiled.tables
        (Verified.initialHeap Tanh.compiled.tables) Tanh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Tanh.compiled.module Tanh.compiled.tables heap store →
        Wasm.Runs false env Tanh.compiled.module 3 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Tanh.expm1 x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.exp (value x.toBits) - 1) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Tanh.compiled.module Tanh.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Tanh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Tanh.compiled.module ∧
      ({ name := "tanh", funcIdx := 4 } : Wasm.Export) ∈ Tanh.compiled.module.exports ∧
      Ready Tanh.compiled.module Tanh.compiled.tables
        (Verified.initialHeap Tanh.compiled.tables) Tanh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Tanh.compiled.module Tanh.compiled.tables heap store →
        Wasm.Runs false env Tanh.compiled.module 4 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Tanh.tanh x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 3 (Real.tanh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Tanh.compiled.module Tanh.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) :=
  ⟨expm1_bytes_accuracy, tanh_bytes_accuracy⟩

#print axioms ready_initial
#print axioms expm1_entry_call
#print axioms tanh_entry_call
#print axioms expm1_export
#print axioms tanh_export
#print axioms expm1_bytes_accuracy
#print axioms tanh_bytes_accuracy
#print axioms tanh_module_accuracy

end Library.Numerics.Float64.Tanh.TanhBytes
