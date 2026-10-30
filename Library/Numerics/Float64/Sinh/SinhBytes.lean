import Library.Numerics.Float64.Sinh.SinhTheorem
import Library.Numerics.Float64.Sinh.CoshTheorem
import Verified.Call

/-!
The byte theorems for the module of `Sinh.lean`, whose exports `sinh` (function 11) and `cosh`
(function 12) read `Exp.expTable` at address 4096.  A store is ready when the allocator invariant
holds, the table is a borrowed array at its address, and the memory cap is at most 65,535 pages.
A call of either entry from a ready store returns without a trap the bits of the Lean function
and leaves a ready store, so the theorems cover every sequence of calls to the two entries from
the initial store.  `sinh_module_accuracy` states both, for the file theorem's axiom report.
-/

namespace Library.Numerics.Float64.Sinh.SinhBytes
open Verified (Ready)
open CodeLib.IEEE64
open LeanExe.ProofKit

/-- The store in which the module starts is ready, with the heap that holds its table. -/
theorem ready_initial :
    Ready Sinh.compiled.module Sinh.compiled.tables (Verified.initialHeap Sinh.compiled.tables)
      Sinh.compiled.module.initialStore :=
  Verified.Ready.initial rfl Sinh.compiled.initial

open Wasm LeanExe.Pipeline in
/-- A call of the module's `sinh` entry from a ready store. -/
theorem sinh_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Sinh.compiled.module Sinh.compiled.tables heap store) :
    Runs false env Sinh.compiled.module 11 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Sinh.sinh x).toBits] ∧ ∃ heap' : Heap,
        Ready Sinh.compiled.module Sinh.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call Sinh.compiled.sinh.implements Sinh.compiled.tables
    (Verified.tables_at [0] (by decide) rfl)
    env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `cosh` entry from a ready store. -/
theorem cosh_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Sinh.compiled.module Sinh.compiled.tables heap store) :
    Runs false env Sinh.compiled.module 12 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Sinh.cosh x).toBits] ∧ ∃ heap' : Heap,
        Ready Sinh.compiled.module Sinh.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call Sinh.compiled.cosh.implements Sinh.compiled.tables
    (Verified.tables_at [0] (by decide) rfl)
    env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

/-- Function 11 of the module is its export `sinh`. -/
theorem sinh_export :
    ({ name := "sinh", funcIdx := 11 } : Wasm.Export) ∈ Sinh.compiled.module.exports := by
  decide +kernel

/-- Function 12 of the module is its export `cosh`. -/
theorem cosh_export :
    ({ name := "cosh", funcIdx := 12 } : Wasm.Export) ∈ Sinh.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `sinh`: the bytes decode to the module, whose function
11 is exported as `sinh`, and the initial store is ready.  A call of that entry from a ready store
returns without a trap the bits of `Sinh.sinh x` and leaves a ready store in which every region
of the heap before the call keeps its bytes.  For finite `x` the bits lie within three
representable steps of the nearest-even rounding of `sinh x`. -/
theorem sinh_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Sinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Sinh.compiled.module ∧
      ({ name := "sinh", funcIdx := 11 } : Wasm.Export) ∈ Sinh.compiled.module.exports ∧
      Ready Sinh.compiled.module Sinh.compiled.tables
        (Verified.initialHeap Sinh.compiled.tables) Sinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Sinh.compiled.module Sinh.compiled.tables heap store →
        Wasm.Runs false env Sinh.compiled.module 11 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Sinh.sinh x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 3 (Real.sinh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Sinh.compiled.module Sinh.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Sinh.compiled.bytes
  refine ⟨bytes, henc, hdec, sinh_export, ready_initial,
    fun env heap store x h => (sinh_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Sinh.sinh x).toBits, hv, rfl, SinhTheorem.sinh_within_three x, hrest⟩

/-- The accuracy theorem for the compiled `cosh`, as `sinh_bytes_accuracy` for function 12 and
`cosh x`, within one representable step. -/
theorem cosh_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Sinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Sinh.compiled.module ∧
      ({ name := "cosh", funcIdx := 12 } : Wasm.Export) ∈ Sinh.compiled.module.exports ∧
      Ready Sinh.compiled.module Sinh.compiled.tables
        (Verified.initialHeap Sinh.compiled.tables) Sinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Sinh.compiled.module Sinh.compiled.tables heap store →
        Wasm.Runs false env Sinh.compiled.module 12 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Sinh.cosh x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.cosh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Sinh.compiled.module Sinh.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Sinh.compiled.bytes
  refine ⟨bytes, henc, hdec, cosh_export, ready_initial,
    fun env heap store x h => (cosh_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Sinh.cosh x).toBits, hv, rfl, CoshTheorem.cosh_within_one x, hrest⟩

/-- Both byte theorems of the module. -/
theorem sinh_module_accuracy :
    (∃ bytes, Wasm.Encoding.encode Sinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Sinh.compiled.module ∧
      ({ name := "sinh", funcIdx := 11 } : Wasm.Export) ∈ Sinh.compiled.module.exports ∧
      Ready Sinh.compiled.module Sinh.compiled.tables
        (Verified.initialHeap Sinh.compiled.tables) Sinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Sinh.compiled.module Sinh.compiled.tables heap store →
        Wasm.Runs false env Sinh.compiled.module 11 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Sinh.sinh x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 3 (Real.sinh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Sinh.compiled.module Sinh.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Sinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Sinh.compiled.module ∧
      ({ name := "cosh", funcIdx := 12 } : Wasm.Export) ∈ Sinh.compiled.module.exports ∧
      Ready Sinh.compiled.module Sinh.compiled.tables
        (Verified.initialHeap Sinh.compiled.tables) Sinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Sinh.compiled.module Sinh.compiled.tables heap store →
        Wasm.Runs false env Sinh.compiled.module 12 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Sinh.cosh x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.cosh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Sinh.compiled.module Sinh.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) :=
  ⟨sinh_bytes_accuracy, cosh_bytes_accuracy⟩

#print axioms ready_initial
#print axioms sinh_entry_call
#print axioms cosh_entry_call
#print axioms sinh_export
#print axioms cosh_export
#print axioms sinh_bytes_accuracy
#print axioms cosh_bytes_accuracy
#print axioms sinh_module_accuracy

end Library.Numerics.Float64.Sinh.SinhBytes
