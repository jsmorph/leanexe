import Library.Numerics.Float64.Atan.AtanTheoremSpecial
import Library.Numerics.Float64.Atan.AtanTwoTheorem

/-!
The byte theorems for the module of `Atan.lean`, whose exports `atan` (function 2) and `atan2`
(function 3) read no table.  A store is ready when the allocator invariant holds and the memory
cap is at most 65,535 pages.  A call of either entry from a ready store returns without a trap the
bits of the Lean function and leaves a ready store, so the theorems cover every sequence of calls
to the two entries from the initial store.  `atan_module_accuracy` states both, for the file
theorem's axiom report.
-/

namespace Library.Numerics.Float64.Atan.AtanBytes
open CodeLib.IEEE64
open LeanExe.ProofKit

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entry runs, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ store.memoryCap Atan.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready. -/
theorem ready_initial :
    Ready (Verified.initialHeap Atan.compiled.tables) Atan.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, -⟩ := Atan.compiled.initial
  exact ⟨hAt, hCap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `atan` entry from a ready store. -/
theorem atan_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Atan.compiled.module 2 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Atan.atan x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hCap⟩ := h
  refine (Atan.compiled.atan.implements env store heap [.f64 x.toBits] x hAt trivial
    rfl Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Atan.atan x).toBits] := howned
  have hvs : values = [.f64 (Atan.atan x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `atan2` entry from a ready store.  The entry takes `y` and then `x`;
the list of arguments is in reverse order. -/
theorem atan2_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (y x : Float)
    (h : Ready heap store) :
    Runs false env Atan.compiled.module 3 store [.f64 x.toBits, .f64 y.toBits] fun final values =>
      values = [.f64 (Atan.atan2 y x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hCap⟩ := h
  refine (Atan.compiled.atan2.implements env store heap [.f64 y.toBits, .f64 x.toBits] (y, x) hAt
    trivial rfl Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Atan.atan2 y x).toBits] := howned
  have hvs : values = [.f64 (Atan.atan2 y x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

/-- Function 2 of the module is its export `atan`. -/
theorem atan_export :
    ({ name := "atan", funcIdx := 2 } : Wasm.Export) ∈ Atan.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `atan`: the bytes decode to the module, whose function
2 is exported as `atan`, and the initial store is ready.  A call of that entry from a
ready store returns without a trap the bits of `Atan.atan x` and leaves a ready store in which
every region of the heap before the call keeps its bytes.  For finite `x` the bits lie within one
representable step of the nearest-even rounding of `arctan x`. -/
theorem atan_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Atan.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Atan.compiled.module ∧
      ({ name := "atan", funcIdx := 2 } : Wasm.Export) ∈ Atan.compiled.module.exports ∧
      Ready (Verified.initialHeap Atan.compiled.tables) Atan.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Atan.compiled.module 2 store [.f64 x.toBits]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Atan.atan x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Atan.compiled.bytes
  refine ⟨bytes, henc, hdec, atan_export, ready_initial,
    fun env heap store x h => (atan_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Atan.atan x).toBits, hv, rfl, AtanTheorem.atan_within_one x, hrest⟩

/-- Function 3 of the module is its export `atan2`. -/
theorem atan2_export :
    ({ name := "atan2", funcIdx := 3 } : Wasm.Export) ∈ Atan.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `atan2`, as `atan_bytes_accuracy` for function 3 with
the arguments `x` and `y`.  For finite `x` and finite nonzero `y` the bits lie within two
representable steps of the nearest-even rounding of `arg (x + y i)`. -/
theorem atan2_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Atan.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Atan.compiled.module ∧
      ({ name := "atan2", funcIdx := 3 } : Wasm.Export) ∈ Atan.compiled.module.exports ∧
      Ready (Verified.initialHeap Atan.compiled.tables) Atan.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (y x : Float), Ready heap store →
        Wasm.Runs false env Atan.compiled.module 3 store [.f64 x.toBits, .f64 y.toBits]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Atan.atan2 y x).toBits ∧
            (Finite y.toBits → Finite x.toBits → value y.toBits ≠ 0 →
              F64SignedRounding.WithinSteps 2
                (Complex.arg ((value x.toBits : ℂ) + (value y.toBits : ℂ) * Complex.I)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Atan.compiled.bytes
  refine ⟨bytes, henc, hdec, atan2_export, ready_initial,
    fun env heap store y x h => (atan2_entry_call env heap store y x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Atan.atan2 y x).toBits, hv, rfl, AtanTwoTheorem.atan2_within_two y x, hrest⟩

/-- Both byte theorems of the module. -/
theorem atan_module_accuracy :
    (∃ bytes, Wasm.Encoding.encode Atan.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Atan.compiled.module ∧
      ({ name := "atan", funcIdx := 2 } : Wasm.Export) ∈ Atan.compiled.module.exports ∧
      Ready (Verified.initialHeap Atan.compiled.tables) Atan.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Atan.compiled.module 2 store [.f64 x.toBits]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Atan.atan x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Atan.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Atan.compiled.module ∧
      ({ name := "atan2", funcIdx := 3 } : Wasm.Export) ∈ Atan.compiled.module.exports ∧
      Ready (Verified.initialHeap Atan.compiled.tables) Atan.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (y x : Float), Ready heap store →
        Wasm.Runs false env Atan.compiled.module 3 store [.f64 x.toBits, .f64 y.toBits]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Atan.atan2 y x).toBits ∧
            (Finite y.toBits → Finite x.toBits → value y.toBits ≠ 0 →
              F64SignedRounding.WithinSteps 2
                (Complex.arg ((value x.toBits : ℂ) + (value y.toBits : ℂ) * Complex.I)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) :=
  ⟨atan_bytes_accuracy, atan2_bytes_accuracy⟩

#print axioms ready_initial
#print axioms atan_entry_call
#print axioms atan2_entry_call
#print axioms atan_export
#print axioms atan2_export
#print axioms atan_bytes_accuracy
#print axioms atan2_bytes_accuracy
#print axioms atan_module_accuracy

end Library.Numerics.Float64.Atan.AtanBytes
