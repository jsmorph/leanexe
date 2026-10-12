import Verified.Examples.AsinTheoremSpecial

/-!
The byte theorems for the module of `Asin.lean`, whose exports `asin` (function 3) and `acos`
(function 4) read no table.  A store is ready when the allocator invariant holds and the memory
cap is at most 65,535 pages.  A call of either entry from a ready store returns without a trap the
bits of the Lean function and leaves a ready store, so the theorems cover every sequence of calls
to the two entries from the initial store.  `asin_module_accuracy` states both, for the file
theorem's axiom report.
-/

namespace Verified.Examples.AsinBytes
open CodeLib.IEEE64
open LeanExe.ProofKit

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entries run, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ store.memoryCap Asin.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready. -/
theorem ready_initial :
    Ready (Verified.initialHeap Asin.compiled.tables) Asin.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, -⟩ := Asin.compiled.initial
  exact ⟨hAt, hCap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `asin` entry from a ready store. -/
theorem asin_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Asin.compiled.module 3 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Asin.asin x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hCap⟩ := h
  refine (Asin.compiled.asin.implements env store heap [.f64 x.toBits] x hAt trivial
    rfl Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Asin.asin x).toBits] := howned
  have hvs : values = [.f64 (Asin.asin x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `acos` entry from a ready store. -/
theorem acos_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Asin.compiled.module 4 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Asin.acos x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hCap⟩ := h
  refine (Asin.compiled.acos.implements env store heap [.f64 x.toBits] x hAt trivial
    rfl Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Asin.acos x).toBits] := howned
  have hvs : values = [.f64 (Asin.acos x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

/-- Function 3 of the module is its export `asin`. -/
theorem asin_export :
    ({ name := "asin", funcIdx := 3 } : Wasm.Export) ∈ Asin.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `asin`: the bytes decode to the module, whose function
3 is exported as `asin`, and the initial store is ready.  A call of that entry from a ready
store returns without a trap the bits of `Asin.asin x` and leaves a ready store in which every
region of the heap before the call keeps its bytes.  For finite `x` with `|x| ≤ 1` the bits lie
within one representable step of the nearest-even rounding of `arcsin x`. -/
theorem asin_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Asin.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asin.compiled.module ∧
      ({ name := "asin", funcIdx := 3 } : Wasm.Export) ∈ Asin.compiled.module.exports ∧
      Ready (Verified.initialHeap Asin.compiled.tables) Asin.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asin.compiled.module 3 store [.f64 x.toBits]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asin.asin x).toBits ∧
            (Finite x.toBits → |value x.toBits| ≤ 1 →
              F64SignedRounding.WithinSteps 1 (Real.arcsin (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Asin.compiled.bytes
  refine ⟨bytes, henc, hdec, asin_export, ready_initial,
    fun env heap store x h => (asin_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Asin.asin x).toBits, hv, rfl, AsinTheorem.asin_within_one x, hrest⟩

/-- Function 4 of the module is its export `acos`. -/
theorem acos_export :
    ({ name := "acos", funcIdx := 4 } : Wasm.Export) ∈ Asin.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `acos`: the bytes decode to the module, whose function
4 is exported as `acos`, and the initial store is ready.  A call of that entry from a ready
store returns without a trap the bits of `Asin.acos x` and leaves a ready store in which every
region of the heap before the call keeps its bytes.  For finite `x` with `|x| ≤ 1` the bits lie
within one representable step of the nearest-even rounding of `arccos x`. -/
theorem acos_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Asin.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asin.compiled.module ∧
      ({ name := "acos", funcIdx := 4 } : Wasm.Export) ∈ Asin.compiled.module.exports ∧
      Ready (Verified.initialHeap Asin.compiled.tables) Asin.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asin.compiled.module 4 store [.f64 x.toBits]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asin.acos x).toBits ∧
            (Finite x.toBits → |value x.toBits| ≤ 1 →
              F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Asin.compiled.bytes
  refine ⟨bytes, henc, hdec, acos_export, ready_initial,
    fun env heap store x h => (acos_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Asin.acos x).toBits, hv, rfl, AcosTheorem.acos_within_one x, hrest⟩

/-- Both byte theorems of the module. -/
theorem asin_module_accuracy :
    (∃ bytes, Wasm.Encoding.encode Asin.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asin.compiled.module ∧
      ({ name := "asin", funcIdx := 3 } : Wasm.Export) ∈ Asin.compiled.module.exports ∧
      Ready (Verified.initialHeap Asin.compiled.tables) Asin.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asin.compiled.module 3 store [.f64 x.toBits]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asin.asin x).toBits ∧
            (Finite x.toBits → |value x.toBits| ≤ 1 →
              F64SignedRounding.WithinSteps 1 (Real.arcsin (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Asin.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asin.compiled.module ∧
      ({ name := "acos", funcIdx := 4 } : Wasm.Export) ∈ Asin.compiled.module.exports ∧
      Ready (Verified.initialHeap Asin.compiled.tables) Asin.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asin.compiled.module 4 store [.f64 x.toBits]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asin.acos x).toBits ∧
            (Finite x.toBits → |value x.toBits| ≤ 1 →
              F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) :=
  ⟨asin_bytes_accuracy, acos_bytes_accuracy⟩

#print axioms asin_bytes_accuracy
#print axioms acos_bytes_accuracy
#print axioms asin_module_accuracy

end Verified.Examples.AsinBytes
