import Verified.Examples.AsinhTheorem
import Verified.Examples.AcoshTheorem
import Verified.Examples.AtanhTheorem
import LeanExe.ProofKit.BorrowedKept

/-!
The byte theorems for the module of `Asinh.lean`, whose exports `atanh` (function 9), `asinh`
(function 10), and `acosh` (function 11) run in one store.  `asinh` and `acosh` read
`Log.logTable` at address 4096 and `Log.logTable2` at address 6152, and `atanh` reads no table.  A
store is ready when the allocator invariant holds, the two tables are borrowed arrays at their
addresses, and the memory cap is at most 65,535 pages.  A call of any of the three entries from a
ready store returns without a trap the bits of the Lean function and leaves a ready store, so the
theorems cover every sequence of calls to the three entries from the initial store.
`asinh_module_accuracy` states all three, for the file theorem's axiom report.
-/

namespace Verified.Examples.AsinhBytes
open CodeLib.IEEE64
open LeanExe.ProofKit

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entries run, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Log.logTable ∧
    heap.Borrowed store 6152 Log.logTable2 ∧ store.memoryCap Asinh.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready (Verified.initialHeap Asinh.compiled.tables) Asinh.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Asinh.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
/-- The tables of a ready store, as the entries that read them take them. -/
theorem ready_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Log.logTable), ((6152 : UInt64), Log.logTable2)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩

open Wasm LeanExe.Pipeline in
/-- After a call that keeps every region of the heap, a ready store stays ready. -/
theorem ready_kept (heap heap' : Heap) (store final : Store Unit) (h : Ready heap store)
    (hAt' : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r)
    (hcap : final.memoryCap Asinh.compiled.module 0 ≤ 65535) : Ready heap' final :=
  ⟨hAt', BorrowedKept.borrowed_kept h.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.1 hAt' hkeep, hcap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `atanh` entry from a ready store. -/
theorem atanh_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Asinh.compiled.module 9 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Asinh.atanh x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Asinh.compiled.atanh.implements env store heap [.f64 x.toBits] x h.1 trivial rfl
    Separate.nil h.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Asinh.atanh x).toBits] := howned
  have hvs : values = [.f64 (Asinh.atanh x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2), hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `asinh` entry from a ready store. -/
theorem asinh_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Asinh.compiled.module 10 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Asinh.asinh x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Asinh.compiled.asinh.implements env store heap [.f64 x.toBits] x h.1 trivial
    (ready_tables heap store h) rfl Separate.nil h.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Asinh.asinh x).toBits] := howned
  have hvs : values = [.f64 (Asinh.asinh x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2), hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `acosh` entry from a ready store. -/
theorem acosh_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Asinh.compiled.module 11 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Asinh.acosh x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Asinh.compiled.acosh.implements env store heap [.f64 x.toBits] x h.1 trivial
    (ready_tables heap store h) rfl Separate.nil h.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Asinh.acosh x).toBits] := howned
  have hvs : values = [.f64 (Asinh.acosh x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2), hkeep⟩

/-- Function 9 of the module is its export `atanh`. -/
theorem atanh_export :
    ({ name := "atanh", funcIdx := 9 } : Wasm.Export) ∈ Asinh.compiled.module.exports := by
  decide +kernel

/-- Function 10 of the module is its export `asinh`. -/
theorem asinh_export :
    ({ name := "asinh", funcIdx := 10 } : Wasm.Export) ∈ Asinh.compiled.module.exports := by
  decide +kernel

/-- Function 11 of the module is its export `acosh`. -/
theorem acosh_export :
    ({ name := "acosh", funcIdx := 11 } : Wasm.Export) ∈ Asinh.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `atanh`: the bytes decode to the module, whose function
9 is exported as `atanh`, and the initial store is ready.  A call of that entry from a ready store
returns without a trap the bits of `Asinh.atanh x` and leaves a ready store in which every region
of the heap before the call keeps its bytes.  For finite `x` with `|x| < 1` the bits lie within
two representable steps of the nearest-even rounding of `artanh x`. -/
theorem atanh_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Asinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asinh.compiled.module ∧
      ({ name := "atanh", funcIdx := 9 } : Wasm.Export) ∈ Asinh.compiled.module.exports ∧
      Ready (Verified.initialHeap Asinh.compiled.tables) Asinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asinh.compiled.module 9 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asinh.atanh x).toBits ∧
            (Finite x.toBits → |value x.toBits| < 1 →
              F64SignedRounding.WithinSteps 2 (Real.artanh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Asinh.compiled.bytes
  refine ⟨bytes, henc, hdec, atanh_export, ready_initial,
    fun env heap store x h => (atanh_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Asinh.atanh x).toBits, hv, rfl, AtanhTheorem.atanh_within_two x, hrest⟩

/-- The accuracy theorem for the compiled `asinh`, as `atanh_bytes_accuracy` for function 10 and
`asinh x`: for finite `x` the bits lie within two representable steps of the nearest-even
rounding of `arsinh x`. -/
theorem asinh_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Asinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asinh.compiled.module ∧
      ({ name := "asinh", funcIdx := 10 } : Wasm.Export) ∈ Asinh.compiled.module.exports ∧
      Ready (Verified.initialHeap Asinh.compiled.tables) Asinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asinh.compiled.module 10 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asinh.asinh x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 2 (Real.arsinh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Asinh.compiled.bytes
  refine ⟨bytes, henc, hdec, asinh_export, ready_initial,
    fun env heap store x h => (asinh_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Asinh.asinh x).toBits, hv, rfl, AsinhTheorem.asinh_within_two x, hrest⟩

/-- The accuracy theorem for the compiled `acosh`, as `atanh_bytes_accuracy` for function 11 and
`acosh x`: for finite `x ≥ 1` the bits lie within two representable steps of the nearest-even
rounding of `arcosh x`. -/
theorem acosh_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Asinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asinh.compiled.module ∧
      ({ name := "acosh", funcIdx := 11 } : Wasm.Export) ∈ Asinh.compiled.module.exports ∧
      Ready (Verified.initialHeap Asinh.compiled.tables) Asinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asinh.compiled.module 11 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asinh.acosh x).toBits ∧
            (Finite x.toBits → 1 ≤ value x.toBits →
              F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Asinh.compiled.bytes
  refine ⟨bytes, henc, hdec, acosh_export, ready_initial,
    fun env heap store x h => (acosh_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Asinh.acosh x).toBits, hv, rfl, AcoshTheorem.acosh_within_two x, hrest⟩

/-- The three byte theorems of the module. -/
theorem asinh_module_accuracy :
    (∃ bytes, Wasm.Encoding.encode Asinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asinh.compiled.module ∧
      ({ name := "atanh", funcIdx := 9 } : Wasm.Export) ∈ Asinh.compiled.module.exports ∧
      Ready (Verified.initialHeap Asinh.compiled.tables) Asinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asinh.compiled.module 9 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asinh.atanh x).toBits ∧
            (Finite x.toBits → |value x.toBits| < 1 →
              F64SignedRounding.WithinSteps 2 (Real.artanh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Asinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asinh.compiled.module ∧
      ({ name := "asinh", funcIdx := 10 } : Wasm.Export) ∈ Asinh.compiled.module.exports ∧
      Ready (Verified.initialHeap Asinh.compiled.tables) Asinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asinh.compiled.module 10 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asinh.asinh x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 2 (Real.arsinh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Asinh.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Asinh.compiled.module ∧
      ({ name := "acosh", funcIdx := 11 } : Wasm.Export) ∈ Asinh.compiled.module.exports ∧
      Ready (Verified.initialHeap Asinh.compiled.tables) Asinh.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Asinh.compiled.module 11 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Asinh.acosh x).toBits ∧
            (Finite x.toBits → 1 ≤ value x.toBits →
              F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) :=
  ⟨atanh_bytes_accuracy, asinh_bytes_accuracy, acosh_bytes_accuracy⟩

#print axioms ready_initial
#print axioms atanh_entry_call
#print axioms asinh_entry_call
#print axioms acosh_entry_call
#print axioms atanh_export
#print axioms asinh_export
#print axioms acosh_export
#print axioms atanh_bytes_accuracy
#print axioms asinh_bytes_accuracy
#print axioms acosh_bytes_accuracy
#print axioms asinh_module_accuracy

end Verified.Examples.AsinhBytes
