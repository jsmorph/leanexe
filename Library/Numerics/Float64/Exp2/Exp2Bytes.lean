import Library.Numerics.Float64.Exp2.Exp10Theorem
import LeanExe.ProofKit.BorrowedKept

/-!
The byte theorems for the module of `Exp2.lean`, whose exports `exp2` (function 7) and `exp10`
(function 8) read `Exp.expTable` at address 4096.  A store is ready when the allocator invariant
holds, the table is a borrowed array at its address, and the memory cap is at most 65,535 pages.
A call of either entry from a ready store returns without a trap the bits of the Lean function
and leaves a ready store, so the theorems cover every sequence of calls to the two entries from
the initial store.  `exp2_module_accuracy` states both, for the file theorem's axiom report.
-/

namespace Library.Numerics.Float64.Exp2.Exp2Bytes
open CodeLib.IEEE64
open LeanExe.ProofKit

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entries run, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Exp.expTable ∧
    store.memoryCap Exp2.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its table. -/
theorem ready_initial :
    Ready (Verified.initialHeap Exp2.compiled.tables) Exp2.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Exp2.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `exp2` entry from a ready store. -/
theorem exp2_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Exp2.compiled.module 7 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Exp2.exp2 x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hTab, hCap⟩ := h
  have htab : ∀ t ∈ [((4096 : UInt64), Exp.expTable)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨hTab, Apart.nil⟩
  refine (Exp2.compiled.exp2.implements env store heap [.f64 x.toBits] x hAt trivial htab rfl
    Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Exp2.exp2 x).toBits] := howned
  have hvs : values = [.f64 (Exp2.exp2 x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', BorrowedKept.borrowed_kept hTab hAt' hkeep,
    memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `exp10` entry from a ready store. -/
theorem exp10_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Exp2.compiled.module 8 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Exp2.exp10 x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hTab, hCap⟩ := h
  have htab : ∀ t ∈ [((4096 : UInt64), Exp.expTable)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨hTab, Apart.nil⟩
  refine (Exp2.compiled.exp10.implements env store heap [.f64 x.toBits] x hAt trivial htab rfl
    Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Exp2.exp10 x).toBits] := howned
  have hvs : values = [.f64 (Exp2.exp10 x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', BorrowedKept.borrowed_kept hTab hAt' hkeep,
    memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

/-- Function 7 of the module is its export `exp2`. -/
theorem exp2_export :
    ({ name := "exp2", funcIdx := 7 } : Wasm.Export) ∈ Exp2.compiled.module.exports := by
  decide +kernel

/-- Function 8 of the module is its export `exp10`. -/
theorem exp10_export :
    ({ name := "exp10", funcIdx := 8 } : Wasm.Export) ∈ Exp2.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `exp2`: the bytes decode to the module, whose function
7 is exported as `exp2`, and the initial store is ready.  A call of that entry from a ready store
returns without a trap the bits of `Exp2.exp2 x` and leaves a ready store in which every region
of the heap before the call keeps its bytes.  For finite `x` the bits lie within one
representable step of the nearest-even rounding of `2 ^ x`. -/
theorem exp2_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Exp2.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Exp2.compiled.module ∧
      ({ name := "exp2", funcIdx := 7 } : Wasm.Export) ∈ Exp2.compiled.module.exports ∧
      Ready (Verified.initialHeap Exp2.compiled.tables) Exp2.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Exp2.compiled.module 7 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Exp2.exp2 x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ value x.toBits) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Exp2.compiled.bytes
  refine ⟨bytes, henc, hdec, exp2_export, ready_initial,
    fun env heap store x h => (exp2_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Exp2.exp2 x).toBits, hv, rfl, Exp2Theorem.exp2_within x, hrest⟩

/-- The accuracy theorem for the compiled `exp10`, as `exp2_bytes_accuracy` for function 8 and
`10 ^ x`. -/
theorem exp10_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Exp2.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Exp2.compiled.module ∧
      ({ name := "exp10", funcIdx := 8 } : Wasm.Export) ∈ Exp2.compiled.module.exports ∧
      Ready (Verified.initialHeap Exp2.compiled.tables) Exp2.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Exp2.compiled.module 8 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Exp2.exp10 x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 ((10 : ℝ) ^ value x.toBits) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Exp2.compiled.bytes
  refine ⟨bytes, henc, hdec, exp10_export, ready_initial,
    fun env heap store x h => (exp10_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Exp2.exp10 x).toBits, hv, rfl, Exp10Theorem.exp10_within x, hrest⟩

/-- Both byte theorems of the module. -/
theorem exp2_module_accuracy :
    (∃ bytes, Wasm.Encoding.encode Exp2.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Exp2.compiled.module ∧
      ({ name := "exp2", funcIdx := 7 } : Wasm.Export) ∈ Exp2.compiled.module.exports ∧
      Ready (Verified.initialHeap Exp2.compiled.tables) Exp2.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Exp2.compiled.module 7 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Exp2.exp2 x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ value x.toBits) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Exp2.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Exp2.compiled.module ∧
      ({ name := "exp10", funcIdx := 8 } : Wasm.Export) ∈ Exp2.compiled.module.exports ∧
      Ready (Verified.initialHeap Exp2.compiled.tables) Exp2.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Exp2.compiled.module 8 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Exp2.exp10 x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 ((10 : ℝ) ^ value x.toBits) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) :=
  ⟨exp2_bytes_accuracy, exp10_bytes_accuracy⟩

#print axioms ready_initial
#print axioms exp2_entry_call
#print axioms exp10_entry_call
#print axioms exp2_export
#print axioms exp10_export
#print axioms exp2_bytes_accuracy
#print axioms exp10_bytes_accuracy
#print axioms exp2_module_accuracy

end Library.Numerics.Float64.Exp2.Exp2Bytes
