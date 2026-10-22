import Library.Numerics.Float64.Pow.PowTheorem
import LeanExe.ProofKit.BorrowedKept

/-!
The byte theorems for the module of `Pow.lean`, whose export `pow` (function 11) reads
`Pow.powLogTable` at address 4096 and `Exp.expTable` at address 8200.  A store is ready when the
allocator invariant holds, both tables are borrowed arrays at their addresses, and the memory cap
is at most 65,535 pages.  A call of the entry from a ready store returns without a trap the bits
of the Lean function and leaves a ready store, so the theorems cover every sequence of calls from
the initial store.
-/

namespace Library.Numerics.Float64.Pow.PowBytes
open CodeLib.IEEE64
open LeanExe.ProofKit

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entry runs, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Pow.powLogTable ∧
    heap.Borrowed store 8200 Exp.expTable ∧ store.memoryCap Pow.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready (Verified.initialHeap Pow.compiled.tables) Pow.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Pow.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `pow` entry from a ready store, with `y` on top of `x`. -/
theorem pow_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x y : Float)
    (h : Ready heap store) :
    Runs false env Pow.compiled.module 11 store [.f64 y.toBits, .f64 x.toBits]
      fun final values =>
        values = [.f64 (Pow.pow x y).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r := by
  obtain ⟨hAt, hLog, hExp, hCap⟩ := h
  have htab : ∀ t ∈ [((4096 : UInt64), Pow.powLogTable), ((8200 : UInt64), Exp.expTable)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨hLog, Apart.nil⟩
    · exact ⟨hExp, Apart.nil⟩
  refine (Pow.compiled.pow.implements env store heap [.f64 x.toBits, .f64 y.toBits] (x, y) hAt
    trivial htab rfl Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Pow.pow x y).toBits] := howned
  have hvs : values = [.f64 (Pow.pow x y).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', BorrowedKept.borrowed_kept hLog hAt' hkeep,
    BorrowedKept.borrowed_kept hExp hAt' hkeep, memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

/-- Function 11 of the module is its export `pow`. -/
theorem pow_export :
    ({ name := "pow", funcIdx := 11 } : Wasm.Export) ∈ Pow.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `pow`: the bytes decode to the module, whose function
11 is exported as `pow`, and the initial store is ready.  A call of that entry from a ready store
returns without a trap the bits of `Pow.pow x y` and leaves a ready store in which every region
of the heap before the call keeps its bytes.  For finite `x` and `y` with a real value of
`x ^ y`, the bits lie within one representable step of the nearest-even rounding of
`Real.rpow x y`. -/
theorem pow_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Pow.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Pow.compiled.module ∧
      ({ name := "pow", funcIdx := 11 } : Wasm.Export) ∈ Pow.compiled.module.exports ∧
      Ready (Verified.initialHeap Pow.compiled.tables) Pow.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x y : Float), Ready heap store →
        Wasm.Runs false env Pow.compiled.module 11 store [.f64 y.toBits, .f64 x.toBits]
          (fun final values =>
            ∃ w : UInt64, values = [.f64 w] ∧ w = (Pow.pow x y).toBits ∧
              (Finite x.toBits → Finite y.toBits →
                (0 < value x.toBits ∨ (value x.toBits < 0 ∧ ∃ n : Int, value y.toBits = n) ∨
                  (value x.toBits = 0 ∧ 0 ≤ value y.toBits)) →
                F64SignedRounding.WithinSteps 1 (value x.toBits ^ value y.toBits) w) ∧
              ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
                ∀ r, heap.Region r → 0 < r.2 →
                  (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                    heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Pow.compiled.bytes
  refine ⟨bytes, henc, hdec, pow_export, ready_initial,
    fun env heap store x y h => (pow_entry_call env heap store x y h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Pow.pow x y).toBits, hv, rfl,
    fun hxf hyf hr => PowTheorem.pow_within x y hxf hyf hr, hrest⟩

#print axioms ready_initial
#print axioms pow_entry_call
#print axioms pow_export
#print axioms pow_bytes_accuracy

end Library.Numerics.Float64.Pow.PowBytes
