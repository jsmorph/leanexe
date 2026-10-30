import Library.Numerics.Float64.Pow.PowTheorem
import Verified.Call

/-!
The byte theorems for the module of `Pow.lean`, whose export `pow` (function 11) reads
`Pow.powLogTable` at address 4096 and `Exp.expTable` at address 8200.  A store is ready when the
allocator invariant holds, both tables are borrowed arrays at their addresses, and the memory cap
is at most 65,535 pages.  A call of the entry from a ready store returns without a trap the bits
of the Lean function and leaves a ready store, so the theorems cover every sequence of calls from
the initial store.
-/

namespace Library.Numerics.Float64.Pow.PowBytes
open Verified (Ready)
open CodeLib.IEEE64
open LeanExe.ProofKit

/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready Pow.compiled.module Pow.compiled.tables (Verified.initialHeap Pow.compiled.tables)
      Pow.compiled.module.initialStore :=
  Verified.Ready.initial rfl Pow.compiled.initial

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- A call of the module's `pow` entry from a ready store, with `y` on top of `x`. -/
theorem pow_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x y : Float)
    (h : Ready Pow.compiled.module Pow.compiled.tables heap store) :
    Runs false env Pow.compiled.module 11 store [.f64 y.toBits, .f64 x.toBits]
      fun final values =>
        values = [.f64 (Pow.pow x y).toBits] ∧ ∃ heap' : Heap,
          Ready Pow.compiled.module Pow.compiled.tables heap' final ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call Pow.compiled.pow.implements Pow.compiled.tables
    (Verified.tables_at [0, 1] (by decide) rfl)
    env heap store [.f64 x.toBits, .f64 y.toBits] (x, y) h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

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
      Ready Pow.compiled.module Pow.compiled.tables
        (Verified.initialHeap Pow.compiled.tables) Pow.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x y : Float), Ready Pow.compiled.module Pow.compiled.tables heap store →
        Wasm.Runs false env Pow.compiled.module 11 store [.f64 y.toBits, .f64 x.toBits]
          (fun final values =>
            ∃ w : UInt64, values = [.f64 w] ∧ w = (Pow.pow x y).toBits ∧
              (Finite x.toBits → Finite y.toBits →
                (0 < value x.toBits ∨ (value x.toBits < 0 ∧ ∃ n : Int, value y.toBits = n) ∨
                  (value x.toBits = 0 ∧ 0 ≤ value y.toBits)) →
                F64SignedRounding.WithinSteps 1 (value x.toBits ^ value y.toBits) w) ∧
              ∃ heap' : LeanExe.Pipeline.Heap,
                Ready Pow.compiled.module Pow.compiled.tables heap' final ∧
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
