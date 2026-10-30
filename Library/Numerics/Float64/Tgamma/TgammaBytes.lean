import Library.Numerics.Float64.Tgamma.TgammaWithin
import Verified.Call

/-!
The byte theorem for `tgamma` in the module of `Tgamma.lean`, whose export `tgamma` is function 41.
The module writes eight tables from address 4096, all of which `tgamma` reads: `Tgamma.dbTable` at
4096, `Tgamma.accurateTable` at 5472, `Tgamma.smallTable` at 11224, `Tgamma.mainTable` at 11440,
`Tgamma.logdTable` at 11880, `Tgamma.sinpidTable` at 14000, `Tgamma.expdTable` at 15112, and
`Tgamma.asymTable` at 16224.  A store is ready when the allocator invariant holds, the eight tables
are borrowed arrays at their addresses, and the memory cap is at most 65,535 pages.  A call of the
entry from a ready store returns without a trap the bits of `Tgamma.tgamma x` and leaves a ready
store, so the theorem covers every sequence of calls from the initial store.  The bound is that of
`TgammaWithin.tgamma_within`: one step of the nearest-even rounding of `Γ x` for finite `x` other
than the poles.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaBytes
open Verified (Ready)
open CodeLib.IEEE64
open LeanExe.ProofKit

/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready Tgamma.compiled.module Tgamma.compiled.tables
      (Verified.initialHeap Tgamma.compiled.tables)
      Tgamma.compiled.module.initialStore :=
  Verified.Ready.initial rfl Tgamma.compiled.initial

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- A call of the module's `tgamma` entry from a ready store. -/
theorem tgamma_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Tgamma.compiled.module Tgamma.compiled.tables heap store) :
    Runs false env Tgamma.compiled.module 41 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Tgamma.tgamma x).toBits] ∧ ∃ heap' : Heap,
        Ready Tgamma.compiled.module Tgamma.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call Tgamma.compiled.tgamma.implements Tgamma.compiled.tables
    (Verified.tables_at [0, 1, 2, 3, 4, 5, 6, 7] (by decide) rfl)
    env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

/-- Function 41 of the module is its export `tgamma`. -/
theorem tgamma_export :
    ({ name := "tgamma", funcIdx := 41 } : Wasm.Export) ∈ Tgamma.compiled.module.exports := by
  decide +kernel

/-- **The accuracy theorem for the compiled `tgamma`**: the bytes decode to the module, whose
function 41 is exported as `tgamma`, and the initial store is ready.  A call of that entry from a
ready store returns without a trap the bits of `Tgamma.tgamma x` and leaves a ready store in which
every region of the heap before the call keeps its bytes.  For finite `x` other than 0 and the
negative integers the value lies within one step of the nearest-even rounding of `Γ x`. -/
theorem tgamma_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Tgamma.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Tgamma.compiled.module ∧
      ({ name := "tgamma", funcIdx := 41 } : Wasm.Export) ∈ Tgamma.compiled.module.exports ∧
      Ready Tgamma.compiled.module Tgamma.compiled.tables
        (Verified.initialHeap Tgamma.compiled.tables) Tgamma.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Tgamma.compiled.module Tgamma.compiled.tables heap store →
        Wasm.Runs false env Tgamma.compiled.module 41 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Tgamma.tgamma x).toBits ∧
            (Finite x.toBits → (∀ n : ℤ, n ≤ 0 → value x.toBits ≠ n) →
              F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Tgamma.compiled.module Tgamma.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Tgamma.compiled.bytes
  refine ⟨bytes, henc, hdec, tgamma_export, ready_initial,
    fun env heap store x h => (tgamma_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Tgamma.tgamma x).toBits, hv, rfl, TgammaWithin.tgamma_within x, hrest⟩

#print axioms ready_initial
#print axioms tgamma_entry_call
#print axioms tgamma_export
#print axioms tgamma_bytes_accuracy

end Library.Numerics.Float64.Tgamma.TgammaBytes
