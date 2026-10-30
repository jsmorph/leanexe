import Library.Numerics.Float64.Sinpi.SinpiExactTan
import Verified.Call

/-!
The accuracy theorems for `Sinpi.sinpi`, `Sinpi.cospi`, and `Sinpi.tanpi`.  For every finite
binary64 input, the result lies within one representable step of the nearest-even rounding of
the real `sin (π x)` and `cos (π x)`, and, away from an integer plus `1/2`, of `tan (π x)`.  The
exceptional inputs give the results of `s_sinpi.c`, `s_cospi.c`, and `s_tanpi.c` as bit
equalities, proved in `SinpiExact` and `SinpiExactTan`: `sinpi` of an integer is `±0` with the
sign of `x`, `cospi` of an integer plus `1/2` is `+0`, `tanpi` of an integer `n` is `±0` with the
sign of `x` for even `n` and the other sign for odd `n`, `tanpi` of `n + 1/2` is `+∞` for even
`n` and `-∞` for odd `n`, and an infinity or a NaN gives the canonical NaN.
`sinpi_bytes_accuracy`, `cospi_bytes_accuracy`, and `tanpi_bytes_accuracy` carry the bounds to
the decoded bytes of the compiled module and to every call in a sequence of calls to its exports
`sinpi`, `cospi`, and `tanpi`, functions 13, 14, and 15.  The module has no tables.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiTheorem
open Verified (Ready)
open CodeLib.IEEE64 LeanExe.ProofKit

/-- The store in which the module starts is ready. -/
theorem ready_initial :
    Ready Sinpi.compiled.module Sinpi.compiled.tables (Verified.initialHeap Sinpi.compiled.tables)
      Sinpi.compiled.module.initialStore :=
  Verified.Ready.initial rfl Sinpi.compiled.initial

open Wasm LeanExe.Pipeline in
/-- A call of the module's `sinpi` entry from a ready store returns the bits of
`Sinpi.sinpi x` and leaves a ready store, and every region of the heap keeps its bytes. -/
theorem sinpi_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Sinpi.compiled.module Sinpi.compiled.tables heap store) :
    Runs false env Sinpi.compiled.module 13 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Sinpi.sinpi x).toBits] ∧ ∃ heap' : Heap,
        Ready Sinpi.compiled.module Sinpi.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA Sinpi.compiled.sinpi.implements) Sinpi.compiled.tables
    nofun env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `cospi` entry, as `sinpi_entry_call`. -/
theorem cospi_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Sinpi.compiled.module Sinpi.compiled.tables heap store) :
    Runs false env Sinpi.compiled.module 14 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Sinpi.cospi x).toBits] ∧ ∃ heap' : Heap,
        Ready Sinpi.compiled.module Sinpi.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA Sinpi.compiled.cospi.implements) Sinpi.compiled.tables
    nofun env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `tanpi` entry, as `sinpi_entry_call`. -/
theorem tanpi_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Sinpi.compiled.module Sinpi.compiled.tables heap store) :
    Runs false env Sinpi.compiled.module 15 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Sinpi.tanpi x).toBits] ∧ ∃ heap' : Heap,
        Ready Sinpi.compiled.module Sinpi.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA Sinpi.compiled.tanpi.implements) Sinpi.compiled.tables
    nofun env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

/-- Functions 13, 14, and 15 of the module are its exports `sinpi`, `cospi`, and `tanpi`. -/
theorem exports :
    ({ name := "sinpi", funcIdx := 13 } : Wasm.Export) ∈ Sinpi.compiled.module.exports ∧
      ({ name := "cospi", funcIdx := 14 } : Wasm.Export) ∈ Sinpi.compiled.module.exports ∧
      ({ name := "tanpi", funcIdx := 15 } : Wasm.Export) ∈ Sinpi.compiled.module.exports := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The accuracy theorem for the compiled module's `sinpi`: its bytes decode to the module,
whose function 13 is exported as `sinpi`, and the store in which the module starts is ready.  A
call of that entry from a ready store returns without a trap a single `f64` whose bits are those
of `Sinpi.sinpi x`, and it leaves a ready store in which every region of the heap before the call
keeps its bytes.  The theorem therefore covers every call in a sequence of calls from the initial
store.  For finite `x` the bits lie within one representable step of the nearest-even rounding
of `sin (π x)`. -/
theorem sinpi_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Sinpi.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Sinpi.compiled.module ∧
      ({ name := "sinpi", funcIdx := 13 } : Wasm.Export) ∈ Sinpi.compiled.module.exports ∧
      Ready Sinpi.compiled.module Sinpi.compiled.tables
        (Verified.initialHeap Sinpi.compiled.tables) Sinpi.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Sinpi.compiled.module Sinpi.compiled.tables heap store →
        Wasm.Runs false env Sinpi.compiled.module 13 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Sinpi.sinpi x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Sinpi.compiled.module Sinpi.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Sinpi.compiled.bytes
  refine ⟨bytes, henc, hdec, exports.1, ready_initial,
    fun env heap store x h => (sinpi_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Sinpi.sinpi x).toBits, hv, rfl, SinpiWithin.sinpi_within x, hrest⟩

/-- The accuracy theorem for the compiled module's `cospi`, as `sinpi_bytes_accuracy`, with
function 14 and `cos (π x)`. -/
theorem cospi_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Sinpi.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Sinpi.compiled.module ∧
      ({ name := "cospi", funcIdx := 14 } : Wasm.Export) ∈ Sinpi.compiled.module.exports ∧
      Ready Sinpi.compiled.module Sinpi.compiled.tables
        (Verified.initialHeap Sinpi.compiled.tables) Sinpi.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Sinpi.compiled.module Sinpi.compiled.tables heap store →
        Wasm.Runs false env Sinpi.compiled.module 14 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Sinpi.cospi x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Sinpi.compiled.module Sinpi.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Sinpi.compiled.bytes
  refine ⟨bytes, henc, hdec, exports.2.1, ready_initial,
    fun env heap store x h => (cospi_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Sinpi.cospi x).toBits, hv, rfl, SinpiWithin.cospi_within x, hrest⟩

/-- The accuracy theorem for the compiled module's `tanpi`, as `sinpi_bytes_accuracy`, with
function 15 and `tan (π x)` for `x` away from an integer plus `1/2`. -/
theorem tanpi_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Sinpi.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Sinpi.compiled.module ∧
      ({ name := "tanpi", funcIdx := 15 } : Wasm.Export) ∈ Sinpi.compiled.module.exports ∧
      Ready Sinpi.compiled.module Sinpi.compiled.tables
        (Verified.initialHeap Sinpi.compiled.tables) Sinpi.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Sinpi.compiled.module Sinpi.compiled.tables heap store →
        Wasm.Runs false env Sinpi.compiled.module 15 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Sinpi.tanpi x).toBits ∧
            (Finite x.toBits → (∀ n : Int, value x.toBits ≠ n + 1 / 2) →
              F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Sinpi.compiled.module Sinpi.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Sinpi.compiled.bytes
  refine ⟨bytes, henc, hdec, exports.2.2, ready_initial,
    fun env heap store x h => (tanpi_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Sinpi.tanpi x).toBits, hv, rfl, SinpiWithin.tanpi_within x, hrest⟩

#print axioms ready_initial
#print axioms sinpi_entry_call
#print axioms cospi_entry_call
#print axioms tanpi_entry_call
#print axioms exports
#print axioms sinpi_bytes_accuracy
#print axioms cospi_bytes_accuracy
#print axioms tanpi_bytes_accuracy
#print axioms SinpiExact.sinpi_int
#print axioms SinpiExact.cospi_half
#print axioms SinpiExact.nonfinite
#print axioms SinpiExactTan.tanpi_int
#print axioms SinpiExactTan.tanpi_half

end Library.Numerics.Float64.Sinpi.SinpiTheorem
