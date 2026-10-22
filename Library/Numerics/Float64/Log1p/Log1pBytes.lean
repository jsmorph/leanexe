import Library.Numerics.Float64.Log1p.Log1pTheoremSpecial

/-!
The byte theorem for the module of `Log1p.lean`, whose export `log1p` reads no table.  A store is
ready when the allocator invariant holds and the memory cap is at most 65,535 pages.  A call of
the entry from a ready store returns without a trap the bits of `Log1p.log1p x` and leaves a ready
store, so the theorem covers every sequence of calls from the initial store.
-/

namespace Library.Numerics.Float64.Log1p.Log1pBytes
open CodeLib.IEEE64
open LeanExe.ProofKit

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entry runs, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ store.memoryCap Log1p.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready. -/
theorem ready_initial :
    Ready (Verified.initialHeap Log1p.compiled.tables) Log1p.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, -⟩ := Log1p.compiled.initial
  exact ⟨hAt, hCap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `log1p` entry from a ready store. -/
theorem log1p_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Log1p.compiled.module 3 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Log1p.log1p x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hCap⟩ := h
  refine (Log1p.compiled.log1p.implements env store heap [.f64 x.toBits] x hAt trivial
    rfl Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Log1p.log1p x).toBits] := howned
  have hvs : values = [.f64 (Log1p.log1p x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

/-- Function 3 of the module is its export `log1p`. -/
theorem log1p_export :
    ({ name := "log1p", funcIdx := 3 } : Wasm.Export) ∈ Log1p.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `log1p`: the bytes decode to the module, whose function
3 is exported as `log1p`, and the initial store is ready.  A call of that entry from a
ready store returns without a trap the bits of `Log1p.log1p x` and leaves a ready store in which
every region of the heap before the call keeps its bytes.  For finite `x` above `-1` the bits lie
within one representable step of the nearest-even rounding of `log (1 + x)`. -/
theorem log1p_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Log1p.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Log1p.compiled.module ∧
      ({ name := "log1p", funcIdx := 3 } : Wasm.Export) ∈ Log1p.compiled.module.exports ∧
      Ready (Verified.initialHeap Log1p.compiled.tables) Log1p.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Log1p.compiled.module 3 store [.f64 x.toBits]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Log1p.log1p x).toBits ∧
            (Finite x.toBits → -1 < value x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.log (1 + value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Log1p.compiled.bytes
  refine ⟨bytes, henc, hdec, log1p_export, ready_initial,
    fun env heap store x h => (log1p_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Log1p.log1p x).toBits, hv, rfl, Log1pTheorem.log1p_within_one x, hrest⟩

#print axioms log1p_bytes_accuracy

end Library.Numerics.Float64.Log1p.Log1pBytes
