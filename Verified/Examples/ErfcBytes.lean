import Verified.Examples.ErfcTheorem
import LeanExe.ProofKit.BorrowedKept

/-!
The byte theorem for `erfc` in the module of `Erfc.lean`, whose export `erfc` is function 49.
The module writes seven tables from address 4096, all of which `erfc` reads: `Erfc.fastTable` at
4096, `Erfc.accTable` at 13880, `Erfc.expTable` at 24040, `Erfc.asymTable` at 26096,
`Erfc.asymAccTable` at 26728, `Erfc.expAccTable` at 29136, and `Erfc.excTable` at 29368.  A store
is ready when the allocator invariant holds, the seven tables are borrowed arrays at their
addresses, and the memory cap is at most 65,535 pages.  A call of the entry from a ready store
returns without a trap the bits of `Erfc.erfc x` and leaves a ready store, so the theorem covers
every sequence of calls from the initial store.  The bound is that of
`ErfcTheorem.erfc_within_one`: one step of the nearest-even rounding of `erfc x` for finite `x`.
-/

namespace Verified.Examples.ErfcBytes
open CodeLib.IEEE64
open LeanExe.ProofKit

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entry runs, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Erfc.fastTable ∧
    heap.Borrowed store 13880 Erfc.accTable ∧ heap.Borrowed store 24040 Erfc.expTable ∧
    heap.Borrowed store 26096 Erfc.asymTable ∧ heap.Borrowed store 26728 Erfc.asymAccTable ∧
    heap.Borrowed store 29136 Erfc.expAccTable ∧ heap.Borrowed store 29368 Erfc.excTable ∧
    store.memoryCap Erfc.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready (Verified.initialHeap Erfc.compiled.tables) Erfc.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Erfc.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hBor 2 (by decide), hBor 3 (by decide),
    hBor 4 (by decide), hBor 5 (by decide), hBor 6 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
/-- After a call that keeps every region of the heap, a ready store stays ready. -/
theorem ready_kept (heap heap' : Heap) (store final : Store Unit) (h : Ready heap store)
    (hAt' : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r)
    (hcap : final.memoryCap Erfc.compiled.module 0 ≤ 65535) : Ready heap' final :=
  ⟨hAt', BorrowedKept.borrowed_kept h.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.1 hAt' hkeep, BorrowedKept.borrowed_kept h.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.2.2.1 hAt' hkeep, hcap⟩

open Wasm LeanExe.Pipeline in
/-- The tables of a ready store, as the entry takes them. -/
theorem erfc_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Erfc.fastTable), ((13880 : UInt64), Erfc.accTable),
        ((24040 : UInt64), Erfc.expTable), ((26096 : UInt64), Erfc.asymTable),
        ((26728 : UInt64), Erfc.asymAccTable), ((29136 : UInt64), Erfc.expAccTable),
        ((29368 : UInt64), Erfc.excTable)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht | ht | ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.2.2.1, Apart.nil⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `erfc` entry from a ready store. -/
theorem erfc_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Erfc.compiled.module 49 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Erfc.erfc x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Erfc.compiled.erfc.implements env store heap [.f64 x.toBits] x h.1 trivial
    (erfc_tables heap store h) rfl Separate.nil h.2.2.2.2.2.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Erfc.erfc x).toBits] := howned
  have hvs : values = [.f64 (Erfc.erfc x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2.2.2.2.2.2), hkeep⟩

/-- Function 49 of the module is its export `erfc`. -/
theorem erfc_export :
    ({ name := "erfc", funcIdx := 49 } : Wasm.Export) ∈ Erfc.compiled.module.exports := by
  decide +kernel

/-- **The accuracy theorem for the compiled `erfc`**: the bytes decode to the module, whose
function 49 is exported as `erfc`, and the initial store is ready.  A call of that entry from a
ready store returns without a trap the bits of `Erfc.erfc x` and leaves a ready store in which every
region of the heap before the call keeps its bytes.  For finite `x` the value lies within one step
of the nearest-even rounding of `erfc x`. -/
theorem erfc_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Erfc.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Erfc.compiled.module ∧
      ({ name := "erfc", funcIdx := 49 } : Wasm.Export) ∈ Erfc.compiled.module.exports ∧
      Ready (Verified.initialHeap Erfc.compiled.tables) Erfc.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Erfc.compiled.module 49 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Erfc.erfc x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (RealErf.erfc (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Erfc.compiled.bytes
  refine ⟨bytes, henc, hdec, erfc_export, ready_initial,
    fun env heap store x h => (erfc_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Erfc.erfc x).toBits, hv, rfl, ErfcTheorem.erfc_within_one x, hrest⟩

#print axioms ready_initial
#print axioms erfc_entry_call
#print axioms erfc_export
#print axioms erfc_bytes_accuracy

end Verified.Examples.ErfcBytes
