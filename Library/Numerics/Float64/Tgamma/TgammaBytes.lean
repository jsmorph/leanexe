import Library.Numerics.Float64.Tgamma.TgammaWithin
import LeanExe.ProofKit.BorrowedKept

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
open CodeLib.IEEE64
open LeanExe.ProofKit

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entry runs, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Tgamma.dbTable ∧
    heap.Borrowed store 5472 Tgamma.accurateTable ∧ heap.Borrowed store 11224 Tgamma.smallTable ∧
    heap.Borrowed store 11440 Tgamma.mainTable ∧ heap.Borrowed store 11880 Tgamma.logdTable ∧
    heap.Borrowed store 14000 Tgamma.sinpidTable ∧ heap.Borrowed store 15112 Tgamma.expdTable ∧
    heap.Borrowed store 16224 Tgamma.asymTable ∧ store.memoryCap Tgamma.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready (Verified.initialHeap Tgamma.compiled.tables) Tgamma.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Tgamma.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hBor 2 (by decide), hBor 3 (by decide),
    hBor 4 (by decide), hBor 5 (by decide), hBor 6 (by decide), hBor 7 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
/-- After a call that keeps every region of the heap, a ready store stays ready. -/
theorem ready_kept (heap heap' : Heap) (store final : Store Unit) (h : Ready heap store)
    (hAt' : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r)
    (hcap : final.memoryCap Tgamma.compiled.module 0 ≤ 65535) : Ready heap' final :=
  ⟨hAt', BorrowedKept.borrowed_kept h.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.1 hAt' hkeep, BorrowedKept.borrowed_kept h.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.2.2.2.1 hAt' hkeep, hcap⟩

open Wasm LeanExe.Pipeline in
/-- The tables of a ready store, as the entry takes them. -/
theorem tgamma_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Tgamma.dbTable), ((5472 : UInt64), Tgamma.accurateTable),
        ((11224 : UInt64), Tgamma.smallTable), ((11440 : UInt64), Tgamma.mainTable),
        ((11880 : UInt64), Tgamma.logdTable), ((14000 : UInt64), Tgamma.sinpidTable),
        ((15112 : UInt64), Tgamma.expdTable), ((16224 : UInt64), Tgamma.asymTable)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht | ht | ht | ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.2.2.2.1, Apart.nil⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `tgamma` entry from a ready store. -/
theorem tgamma_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Tgamma.compiled.module 41 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Tgamma.tgamma x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Tgamma.compiled.tgamma.implements env store heap [.f64 x.toBits] x h.1 trivial
    (tgamma_tables heap store h) rfl Separate.nil h.2.2.2.2.2.2.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Tgamma.tgamma x).toBits] := howned
  have hvs : values = [.f64 (Tgamma.tgamma x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2.2.2.2.2.2.2), hkeep⟩

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
      Ready (Verified.initialHeap Tgamma.compiled.tables) Tgamma.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Tgamma.compiled.module 41 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Tgamma.tgamma x).toBits ∧
            (Finite x.toBits → (∀ n : ℤ, n ≤ 0 → value x.toBits ≠ n) →
              F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
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
