import Verified.Examples.LgammaWithin
import LeanExe.ProofKit.BorrowedKept

/-!
The byte theorem for `lgamma` in the module of `Lgamma.lean`, whose export `lgamma` is function 44.
The module writes seven tables from address 4096, all of which `lgamma` reads: `Tgamma.logdTable`
at 4096, `Lgamma.logAccurateTable` at 6216, `Lgamma.sinpiTable` at 7952, `Lgamma.asymTable` at
9280, `Lgamma.accurateTable` at 10056, `Lgamma.dbTable` at 18152, and `Lgamma.mainTable` at 18616.
A store is ready when the allocator invariant holds, the seven tables are borrowed arrays at their
addresses, and the memory cap is at most 65,535 pages.  A call of the entry from a ready store
returns without a trap the bits of `Lgamma.lgamma x` and leaves a ready store, so the theorem
covers every sequence of calls from the initial store.  The bound is that of
`LgammaWithin.lgamma_within`: one step of the nearest-even rounding of `ln |Γ x|` for every finite
`x` other than 0 and the negative integers.
-/

namespace Verified.Examples.LgammaBytes
open CodeLib.IEEE64
open LeanExe.ProofKit

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entry runs, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Tgamma.logdTable ∧
    heap.Borrowed store 6216 Lgamma.logAccurateTable ∧
    heap.Borrowed store 7952 Lgamma.sinpiTable ∧ heap.Borrowed store 9280 Lgamma.asymTable ∧
    heap.Borrowed store 10056 Lgamma.accurateTable ∧ heap.Borrowed store 18152 Lgamma.dbTable ∧
    heap.Borrowed store 18616 Lgamma.mainTable ∧
    store.memoryCap Lgamma.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready (Verified.initialHeap Lgamma.compiled.tables) Lgamma.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Lgamma.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hBor 2 (by decide), hBor 3 (by decide),
    hBor 4 (by decide), hBor 5 (by decide), hBor 6 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
/-- After a call that keeps every region of the heap, a ready store stays ready. -/
theorem ready_kept (heap heap' : Heap) (store final : Store Unit) (h : Ready heap store)
    (hAt' : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r)
    (hcap : final.memoryCap Lgamma.compiled.module 0 ≤ 65535) : Ready heap' final :=
  ⟨hAt', BorrowedKept.borrowed_kept h.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.1 hAt' hkeep, BorrowedKept.borrowed_kept h.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.2.2.1 hAt' hkeep, hcap⟩

open Wasm LeanExe.Pipeline in
/-- The tables of a ready store, as the entry takes them. -/
theorem lgamma_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Tgamma.logdTable), ((6216 : UInt64), Lgamma.logAccurateTable),
        ((7952 : UInt64), Lgamma.sinpiTable), ((9280 : UInt64), Lgamma.asymTable),
        ((10056 : UInt64), Lgamma.accurateTable), ((18152 : UInt64), Lgamma.dbTable),
        ((18616 : UInt64), Lgamma.mainTable)],
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
/-- A call of the module's `lgamma` entry from a ready store. -/
theorem lgamma_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Lgamma.compiled.module 44 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Lgamma.lgamma x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Lgamma.compiled.lgamma.implements env store heap [.f64 x.toBits] x h.1 trivial
    (lgamma_tables heap store h) rfl Separate.nil h.2.2.2.2.2.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Lgamma.lgamma x).toBits] := howned
  have hvs : values = [.f64 (Lgamma.lgamma x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2.2.2.2.2.2), hkeep⟩

/-- Function 44 of the module is its export `lgamma`. -/
theorem lgamma_export :
    ({ name := "lgamma", funcIdx := 44 } : Wasm.Export) ∈ Lgamma.compiled.module.exports := by
  decide +kernel

/-- **The accuracy theorem for the compiled `lgamma`**: the bytes decode to the module, whose
function 44 is exported as `lgamma`, and the initial store is ready.  A call of that entry from a
ready store returns without a trap the bits of `Lgamma.lgamma x` and leaves a ready store in which
every region of the heap before the call keeps its bytes.  For every finite `x` other than 0 and
the negative integers the value lies within one step of the nearest-even rounding of
`ln |Γ x|`. -/
theorem lgamma_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Lgamma.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Lgamma.compiled.module ∧
      ({ name := "lgamma", funcIdx := 44 } : Wasm.Export) ∈ Lgamma.compiled.module.exports ∧
      Ready (Verified.initialHeap Lgamma.compiled.tables) Lgamma.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Lgamma.compiled.module 44 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Lgamma.lgamma x).toBits ∧
            (Finite x.toBits → (∀ n : ℤ, value x.toBits = n → 0 < n) →
              F64SignedRounding.WithinSteps 1 (Real.log |Real.Gamma (value x.toBits)|) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Lgamma.compiled.bytes
  refine ⟨bytes, henc, hdec, lgamma_export, ready_initial,
    fun env heap store x h => (lgamma_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  refine ⟨(Lgamma.lgamma x).toBits, hv, rfl, fun hf hp => ?_, hrest⟩
  rw [LgammaSpecial.log_abs_gamma]
  exact LgammaWithin.lgamma_within x hf hp

#print axioms ready_initial
#print axioms lgamma_entry_call
#print axioms lgamma_export
#print axioms lgamma_bytes_accuracy

end Verified.Examples.LgammaBytes
