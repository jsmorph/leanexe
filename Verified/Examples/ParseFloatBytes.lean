import Verified.Examples.ParseFloatTheorem
import LeanExe.ProofKit.BorrowedKept

/-!
The byte theorems for the module of `ParseFloat.lean`, whose exports `parse64` (function 35) and
`parse32` (function 36) take the flag of the general grammar as a word, 1 or 0, and a string as a
borrowed array of one-byte words, and return the result word and the acceptance flag.  The module
holds no tables, so a store is ready when the allocator invariant holds and the memory cap is at
most 65,535 pages.  A call from a ready store, with the string a borrowed array of the heap,
either traps at `unreachable` when an allocation finds no memory, or returns the words of
`parse64 general (words s)`, which `ParseFloatTheorem.parse64_spec` describes, and leaves a ready
store in which the string is still a borrowed array and every region of the heap before the call
keeps its bytes.  The theorems therefore cover every sequence of calls from the initial store.
-/

namespace Verified.Examples.ParseFloatBytes
open LeanExe.ProofKit StrconvGrammar StrconvRound StrconvDecode

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entries run, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ store.memoryCap ParseFloat.compiled.module 0 ≤ 65535

open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready. -/
theorem ready_initial :
    Ready (Verified.initialHeap ParseFloat.compiled.tables) ParseFloat.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, _⟩ := ParseFloat.compiled.initial
  exact ⟨hAt, hCap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `parse64` entry from a ready store with a borrowed string `ws`: it
traps when memory runs out, or returns the result word and the flag of `parse64 general ws`. -/
theorem parse64_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (general : Bool) (ws : Array UInt64) (ptr : UInt64) (h : Ready heap store)
    (hb : heap.Borrowed store ptr ws) :
    Runs true env ParseFloat.compiled.module 35 store [.i64 ptr, .i64 (cond general 1 0)]
      fun final values =>
        values = [.i64 (ParseFloat.parse64 general ws).2,
          .i64 (cond (ParseFloat.parse64 general ws).1 1 0)] ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr ws ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r := by
  have hargs : Represent.borrowed heap store [.i64 (cond general 1 0), .i64 ptr] (general, ws) :=
    ⟨[.i64 (cond general 1 0)], [.i64 ptr], rfl, rfl, ptr, rfl, hb⟩
  refine (ParseFloat.compiled.parse64.implements env store heap [.i64 (cond general 1 0), .i64 ptr]
    (general, ws) h.1 trivial hargs Separate.nil h.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.i64 (cond (ParseFloat.parse64 general ws).1 1 0),
      .i64 (ParseFloat.parse64 general ws).2] := howned
  have hvs : values = [.i64 (ParseFloat.parse64 general ws).2,
      .i64 (cond (ParseFloat.parse64 general ws).1 1 0)] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', memoryCap_le_of_caps hcaps h.2⟩,
    BorrowedKept.borrowed_kept hb hAt' hkeep, hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `parse32` entry from a ready store with a borrowed string `ws`. -/
theorem parse32_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (general : Bool) (ws : Array UInt64) (ptr : UInt64) (h : Ready heap store)
    (hb : heap.Borrowed store ptr ws) :
    Runs true env ParseFloat.compiled.module 36 store [.i64 ptr, .i64 (cond general 1 0)]
      fun final values =>
        values = [.i64 (ParseFloat.parse32 general ws).2,
          .i64 (cond (ParseFloat.parse32 general ws).1 1 0)] ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr ws ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r := by
  have hargs : Represent.borrowed heap store [.i64 (cond general 1 0), .i64 ptr] (general, ws) :=
    ⟨[.i64 (cond general 1 0)], [.i64 ptr], rfl, rfl, ptr, rfl, hb⟩
  refine (ParseFloat.compiled.parse32.implements env store heap [.i64 (cond general 1 0), .i64 ptr]
    (general, ws) h.1 trivial hargs Separate.nil h.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.i64 (cond (ParseFloat.parse32 general ws).1 1 0),
      .i64 (ParseFloat.parse32 general ws).2] := howned
  have hvs : values = [.i64 (ParseFloat.parse32 general ws).2,
      .i64 (cond (ParseFloat.parse32 general ws).1 1 0)] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', memoryCap_le_of_caps hcaps h.2⟩,
    BorrowedKept.borrowed_kept hb hAt' hkeep, hkeep⟩

/-- Function 35 of the module is its export `parse64`. -/
theorem parse64_export :
    ({ name := "parse64", funcIdx := 35 } : Wasm.Export) ∈ ParseFloat.compiled.module.exports := by
  decide +kernel

/-- Function 36 of the module is its export `parse32`. -/
theorem parse32_export :
    ({ name := "parse32", funcIdx := 36 } : Wasm.Export) ∈ ParseFloat.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `parse64`: the bytes decode to the module, whose
function 35 is exported as `parse64`, and the initial store is ready.  A call of that entry from
a ready store, with the flag of the general grammar and a string `s` of fewer than `2 ^ 32` bytes
held as a borrowed array of one-byte words, traps when memory runs out or returns the word `w` and
the flag `b`.  When `s` is a number `n` of the grammar, `b = 1` and `w = round64 n`, the binary64
word of roundTiesToEven applied to `n`; otherwise `b = 0` and `w = 0`.  The call leaves a ready
store in which the string is still borrowed and every region of the heap before the call keeps its
bytes. -/
theorem parse64_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode ParseFloat.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok ParseFloat.compiled.module ∧
      ({ name := "parse64", funcIdx := 35 } : Wasm.Export) ∈ ParseFloat.compiled.module.exports ∧
      Ready (Verified.initialHeap ParseFloat.compiled.tables)
        ParseFloat.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (general : Bool) (s : List UInt8) (ptr : UInt64), Ready heap store →
        heap.Borrowed store ptr (words s) → s.length < 2 ^ 32 →
        Wasm.Runs true env ParseFloat.compiled.module 35 store [.i64 ptr, .i64 (cond general 1 0)]
          (fun final values =>
            ∃ b w : UInt64, values = [.i64 w, .i64 b] ∧
              (∀ n, Derives general s n → b = 1 ∧ w = round64 n) ∧
              ((∀ n, ¬ Derives general s n) → b = 0 ∧ w = 0) ∧
              ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
                heap'.Borrowed final ptr (words s) ∧
                ∀ r, heap.Region r → 0 < r.2 →
                  (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                    heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := ParseFloat.compiled.bytes
  refine ⟨bytes, henc, hdec, parse64_export, ready_initial,
    fun env heap store general s ptr h hb hs =>
      (parse64_entry_call env heap store general (words s) ptr h hb).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  refine ⟨_, _, hv, fun n hn => ?_, fun hn => ?_, hrest⟩
  · rw [ParseFloatTheorem.parse64_accept general s n hs hn]; exact ⟨rfl, rfl⟩
  · rw [ParseFloatTheorem.parse64_reject general s hs hn]; exact ⟨rfl, rfl⟩

/-- The accuracy theorem for the compiled `parse32`, as `parse64_bytes_accuracy` for function 36:
when `s` is a number `n` of the grammar, the call returns `b = 1` and the binary32 pattern
`round32 n` in the low 32 bits of `w`; otherwise `b = 0` and `w = 0`. -/
theorem parse32_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode ParseFloat.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok ParseFloat.compiled.module ∧
      ({ name := "parse32", funcIdx := 36 } : Wasm.Export) ∈ ParseFloat.compiled.module.exports ∧
      Ready (Verified.initialHeap ParseFloat.compiled.tables)
        ParseFloat.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (general : Bool) (s : List UInt8) (ptr : UInt64), Ready heap store →
        heap.Borrowed store ptr (words s) → s.length < 2 ^ 32 →
        Wasm.Runs true env ParseFloat.compiled.module 36 store [.i64 ptr, .i64 (cond general 1 0)]
          (fun final values =>
            ∃ b w : UInt64, values = [.i64 w, .i64 b] ∧
              (∀ n, Derives general s n → b = 1 ∧ w = (round32 n).toUInt64) ∧
              ((∀ n, ¬ Derives general s n) → b = 0 ∧ w = 0) ∧
              ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
                heap'.Borrowed final ptr (words s) ∧
                ∀ r, heap.Region r → 0 < r.2 →
                  (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                    heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := ParseFloat.compiled.bytes
  refine ⟨bytes, henc, hdec, parse32_export, ready_initial,
    fun env heap store general s ptr h hb hs =>
      (parse32_entry_call env heap store general (words s) ptr h hb).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  refine ⟨_, _, hv, fun n hn => ?_, fun hn => ?_, hrest⟩
  · rw [ParseFloatTheorem.parse32_accept general s n hs hn]; exact ⟨rfl, rfl⟩
  · rw [ParseFloatTheorem.parse32_reject general s hs hn]; exact ⟨rfl, rfl⟩

#print axioms ready_initial
#print axioms parse64_entry_call
#print axioms parse32_entry_call
#print axioms parse64_export
#print axioms parse32_export
#print axioms parse64_bytes_accuracy
#print axioms parse32_bytes_accuracy

end Verified.Examples.ParseFloatBytes
