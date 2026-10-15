import Verified.Examples.PrintFloatTheorem

/-!
The byte theorems for the module of `PrintFloat.lean`, whose exports `print64` (function 35),
`print64Ecma` (36), `print32` (37), and `print32Ecma` (38) take a word and return a string as an
array of one-byte words that the caller owns.  The module holds no tables, so a store is ready
when the allocator invariant holds and the memory cap is at most 65,535 pages.  A call from a
ready store either traps at `unreachable` when an allocation finds no memory, or returns a pointer
to the new array, whose string `PrintFloatTheorem.derives64` and `derives32` describe, and leaves
a ready store in which every region of the heap before the call keeps its bytes and lies apart
from the new array.  The theorems therefore cover every sequence of calls from the initial store.
-/

namespace Verified.Examples.PrintFloatBytes
open LeanExe.ProofKit StrconvGrammar StrconvRound PrintFloatTheorem

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entries run, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ store.memoryCap PrintFloat.compiled.module 0 ≤ 65535

open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready. -/
theorem ready_initial :
    Ready (Verified.initialHeap PrintFloat.compiled.tables)
      PrintFloat.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, _⟩ := PrintFloat.compiled.initial
  exact ⟨hAt, hCap⟩

open Wasm LeanExe.Pipeline LeanExe.Runtime in
/-- A call of an entry that implements `f` on a word, from a ready store: it traps when memory
runs out, or returns a pointer to an owned array holding `f w`, apart from every region of the
heap before the call, which keeps its bytes. -/
theorem entry_call (entry : Nat) (f : UInt64 → Array UInt64)
    (himpl : ImplementsA true PrintFloat.compiled.module entry f (fun _ _ _ => True)
      (fun _ _ _ _ _ => True))
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (w : UInt64) (h : Ready heap store) :
    Runs true env PrintFloat.compiled.module entry store [.i64 w] fun final values =>
      ∃ ptr : UInt64, values = [.i64 ptr] ∧ ∃ heap' : Heap, Ready heap' final ∧
        heap'.Owned final ptr (f w) ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ regionsDisjoint r (block final ptr) := by
  refine (himpl env store heap [.i64 w] w h.1 trivial rfl Separate.nil h.2).mono ?_
  intro final values ⟨heap', hAt', howned, hcaps, hframe, _⟩
  obtain ⟨ptr, hv, hown⟩ : ∃ ptr, values.reverse = [.i64 ptr] ∧ heap'.Owned final ptr (f w) :=
    howned
  have hvs : values = [.i64 ptr] := by simpa using congrArg List.reverse hv
  refine ⟨ptr, hvs, heap', ⟨hAt', memoryCap_le_of_caps hcaps h.2⟩, hown, fun r hr hpos => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hframe r hr hpos Apart.nil
  refine ⟨h1, h2, h3 _ ?_⟩
  rw [hv]
  exact List.mem_singleton_self _

open Wasm LeanExe.Pipeline LeanExe.Runtime in
/-- A call of a binary64 printer: the string is a number of the general grammar that rounds to
`canon64 w`, of RFC 8259's grammar for a finite word, and for a finite nonzero word the layout of
a `Shortest64` decimal with no trailing zero. -/
theorem print64_entry (ecma : Bool) (entry : Nat)
    (himpl : ImplementsA true PrintFloat.compiled.module entry
      (fun x => PrintFloat.print64With ecma x) (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (w : UInt64) (h : Ready heap store) :
    Runs true env PrintFloat.compiled.module entry store [.i64 w] fun final values =>
      ∃ (ptr : UInt64) (s : List UInt8) (n : Num), values = [.i64 ptr] ∧
        Derives true s n ∧ round64 n = canon64 w ∧
        (Wasm.IEEE64.isFinite w = true → Derives false s n) ∧
        (Wasm.IEEE64.isFinite w = true → Wasm.IEEE64.scaledMagnitude w ≠ 0 →
          ∃ neg t k, t % 10 ≠ 0 ∧ Shortest64 w neg t k ∧
            s = if ecma then ecmaLayout neg t k else sciLayout neg t k) ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Owned final ptr (words s) ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r ∧ regionsDisjoint r (block final ptr) := by
  obtain ⟨s, n, h1, h2, h3, h4, -, h6⟩ := derives64 ecma w
  refine (entry_call entry _ himpl env heap store w h).mono ?_
  intro final values ⟨ptr, hv, heap', hr, ho, hf⟩
  refine ⟨ptr, s, n, hv, h2, h4, h3, h6, heap', hr, ?_, hf⟩
  rw [← h1]
  exact ho

open Wasm LeanExe.Pipeline LeanExe.Runtime in
/-- A call of a binary32 printer, which reads the pattern `w.toUInt32` from the low 32 bits of
its argument, as `print64_entry`. -/
theorem print32_entry (ecma : Bool) (entry : Nat)
    (himpl : ImplementsA true PrintFloat.compiled.module entry
      (fun x => PrintFloat.print32With ecma x) (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (w : UInt64) (h : Ready heap store) :
    Runs true env PrintFloat.compiled.module entry store [.i64 w] fun final values =>
      ∃ (ptr : UInt64) (s : List UInt8) (n : Num), values = [.i64 ptr] ∧
        Derives true s n ∧ round32 n = canon32 w.toUInt32 ∧
        (Wasm.IEEE32.isFinite w.toUInt32 = true → Derives false s n) ∧
        (Wasm.IEEE32.isFinite w.toUInt32 = true → Wasm.IEEE32.scaledMagnitude w.toUInt32 ≠ 0 →
          ∃ neg t k, t % 10 ≠ 0 ∧ Shortest32 w.toUInt32 neg t k ∧
            s = if ecma then ecmaLayout neg t k else sciLayout neg t k) ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Owned final ptr (words s) ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r ∧ regionsDisjoint r (block final ptr) := by
  obtain ⟨s, n, h1, h2, h3, h4, -, h6⟩ := derives32 ecma w.toUInt32
  have hlow : PrintFloat.print32With ecma w = PrintFloat.print32With ecma w.toUInt32.toUInt64 := by
    cases ecma
    · exact PrintFloatWord32.print32_low w
    · exact PrintFloatWord32.print32Ecma_low w
  refine (entry_call entry _ himpl env heap store w h).mono ?_
  intro final values ⟨ptr, hv, heap', hr, ho, hf⟩
  refine ⟨ptr, s, n, hv, h2, h4, h3, h6, heap', hr, ?_, hf⟩
  rw [← h1, ← hlow]
  exact ho

/-- Function 35 of the module is its export `print64`. -/
theorem print64_export :
    ({ name := "print64", funcIdx := 35 } : Wasm.Export) ∈ PrintFloat.compiled.module.exports := by
  decide +kernel

/-- Function 36 of the module is its export `print64Ecma`. -/
theorem print64Ecma_export :
    ({ name := "print64Ecma", funcIdx := 36 } : Wasm.Export) ∈
      PrintFloat.compiled.module.exports := by
  decide +kernel

/-- Function 37 of the module is its export `print32`. -/
theorem print32_export :
    ({ name := "print32", funcIdx := 37 } : Wasm.Export) ∈ PrintFloat.compiled.module.exports := by
  decide +kernel

/-- Function 38 of the module is its export `print32Ecma`. -/
theorem print32Ecma_export :
    ({ name := "print32Ecma", funcIdx := 38 } : Wasm.Export) ∈
      PrintFloat.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `print64`: the bytes decode to the module, whose
function 35 is exported as `print64`, and the initial store is ready.  A call of that entry from a
ready store with a word `w` traps when memory runs out or returns a pointer to an array the caller
owns, holding the words of a string `s`.  The string is a number `n` of the general grammar with
`round64 n = canon64 w`, so that the general parser reads it back as `canon64 w`; for a finite
word it is a number of RFC 8259's grammar; and for a finite nonzero word it is the scientific
layout of a `Shortest64` decimal `t · 10^k` with no trailing zero.  The call leaves a ready store
in which every region of the heap before the call keeps its bytes and lies apart from the array. -/
theorem print64_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode PrintFloat.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok PrintFloat.compiled.module ∧
      ({ name := "print64", funcIdx := 35 } : Wasm.Export) ∈ PrintFloat.compiled.module.exports ∧
      Ready (Verified.initialHeap PrintFloat.compiled.tables)
        PrintFloat.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (w : UInt64), Ready heap store →
        Wasm.Runs true env PrintFloat.compiled.module 35 store [.i64 w]
          (fun final values =>
            ∃ (ptr : UInt64) (s : List UInt8) (n : Num), values = [.i64 ptr] ∧
              Derives true s n ∧ round64 n = canon64 w ∧
              (Wasm.IEEE64.isFinite w = true → Derives false s n) ∧
              (Wasm.IEEE64.isFinite w = true → Wasm.IEEE64.scaledMagnitude w ≠ 0 →
                ∃ neg t k, t % 10 ≠ 0 ∧ Shortest64 w neg t k ∧ s = sciLayout neg t k) ∧
              ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
                heap'.Owned final ptr (words s) ∧
                ∀ r, heap.Region r → 0 < r.2 →
                  (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                    heap'.Region r ∧
                    LeanExe.Runtime.regionsDisjoint r (LeanExe.Pipeline.block final ptr)) := by
  obtain ⟨bytes, henc, hdec, _⟩ := PrintFloat.compiled.bytes
  exact ⟨bytes, henc, hdec, print64_export, ready_initial, fun env heap store w h =>
    print64_entry false 35 PrintFloat.compiled.print64.implements env heap store w h⟩

/-- The accuracy theorem for the compiled `print64Ecma`, as `print64_bytes_accuracy` for function
36, with the layout of ECMA-262's Number::toString. -/
theorem print64Ecma_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode PrintFloat.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok PrintFloat.compiled.module ∧
      ({ name := "print64Ecma", funcIdx := 36 } : Wasm.Export) ∈
        PrintFloat.compiled.module.exports ∧
      Ready (Verified.initialHeap PrintFloat.compiled.tables)
        PrintFloat.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (w : UInt64), Ready heap store →
        Wasm.Runs true env PrintFloat.compiled.module 36 store [.i64 w]
          (fun final values =>
            ∃ (ptr : UInt64) (s : List UInt8) (n : Num), values = [.i64 ptr] ∧
              Derives true s n ∧ round64 n = canon64 w ∧
              (Wasm.IEEE64.isFinite w = true → Derives false s n) ∧
              (Wasm.IEEE64.isFinite w = true → Wasm.IEEE64.scaledMagnitude w ≠ 0 →
                ∃ neg t k, t % 10 ≠ 0 ∧ Shortest64 w neg t k ∧ s = ecmaLayout neg t k) ∧
              ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
                heap'.Owned final ptr (words s) ∧
                ∀ r, heap.Region r → 0 < r.2 →
                  (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                    heap'.Region r ∧
                    LeanExe.Runtime.regionsDisjoint r (LeanExe.Pipeline.block final ptr)) := by
  obtain ⟨bytes, henc, hdec, _⟩ := PrintFloat.compiled.bytes
  exact ⟨bytes, henc, hdec, print64Ecma_export, ready_initial, fun env heap store w h =>
    print64_entry true 36 PrintFloat.compiled.print64Ecma.implements env heap store w h⟩

/-- The accuracy theorem for the compiled `print32`, as `print64_bytes_accuracy` for function 37
and the binary32 pattern `w.toUInt32` in the low 32 bits of the argument. -/
theorem print32_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode PrintFloat.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok PrintFloat.compiled.module ∧
      ({ name := "print32", funcIdx := 37 } : Wasm.Export) ∈ PrintFloat.compiled.module.exports ∧
      Ready (Verified.initialHeap PrintFloat.compiled.tables)
        PrintFloat.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (w : UInt64), Ready heap store →
        Wasm.Runs true env PrintFloat.compiled.module 37 store [.i64 w]
          (fun final values =>
            ∃ (ptr : UInt64) (s : List UInt8) (n : Num), values = [.i64 ptr] ∧
              Derives true s n ∧ round32 n = canon32 w.toUInt32 ∧
              (Wasm.IEEE32.isFinite w.toUInt32 = true → Derives false s n) ∧
              (Wasm.IEEE32.isFinite w.toUInt32 = true →
                Wasm.IEEE32.scaledMagnitude w.toUInt32 ≠ 0 →
                ∃ neg t k, t % 10 ≠ 0 ∧ Shortest32 w.toUInt32 neg t k ∧ s = sciLayout neg t k) ∧
              ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
                heap'.Owned final ptr (words s) ∧
                ∀ r, heap.Region r → 0 < r.2 →
                  (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                    heap'.Region r ∧
                    LeanExe.Runtime.regionsDisjoint r (LeanExe.Pipeline.block final ptr)) := by
  obtain ⟨bytes, henc, hdec, _⟩ := PrintFloat.compiled.bytes
  exact ⟨bytes, henc, hdec, print32_export, ready_initial, fun env heap store w h =>
    print32_entry false 37 PrintFloat.compiled.print32.implements env heap store w h⟩

/-- The accuracy theorem for the compiled `print32Ecma`, as `print32_bytes_accuracy` for function
38, with the layout of ECMA-262's Number::toString. -/
theorem print32Ecma_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode PrintFloat.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok PrintFloat.compiled.module ∧
      ({ name := "print32Ecma", funcIdx := 38 } : Wasm.Export) ∈
        PrintFloat.compiled.module.exports ∧
      Ready (Verified.initialHeap PrintFloat.compiled.tables)
        PrintFloat.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (w : UInt64), Ready heap store →
        Wasm.Runs true env PrintFloat.compiled.module 38 store [.i64 w]
          (fun final values =>
            ∃ (ptr : UInt64) (s : List UInt8) (n : Num), values = [.i64 ptr] ∧
              Derives true s n ∧ round32 n = canon32 w.toUInt32 ∧
              (Wasm.IEEE32.isFinite w.toUInt32 = true → Derives false s n) ∧
              (Wasm.IEEE32.isFinite w.toUInt32 = true →
                Wasm.IEEE32.scaledMagnitude w.toUInt32 ≠ 0 →
                ∃ neg t k, t % 10 ≠ 0 ∧ Shortest32 w.toUInt32 neg t k ∧ s = ecmaLayout neg t k) ∧
              ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
                heap'.Owned final ptr (words s) ∧
                ∀ r, heap.Region r → 0 < r.2 →
                  (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                    heap'.Region r ∧
                    LeanExe.Runtime.regionsDisjoint r (LeanExe.Pipeline.block final ptr)) := by
  obtain ⟨bytes, henc, hdec, _⟩ := PrintFloat.compiled.bytes
  exact ⟨bytes, henc, hdec, print32Ecma_export, ready_initial, fun env heap store w h =>
    print32_entry true 38 PrintFloat.compiled.print32Ecma.implements env heap store w h⟩

#print axioms ready_initial
#print axioms entry_call
#print axioms print64_export
#print axioms print64Ecma_export
#print axioms print32_export
#print axioms print32Ecma_export
#print axioms print64_bytes_accuracy
#print axioms print64Ecma_bytes_accuracy
#print axioms print32_bytes_accuracy
#print axioms print32Ecma_bytes_accuracy

end Verified.Examples.PrintFloatBytes
