import Verified.Examples.FourierTheorem
import LeanExe.ProofKit.BorrowedKept

namespace Verified.Examples.FourierBytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit CodeLib.IEEE64

def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Trig.invPi ∧
    heap.Borrowed store 4264 Trig.halfPi ∧
    store.memoryCap Fourier.compiled.module 0 ≤ 65535

def EntryReady (heap : Heap) (store : Store Unit) (params : List Value)
    (xs : Array Float) : Prop :=
  Ready heap store ∧ Represent.borrowed heap store params xs

def ResultPost (xs : Array Float) (Q : Array Float → Prop) (heap : Heap)
    (store final : Store Unit) (values : List Value) : Prop :=
  ∃ heap' : Heap, Ready heap' final ∧ ∃ ys : Array Float,
    ys = Fourier.dft xs ∧ Represent.owned heap' final values.reverse ys ∧ Q ys ∧
    final.memoryCaps = store.memoryCaps ∧
    ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r ∧ Represent.outside final values.reverse ys r

set_option maxRecDepth 100000 in
theorem ready_initial :
    Ready (Verified.initialHeap Fourier.compiled.tables) Fourier.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Fourier.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hCap⟩

theorem ready_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩

theorem ready_kept (heap heap' : Heap) (store final : Store Unit) (h : Ready heap store)
    (hAt' : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r)
    (hcap : final.memoryCap Fourier.compiled.module 0 ≤ 65535) : Ready heap' final :=
  ⟨hAt', BorrowedKept.borrowed_kept h.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.1 hAt' hkeep, hcap⟩

theorem dft_entry_call_of_post (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (Q : Array Float → Prop)
    (h : EntryReady heap store params xs) (hQ : Q (Fourier.dft xs)) :
    Runs true env Fourier.compiled.module 21 store params.reverse
      (ResultPost xs Q heap store) := by
  refine (Fourier.compiled.dft.implements env store heap params xs h.1.1 trivial
    (ready_tables heap store h.1) h.2 Separate.nil h.1.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hframe' : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r ∧ Represent.outside final values.reverse (Fourier.dft xs) r :=
    fun r hr hpos => hframe r hr hpos Apart.nil
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe' r hr hpos).1, (hframe' r hr hpos).2.1⟩
  exact ⟨heap', ready_kept heap heap' store final h.1 hAt' hkeep
    (memoryCap_le_of_caps hcaps h.1.2.2.2), Fourier.dft xs, rfl, howned, hQ, hcaps, hframe'⟩

theorem dft_export :
    ({ name := "dft", funcIdx := 21 } : Export) ∈ Fourier.compiled.module.exports := by
  decide +kernel

theorem dft_decoded_call_of_post (bytes : ByteArray) (module_ : Module)
    (henc : Encoding.encode Fourier.compiled.module = .ok bytes)
    (hdec : Encoding.decode bytes = .ok module_)
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (Q : Array Float → Prop)
    (h : EntryReady heap store params xs) (hQ : Q (Fourier.dft xs)) :
    Runs true env module_ 21 store params.reverse (ResultPost xs Q heap store) := by
  obtain ⟨encoded, henc', hdec', _⟩ := Fourier.compiled.bytes
  have hbytes : bytes = encoded := Except.ok.inj (henc.symm.trans henc')
  subst bytes
  have hmodule : module_ = Fourier.compiled.module := Except.ok.inj (hdec.symm.trans hdec')
  subst module_
  exact dft_entry_call_of_post env heap store params xs Q h hQ

def AccurateOutput (xs ys : Array Float) : Prop :=
  ys.size = 2 * (xs.size / 2) ∧
    ∀ k, k < xs.size / 2 →
      Finite ys[2 * k]!.toBits ∧ Finite ys[2 * k + 1]!.toBits ∧
      |value ys[2 * k]!.toBits - FourierSpec.realDFT xs k| ≤ FourierSpec.errorBound xs ∧
      |value ys[2 * k + 1]!.toBits - FourierSpec.imagDFT xs k| ≤ FourierSpec.errorBound xs

/-- With enough fuel, the call returns an owned array satisfying the error bound and preserving
the borrowed input and tables, or traps at `unreachable`. -/
theorem dft_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (h : EntryReady heap store params xs)
    (ha : FourierSpec.Admissible xs) :
    Runs true env Fourier.compiled.module 21 store params.reverse
      (ResultPost xs (AccurateOutput xs) heap store) :=
  dft_entry_call_of_post env heap store params xs (AccurateOutput xs) h
    (FourierTheorem.dft_accuracy xs ha)

theorem dft_decoded_accuracy (bytes : ByteArray) (module_ : Module)
    (henc : Encoding.encode Fourier.compiled.module = .ok bytes)
    (hdec : Encoding.decode bytes = .ok module_)
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (h : EntryReady heap store params xs)
    (ha : FourierSpec.Admissible xs) :
    Runs true env module_ 21 store params.reverse
      (ResultPost xs (AccurateOutput xs) heap store) :=
  dft_decoded_call_of_post bytes module_ henc hdec env heap store params xs (AccurateOutput xs) h
    (FourierTheorem.dft_accuracy xs ha)

theorem dft_bytes_accuracy :
    ∃ bytes, Encoding.encode Fourier.compiled.module = .ok bytes ∧
      Encoding.decode bytes = .ok Fourier.compiled.module ∧
      ({ name := "dft", funcIdx := 21 } : Export) ∈ Fourier.compiled.module.exports ∧
      Ready (Verified.initialHeap Fourier.compiled.tables) Fourier.compiled.module.initialStore ∧
      ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
        (params : List Value) (xs : Array Float), EntryReady heap store params xs →
        FourierSpec.Admissible xs →
        Runs true env Fourier.compiled.module 21 store params.reverse
          (ResultPost xs (AccurateOutput xs) heap store) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Fourier.compiled.bytes
  exact ⟨bytes, henc, hdec, dft_export, ready_initial, dft_entry_call⟩

#print axioms ready_initial
#print axioms dft_entry_call_of_post
#print axioms dft_export
#print axioms dft_decoded_call_of_post
#print axioms dft_entry_call
#print axioms dft_decoded_accuracy
#print axioms dft_bytes_accuracy

end Verified.Examples.FourierBytes
