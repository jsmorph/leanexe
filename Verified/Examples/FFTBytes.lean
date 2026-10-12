import Verified.Examples.FFTProgram
import Verified.Examples.FFTTheorem
import Verified.Examples.FFTInverse
import Verified.Examples.FFTPower
import LeanExe.ProofKit.BorrowedKept

namespace Verified.Examples.FFTBytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit CodeLib.IEEE64

def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Trig.invPi ∧
    heap.Borrowed store 4264 Trig.halfPi ∧ store.memoryCap FFT.compiled.module 0 ≤ 65535

def EntryReady (heap : Heap) (store : Store Unit) (params : List Value)
    (xs : Array Float) : Prop :=
  Ready heap store ∧ Represent.borrowed heap store params xs

def OutputPost (expected : Array Float) (Q : Array Float → Prop) (heap : Heap)
    (store final : Store Unit) (values : List Value) : Prop :=
  ∃ heap' : Heap, Ready heap' final ∧ ∃ ys : Array Float,
    ys = expected ∧ Represent.owned heap' final values.reverse ys ∧ Q ys ∧
    final.memoryCaps = store.memoryCaps ∧
    ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r ∧ Represent.outside final values.reverse ys r

set_option maxRecDepth 100000 in
theorem ready_initial :
    Ready (Verified.initialHeap FFT.compiled.tables) FFT.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := FFT.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hCap⟩

theorem ready_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩

private theorem outputPost_of_frame (heap heap' : Heap) (store final : Store Unit)
    (values : List Value) (expected : Array Float) (Q : Array Float → Prop)
    (h : Ready heap store) (hAt : heap'.At final)
    (howned : Represent.owned heap' final values.reverse expected) (hQ : Q expected)
    (hcaps : final.memoryCaps = store.memoryCaps)
    (hframe : ∀ r, heap.Region r → 0 < r.2 → Apart store [] r →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r ∧ Represent.outside final values.reverse expected r) :
    OutputPost expected Q heap store final values := by
  have hframe' : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r ∧ Represent.outside final values.reverse expected r :=
    fun r hr hpos => hframe r hr hpos Apart.nil
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe' r hr hpos).1, (hframe' r hr hpos).2.1⟩
  have hReady : Ready heap' final :=
    ⟨hAt, BorrowedKept.borrowed_kept h.2.1 hAt hkeep,
      BorrowedKept.borrowed_kept h.2.2.1 hAt hkeep, memoryCap_le_of_caps hcaps h.2.2.2⟩
  exact ⟨heap', hReady, expected, rfl, howned, hQ, hcaps, hframe'⟩

theorem fft_entry_call_of_post (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (Q : Array Float → Prop)
    (h : EntryReady heap store params xs) (hQ : Q (FFT.fft xs)) :
    Runs true env FFT.compiled.module 27 store params.reverse
      (OutputPost (FFT.fft xs) Q heap store) := by
  refine (FFT.compiled.fft.implements env store heap params xs h.1.1 trivial
    (ready_tables heap store h.1) h.2 Separate.nil h.1.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt, howned, hcaps, hframe, _⟩ := hpost
  exact outputPost_of_frame heap heap' store final values (FFT.fft xs) Q h.1
    hAt howned hQ hcaps hframe

theorem inverse_entry_call_of_post (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (Q : Array Float → Prop)
    (h : EntryReady heap store params xs) (hQ : Q (FFT.inverse xs)) :
    Runs true env FFT.compiled.module 28 store params.reverse
      (OutputPost (FFT.inverse xs) Q heap store) := by
  refine (FFT.compiled.inverse.implements env store heap params xs h.1.1 trivial
    (ready_tables heap store h.1) h.2 Separate.nil h.1.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt, howned, hcaps, hframe, _⟩ := hpost
  exact outputPost_of_frame heap heap' store final values (FFT.inverse xs) Q h.1
    hAt howned hQ hcaps hframe

theorem power_entry_call_of_post (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (samples : Array Float) (Q : Array Float → Prop)
    (h : EntryReady heap store params samples) (hQ : Q (FFT.powerSpectrum samples)) :
    Runs true env FFT.compiled.module 29 store params.reverse
      (OutputPost (FFT.powerSpectrum samples) Q heap store) := by
  refine (FFT.compiled.powerSpectrum.implements env store heap params samples h.1.1 trivial
    (ready_tables heap store h.1) h.2 Separate.nil h.1.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt, howned, hcaps, hframe, _⟩ := hpost
  exact outputPost_of_frame heap heap' store final values (FFT.powerSpectrum samples) Q h.1
    hAt howned hQ hcaps hframe

theorem fft_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (h : EntryReady heap store params xs)
    (ha : FFTSpec.Admissible xs) :
    Runs true env FFT.compiled.module 27 store params.reverse
      (OutputPost (FFT.fft xs) (FFTSpec.AccurateOutput xs) heap store) :=
  fft_entry_call_of_post env heap store params xs (FFTSpec.AccurateOutput xs) h
    (FFTTheorem.fft_accuracy xs ha)

theorem inverse_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (h : EntryReady heap store params xs)
    (ha : FFTSpec.Admissible xs) :
    Runs true env FFT.compiled.module 28 store params.reverse
      (OutputPost (FFT.inverse xs) (FFTSpec.AccurateInverse xs) heap store) :=
  inverse_entry_call_of_post env heap store params xs (FFTSpec.AccurateInverse xs) h
    (FFTInverse.inverse_accuracy xs ha)

theorem power_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (samples : Array Float) (h : EntryReady heap store params samples)
    (ha : FFTSpec.PowerAdmissible samples) :
    Runs true env FFT.compiled.module 29 store params.reverse
      (OutputPost (FFT.powerSpectrum samples) (FFTSpec.AccuratePower samples) heap store) :=
  power_entry_call_of_post env heap store params samples (FFTSpec.AccuratePower samples) h
    (FFTPower.powerSpectrum_accuracy samples ha)

theorem fft_export :
    ({ name := "fft", funcIdx := 27 } : Export) ∈ FFT.compiled.module.exports := by
  decide +kernel

theorem inverse_export :
    ({ name := "inverse", funcIdx := 28 } : Export) ∈ FFT.compiled.module.exports := by
  decide +kernel

theorem power_export :
    ({ name := "powerSpectrum", funcIdx := 29 } : Export) ∈ FFT.compiled.module.exports := by
  decide +kernel

private theorem decoded_module_eq (bytes : ByteArray) (module_ : Module)
    (henc : Encoding.encode FFT.compiled.module = .ok bytes)
    (hdec : Encoding.decode bytes = .ok module_) : module_ = FFT.compiled.module := by
  obtain ⟨encoded, henc', hdec', _⟩ := FFT.compiled.bytes
  have hbytes : bytes = encoded := Except.ok.inj (henc.symm.trans henc')
  subst bytes
  exact Except.ok.inj (hdec.symm.trans hdec')

theorem fft_decoded_accuracy (bytes : ByteArray) (module_ : Module)
    (henc : Encoding.encode FFT.compiled.module = .ok bytes)
    (hdec : Encoding.decode bytes = .ok module_)
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (h : EntryReady heap store params xs)
    (ha : FFTSpec.Admissible xs) :
    Runs true env module_ 27 store params.reverse
      (OutputPost (FFT.fft xs) (FFTSpec.AccurateOutput xs) heap store) := by
  rw [decoded_module_eq bytes module_ henc hdec]
  exact fft_entry_call env heap store params xs h ha

theorem inverse_decoded_accuracy (bytes : ByteArray) (module_ : Module)
    (henc : Encoding.encode FFT.compiled.module = .ok bytes)
    (hdec : Encoding.decode bytes = .ok module_)
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (h : EntryReady heap store params xs)
    (ha : FFTSpec.Admissible xs) :
    Runs true env module_ 28 store params.reverse
      (OutputPost (FFT.inverse xs) (FFTSpec.AccurateInverse xs) heap store) := by
  rw [decoded_module_eq bytes module_ henc hdec]
  exact inverse_entry_call env heap store params xs h ha

theorem power_decoded_accuracy (bytes : ByteArray) (module_ : Module)
    (henc : Encoding.encode FFT.compiled.module = .ok bytes)
    (hdec : Encoding.decode bytes = .ok module_)
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (samples : Array Float) (h : EntryReady heap store params samples)
    (ha : FFTSpec.PowerAdmissible samples) :
    Runs true env module_ 29 store params.reverse
      (OutputPost (FFT.powerSpectrum samples) (FFTSpec.AccuratePower samples) heap store) := by
  rw [decoded_module_eq bytes module_ henc hdec]
  exact power_entry_call env heap store params samples h ha

def ModuleAccuracy : Prop :=
  ∃ bytes, Encoding.encode FFT.compiled.module = .ok bytes ∧
    Encoding.decode bytes = .ok FFT.compiled.module ∧
    ({ name := "fft", funcIdx := 27 } : Export) ∈ FFT.compiled.module.exports ∧
    ({ name := "inverse", funcIdx := 28 } : Export) ∈ FFT.compiled.module.exports ∧
    ({ name := "powerSpectrum", funcIdx := 29 } : Export) ∈ FFT.compiled.module.exports ∧
    Ready (Verified.initialHeap FFT.compiled.tables) FFT.compiled.module.initialStore ∧
    (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
      (params : List Value) (xs : Array Float), EntryReady heap store params xs →
      FFTSpec.Admissible xs → Runs true env FFT.compiled.module 27 store params.reverse
        (OutputPost (FFT.fft xs) (FFTSpec.AccurateOutput xs) heap store)) ∧
    (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
      (params : List Value) (xs : Array Float), EntryReady heap store params xs →
      FFTSpec.Admissible xs → Runs true env FFT.compiled.module 28 store params.reverse
        (OutputPost (FFT.inverse xs) (FFTSpec.AccurateInverse xs) heap store)) ∧
    (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
      (params : List Value) (samples : Array Float), EntryReady heap store params samples →
      FFTSpec.PowerAdmissible samples → Runs true env FFT.compiled.module 29 store params.reverse
        (OutputPost (FFT.powerSpectrum samples) (FFTSpec.AccuratePower samples) heap store))

theorem fft_module_accuracy : ModuleAccuracy := by
  obtain ⟨bytes, henc, hdec, _⟩ := FFT.compiled.bytes
  exact ⟨bytes, henc, hdec, fft_export, inverse_export, power_export,
    ready_initial, fft_entry_call, inverse_entry_call, power_entry_call⟩

#print axioms fft_entry_call
#print axioms inverse_entry_call
#print axioms power_entry_call
#print axioms fft_decoded_accuracy
#print axioms inverse_decoded_accuracy
#print axioms power_decoded_accuracy
#print axioms fft_module_accuracy

end Verified.Examples.FFTBytes
