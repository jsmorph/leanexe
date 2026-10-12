import Verified.Examples.FourierBytes
import Verified.Examples.FourierInverse
import Verified.Examples.FourierPowerTheorem

namespace Verified.Examples.FourierExtraBytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit CodeLib.IEEE64 FourierBytes

def OutputPost (expected : Array Float) (Q : Array Float → Prop) (heap : Heap)
    (store final : Store Unit) (values : List Value) : Prop :=
  ∃ heap' : Heap, Ready heap' final ∧ ∃ ys : Array Float,
    ys = expected ∧ Represent.owned heap' final values.reverse ys ∧ Q ys ∧
    final.memoryCaps = store.memoryCaps ∧
    ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r ∧ Represent.outside final values.reverse ys r

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
  exact ⟨heap', ready_kept heap heap' store final h hAt hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2), expected, rfl, howned, hQ, hcaps, hframe'⟩

theorem inverse_entry_call_of_post (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (Q : Array Float → Prop)
    (h : EntryReady heap store params xs) (hQ : Q (Fourier.inverse xs)) :
    Runs true env Fourier.compiled.module 22 store params.reverse
      (OutputPost (Fourier.inverse xs) Q heap store) := by
  refine (Fourier.compiled.inverse.implements env store heap params xs h.1.1 trivial
    (ready_tables heap store h.1) h.2 Separate.nil h.1.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt, howned, hcaps, hframe, _⟩ := hpost
  exact outputPost_of_frame heap heap' store final values (Fourier.inverse xs) Q h.1
    hAt howned hQ hcaps hframe

theorem power_entry_call_of_post (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (samples : Array Float) (Q : Array Float → Prop)
    (h : EntryReady heap store params samples) (hQ : Q (Fourier.powerSpectrum samples)) :
    Runs true env Fourier.compiled.module 23 store params.reverse
      (OutputPost (Fourier.powerSpectrum samples) Q heap store) := by
  refine (Fourier.compiled.powerSpectrum.implements env store heap params samples h.1.1 trivial
    (ready_tables heap store h.1) h.2 Separate.nil h.1.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt, howned, hcaps, hframe, _⟩ := hpost
  exact outputPost_of_frame heap heap' store final values (Fourier.powerSpectrum samples) Q h.1
    hAt howned hQ hcaps hframe

theorem inverse_export :
    ({ name := "inverse", funcIdx := 22 } : Export) ∈ Fourier.compiled.module.exports := by
  decide +kernel

theorem power_export :
    ({ name := "powerSpectrum", funcIdx := 23 } : Export) ∈ Fourier.compiled.module.exports := by
  decide +kernel

def InverseOutput (xs ys : Array Float) : Prop :=
  ys.size = 2 * (xs.size / 2) ∧
    ∀ k, k < xs.size / 2 →
      Finite ys[2 * k]!.toBits ∧ Finite ys[2 * k + 1]!.toBits ∧
      |value ys[2 * k]!.toBits - FourierInverse.realReference xs k| ≤
        FourierInverse.errorBound xs ∧
      |value ys[2 * k + 1]!.toBits - FourierInverse.imagReference xs k| ≤
        FourierInverse.errorBound xs

def PowerOutput (samples ys : Array Float) : Prop :=
  ys.size = FourierPowerEmbedding.powerCount samples.size ∧
    ∀ k, k < FourierPowerEmbedding.powerCount samples.size →
      Finite ys[k]!.toBits ∧ 0 ≤ value ys[k]!.toBits ∧
      |value ys[k]!.toBits - FourierPowerSpec.realPower samples k| ≤
        FourierPowerSpec.errorBound samples

theorem inverse_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (h : EntryReady heap store params xs)
    (ha : FourierSpec.Admissible xs) :
    Runs true env Fourier.compiled.module 22 store params.reverse
      (OutputPost (Fourier.inverse xs) (InverseOutput xs) heap store) :=
  inverse_entry_call_of_post env heap store params xs (InverseOutput xs) h
    (FourierInverse.inverse_accuracy xs ha)

theorem power_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (samples : Array Float) (h : EntryReady heap store params samples)
    (ha : FourierPowerSpec.Admissible samples) :
    Runs true env Fourier.compiled.module 23 store params.reverse
      (OutputPost (Fourier.powerSpectrum samples) (PowerOutput samples) heap store) :=
  power_entry_call_of_post env heap store params samples (PowerOutput samples) h
    (FourierPowerTheorem.powerSpectrum_accuracy samples ha)

private theorem decoded_module_eq (bytes : ByteArray) (module_ : Module)
    (henc : Encoding.encode Fourier.compiled.module = .ok bytes)
    (hdec : Encoding.decode bytes = .ok module_) : module_ = Fourier.compiled.module := by
  obtain ⟨encoded, henc', hdec', _⟩ := Fourier.compiled.bytes
  have hbytes : bytes = encoded := Except.ok.inj (henc.symm.trans henc')
  subst bytes
  exact Except.ok.inj (hdec.symm.trans hdec')

theorem inverse_decoded_accuracy (bytes : ByteArray) (module_ : Module)
    (henc : Encoding.encode Fourier.compiled.module = .ok bytes)
    (hdec : Encoding.decode bytes = .ok module_)
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (xs : Array Float) (h : EntryReady heap store params xs)
    (ha : FourierSpec.Admissible xs) :
    Runs true env module_ 22 store params.reverse
      (OutputPost (Fourier.inverse xs) (InverseOutput xs) heap store) := by
  rw [decoded_module_eq bytes module_ henc hdec]
  exact inverse_entry_call env heap store params xs h ha

theorem power_decoded_accuracy (bytes : ByteArray) (module_ : Module)
    (henc : Encoding.encode Fourier.compiled.module = .ok bytes)
    (hdec : Encoding.decode bytes = .ok module_)
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (params : List Value) (samples : Array Float) (h : EntryReady heap store params samples)
    (ha : FourierPowerSpec.Admissible samples) :
    Runs true env module_ 23 store params.reverse
      (OutputPost (Fourier.powerSpectrum samples) (PowerOutput samples) heap store) := by
  rw [decoded_module_eq bytes module_ henc hdec]
  exact power_entry_call env heap store params samples h ha

theorem inverse_bytes_accuracy :
    ∃ bytes, Encoding.encode Fourier.compiled.module = .ok bytes ∧
      Encoding.decode bytes = .ok Fourier.compiled.module ∧
      ({ name := "inverse", funcIdx := 22 } : Export) ∈ Fourier.compiled.module.exports ∧
      Ready (Verified.initialHeap Fourier.compiled.tables) Fourier.compiled.module.initialStore ∧
      ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
        (params : List Value) (xs : Array Float), EntryReady heap store params xs →
        FourierSpec.Admissible xs →
        Runs true env Fourier.compiled.module 22 store params.reverse
          (OutputPost (Fourier.inverse xs) (InverseOutput xs) heap store) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Fourier.compiled.bytes
  exact ⟨bytes, henc, hdec, inverse_export, ready_initial, inverse_entry_call⟩

theorem power_bytes_accuracy :
    ∃ bytes, Encoding.encode Fourier.compiled.module = .ok bytes ∧
      Encoding.decode bytes = .ok Fourier.compiled.module ∧
      ({ name := "powerSpectrum", funcIdx := 23 } : Export) ∈ Fourier.compiled.module.exports ∧
      Ready (Verified.initialHeap Fourier.compiled.tables) Fourier.compiled.module.initialStore ∧
      ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
        (params : List Value) (samples : Array Float), EntryReady heap store params samples →
        FourierPowerSpec.Admissible samples →
        Runs true env Fourier.compiled.module 23 store params.reverse
          (OutputPost (Fourier.powerSpectrum samples) (PowerOutput samples) heap store) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Fourier.compiled.bytes
  exact ⟨bytes, henc, hdec, power_export, ready_initial, power_entry_call⟩

theorem fourier_module_accuracy :
    (∃ bytes, Encoding.encode Fourier.compiled.module = .ok bytes ∧
      Encoding.decode bytes = .ok Fourier.compiled.module ∧
      ({ name := "dft", funcIdx := 21 } : Export) ∈ Fourier.compiled.module.exports ∧
      Ready (Verified.initialHeap Fourier.compiled.tables) Fourier.compiled.module.initialStore ∧
      ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
        (params : List Value) (xs : Array Float), EntryReady heap store params xs →
        FourierSpec.Admissible xs →
        Runs true env Fourier.compiled.module 21 store params.reverse
          (FourierBytes.ResultPost xs (AccurateOutput xs) heap store)) ∧
    (∃ bytes, Encoding.encode Fourier.compiled.module = .ok bytes ∧
      Encoding.decode bytes = .ok Fourier.compiled.module ∧
      ({ name := "inverse", funcIdx := 22 } : Export) ∈ Fourier.compiled.module.exports ∧
      Ready (Verified.initialHeap Fourier.compiled.tables) Fourier.compiled.module.initialStore ∧
      ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
        (params : List Value) (xs : Array Float), EntryReady heap store params xs →
        FourierSpec.Admissible xs →
        Runs true env Fourier.compiled.module 22 store params.reverse
          (OutputPost (Fourier.inverse xs) (InverseOutput xs) heap store)) ∧
    (∃ bytes, Encoding.encode Fourier.compiled.module = .ok bytes ∧
      Encoding.decode bytes = .ok Fourier.compiled.module ∧
      ({ name := "powerSpectrum", funcIdx := 23 } : Export) ∈ Fourier.compiled.module.exports ∧
      Ready (Verified.initialHeap Fourier.compiled.tables) Fourier.compiled.module.initialStore ∧
      ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
        (params : List Value) (samples : Array Float), EntryReady heap store params samples →
        FourierPowerSpec.Admissible samples →
        Runs true env Fourier.compiled.module 23 store params.reverse
          (OutputPost (Fourier.powerSpectrum samples) (PowerOutput samples) heap store)) :=
  ⟨dft_bytes_accuracy, inverse_bytes_accuracy, power_bytes_accuracy⟩

#print axioms inverse_entry_call_of_post
#print axioms power_entry_call_of_post
#print axioms inverse_export
#print axioms power_export
#print axioms inverse_entry_call
#print axioms power_entry_call
#print axioms inverse_decoded_accuracy
#print axioms power_decoded_accuracy
#print axioms inverse_bytes_accuracy
#print axioms power_bytes_accuracy
#print axioms fourier_module_accuracy

end Verified.Examples.FourierExtraBytes
