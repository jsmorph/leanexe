import Project.ProofKit.F32LogitCertificate
import LeanExe.Models.Gpt2.Kernel

namespace Project.ProofKit.PackedLogitCertificate
open CodeLib.IEEE32

def words (bytes : ByteArray) (count : Nat) : Array UInt32 :=
  Array.ofFn fun i : Fin count => LeanExe.Models.Gpt2.word bytes i

theorem words_get (bytes : ByteArray) (count i : Nat) (hi : i < count) :
    (words bytes count)[i]! = LeanExe.Models.Gpt2.word bytes i := by
  simp [words, getElem!_pos, hi]

def check (reference quantized : ByteArray) (count : Nat) (errors : Array Nat)
    (shift : Int) (winner : Nat) : Bool :=
  reference.size == count * 4 && quantized.size == count * 4 &&
    F32LogitCertificate.check (words reference count) (words quantized count) errors shift winner

theorem sound (reference quantized : ByteArray) (count : Nat) (errors : Array Nat)
    (shift : Int) (winner : Nat) (h : check reference quantized count errors shift winner = true) :
    reference.size = count * 4 ∧ quantized.size = count * 4 ∧ winner < count ∧
      (∀ i < count, |value (LeanExe.Models.Gpt2.word quantized i) -
        (shift : ℝ) / 2 ^ 149 - value (LeanExe.Models.Gpt2.word reference i)| ≤ F32LogitCertificate.realError errors[i]!) ∧
      (∀ i < count, i ≠ winner → value (LeanExe.Models.Gpt2.word quantized winner) >
        value (LeanExe.Models.Gpt2.word quantized i)) := by
  simp only [check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hWinner, _, hError, hUnique⟩ := F32LogitCertificate.sound _ _ errors shift winner h.2
  have hSize (bytes : ByteArray) : (words bytes count).size = count := Array.size_ofFn
  rw [hSize] at hWinner hError hUnique
  refine ⟨h.1.1, h.1.2, hWinner, ?_, ?_⟩
  · intro i hi
    simpa only [words_get reference count i hi, words_get quantized count i hi] using hError i hi
  · intro i hi hNe
    simpa only [words_get quantized count i hi, words_get quantized count winner hWinner] using hUnique i hi hNe

#print axioms words_get
#print axioms sound
end Project.ProofKit.PackedLogitCertificate
