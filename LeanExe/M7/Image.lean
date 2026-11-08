import LeanExe.FileNat
import LeanExe.M7.Gen

/-!
The bytes of generated Thumb-2 code.  `imageBytes` lays out each instruction's halfwords, the first
at the lower address, each with its low byte first, the order in which the processor fetches them
(DDI 0403E.e section A3.3.1).  `fileOk` compares those bytes with the number that `file_nat%` of
`LeanExe/FileNat.lean` reads from a file, so that the kernel's evaluation of the generator checks
the file that the board's flash receives.  The check forms the number of the bytes with
`natOfBytesPaired`, which equals `natOfBytes` and which the kernel evaluates without forming the
number of every suffix of the bytes, and `fileOk_ok` states its result with `natOfBytes`.
-/

namespace LeanExe.M7

/-- The two bytes of a halfword, the low byte first. -/
def halfBytes (h : UInt16) : List UInt8 := [h.toUInt8, (h >>> 8).toUInt8]

/-- The bytes of the instructions `is`. -/
def imageBytes (is : List Instr) : List UInt8 :=
  is.flatMap fun i => (encode i).flatMap halfBytes

/-- The generator's result `g` is code whose bytes have the number `n` and the length `len`. -/
def fileOk (g : Except String (List Instr)) (n len : Nat) : Bool :=
  match g with
  | .ok is =>
      LeanExe.FileNat.natOfBytesPaired (imageBytes is) == n && (imageBytes is).length == len
  | .error _ => false

theorem fileOk_ok {g : Except String (List Instr)} {n len : Nat} (h : fileOk g n len = true) :
    ∃ is, g = .ok is ∧ LeanExe.FileNat.natOfBytes (imageBytes is) = n ∧
      (imageBytes is).length = len := by
  unfold fileOk at h
  split at h
  · rename_i is
    simp only [Bool.and_eq_true, beq_iff_eq, LeanExe.FileNat.natOfBytesPaired_eq] at h
    exact ⟨is, rfl, h.1, h.2⟩
  · cases h

end LeanExe.M7
