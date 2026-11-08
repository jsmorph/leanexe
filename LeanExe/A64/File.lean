import LeanExe.FileNat
import LeanExe.A64.Image

/-!
The comparison of the AArch64 back end's code with the bytes of a file, which `file_nat%` and
`file_size%` of `LeanExe/FileNat.lean` read when a theorem elaborates.  `fileOk` compares
`natOfBytes` of the code's bytes with the file's number, and `of_file` turns a theorem about a
memory that holds `imageBytes is`, for the `is` that a generator returns, into one about a memory
that holds the bytes of a file.
-/

namespace LeanExe.A64

export LeanExe.FileNat (natOfBytes byteAt byteAt_natOfBytes natOfBytesPaired natOfBytesPaired_eq)

/-- The generator's result `g` is code whose bytes have the number `n` and the length `len`. -/
def fileOk (g : Except String (List Instr)) (n len : Nat) : Bool :=
  match g with
  | .ok is => natOfBytes (imageBytes is) == n && (imageBytes is).length == len
  | .error _ => false

/-- A theorem `hthm` about a memory `m` that holds, from `a`, the bytes of the code that the
generator's result `g` gives holds of that code when `m` holds, from `a`, the `len` bytes of the
number `n`, and the kernel's check `hk` finds those bytes to be the code's. -/
theorem of_file {g : Except String (List Instr)} {n len : Nat} (hk : fileOk g n len = true)
    {m : UInt64 → UInt8} {a : UInt64} (h : ∀ j < len, m (a + UInt64.ofNat j) = byteAt n j)
    {C : List Instr → Prop}
    (hthm : ∀ is, g = .ok is → (∀ j (hj : j < (imageBytes is).length),
      m (a + UInt64.ofNat j) = (imageBytes is)[j]) → C is) :
    ∃ is, 4 * is.length = len ∧ C is := by
  cases hg : g with
  | error e => rw [hg] at hk; cases hk
  | ok is =>
      rw [hg] at hk
      simp only [fileOk, Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨hn, hl⟩ := hk
      refine ⟨is, by rw [← hl, length_imageBytes], hthm is hg fun j hj => ?_⟩
      rw [h j (hl ▸ hj), ← hn, byteAt_natOfBytes]

/-- The generator's result `g` holds bytes with the number `n` and the length `len`.  The number
of the bytes is `natOfBytesPaired`, which equals `natOfBytes` and which the kernel evaluates in
memory about linear in the number of bytes. -/
def bytesOk {α : Type} (g : Except String (List UInt8 × α)) (n len : Nat) : Bool :=
  match g with
  | .ok (bytes, _) => natOfBytesPaired bytes == n && bytes.length == len
  | .error _ => false

/-- When the kernel's check `hk` passes, the generator's bytes are the `len` bytes of the number
`n`, byte by byte. -/
theorem of_bytesOk {α : Type} {g : Except String (List UInt8 × α)} {n len : Nat}
    (hk : bytesOk g n len = true) :
    ∃ bytes x, g = .ok (bytes, x) ∧ bytes.length = len ∧
      ∀ j (hj : j < bytes.length), byteAt n j = bytes[j] := by
  cases hg : g with
  | error e => rw [hg] at hk; cases hk
  | ok r =>
      obtain ⟨bytes, x⟩ := r
      rw [hg] at hk
      simp only [bytesOk, Bool.and_eq_true, beq_iff_eq, natOfBytesPaired_eq] at hk
      obtain ⟨hn, hl⟩ := hk
      exact ⟨bytes, x, rfl, hl, fun j hj => by rw [← hn, byteAt_natOfBytes]⟩

end LeanExe.A64
