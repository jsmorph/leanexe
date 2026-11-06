import Lean
import LeanExe.A64.Image

/-!
The bytes of a file as a number, so that a theorem can name the bytes that a build wrote.
`file_nat% "PATH"` reads the file when it elaborates and gives `natOfBytes` of its bytes, the
number whose base-256 digits, the lowest first, are those bytes, and `file_size% "PATH"` gives the
file's length.  PATH is relative to the directory in which Lean runs.  The kernel compares such a
number with `natOfBytes` of the bytes that a function computes, so a theorem over the file's bytes
rests on the reading of the file and on the kernel, and the compiled code that wrote the file lies
outside it.  `of_file` turns a theorem about a memory that holds `imageBytes is`, for the `is`
that a generator returns, into one about a memory that holds the bytes of a file.
-/

namespace LeanExe.A64

/-- The number whose base-256 digits, the lowest first, are the bytes `l`. -/
def natOfBytes : List UInt8 → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * natOfBytes l

/-- Byte `j` of the number `n`, in the order of `natOfBytes`. -/
def byteAt (n j : Nat) : UInt8 := UInt8.ofNat (n / 256 ^ j % 256)

theorem byteAt_natOfBytes (l : List UInt8) (j : Nat) (hj : j < l.length) :
    byteAt (natOfBytes l) j = l[j] := by
  induction l generalizing j with
  | nil => simp at hj
  | cons b l ih =>
      have hb : b.toNat < 256 := b.toNat_lt
      cases j with
      | zero =>
          have h : natOfBytes (b :: l) / 256 ^ 0 % 256 = b.toNat := by
            show (b.toNat + 256 * natOfBytes l) / 256 ^ 0 % 256 = b.toNat
            rw [Nat.pow_zero, Nat.div_one]
            omega
          rw [List.getElem_cons_zero]
          unfold byteAt
          rw [h]
          simp
      | succ j =>
          rw [List.getElem_cons_succ, ← ih j (by simp at hj; omega)]
          have e : natOfBytes (b :: l) / 256 ^ (j + 1) = natOfBytes l / 256 ^ j := by
            rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
            congr 1
            show (b.toNat + 256 * natOfBytes l) / 256 = natOfBytes l
            omega
          unfold byteAt
          rw [e]

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

open Lean Elab Term in
/-- `natOfBytes` of the bytes of the file at the path, read when the term elaborates. -/
elab "file_nat% " path:str : term => do
  let b ← IO.FS.readBinFile path.getString
  return mkNatLit (natOfBytes b.toList)

open Lean Elab Term in
/-- The number of bytes of the file at the path, read when the term elaborates. -/
elab "file_size% " path:str : term => do
  let b ← IO.FS.readBinFile path.getString
  return mkNatLit b.size

end LeanExe.A64
