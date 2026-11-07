import Lean

/-!
The bytes of a file as a number, so that a theorem can name the bytes that a build wrote.
`file_nat% "PATH"` reads the file when it elaborates and gives `natOfBytes` of its bytes, the
number whose base-256 digits, the lowest first, are those bytes, and `file_size% "PATH"` gives the
file's length.  PATH is relative to the directory in which Lean runs.  The kernel compares such a
number with `natOfBytes` of the bytes that a function computes, so a theorem over the file's bytes
rests on the reading of the file and on the kernel, and the compiled code that wrote the file lies
outside it.  The AArch64 and Cortex-M7 back ends share these definitions.
-/

namespace LeanExe.FileNat

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

end LeanExe.FileNat
