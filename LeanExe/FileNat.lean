import Lean

/-!
The bytes of a file as a number, so that a theorem can name the bytes that a build wrote.
`file_nat% "PATH"` reads the file when it elaborates and gives `natOfBytes` of its bytes, the
number whose base-256 digits, the lowest first, are those bytes, and `file_size% "PATH"` gives the
file's length.  PATH is relative to the directory in which Lean runs.  The kernel compares such a
number with `natOfBytes` of the bytes that a function computes, or with `natOfBytesPaired`, which
equals it, so a theorem over the file's bytes depends on the reading of the file and on the kernel,
and the compiled code that wrote the file lies outside it.  The AArch64 and Cortex-M7 back ends
share these definitions.
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

/-- The number whose base-`b` digits, the lowest first, are `l`. -/
def digitsVal (b : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => x + b * digitsVal b l

/-- The digits of base `b * b` that the adjacent pairs of the base-`b` digits `l` form, the lowest
first. -/
def pairDigits (b : Nat) : List Nat → List Nat
  | x :: y :: l => (x + b * y) :: pairDigits b l
  | l => l

/-- `digitsVal b l` after at most `fuel` rounds of `pairDigits`, each of which halves the list and
squares the base. -/
def pairVal : Nat → Nat → List Nat → Nat
  | 0, b, l => digitsVal b l
  | _ + 1, _, [] => 0
  | _ + 1, _, [x] => x
  | fuel + 1, b, l => pairVal fuel (b * b) (pairDigits b l)

/-- `natOfBytes l`, computed by rounds of `pairDigits` from the bytes.  The kernel's evaluation of
`natOfBytes` forms the number of every suffix of `l` and keeps each, which for `n` bytes takes
memory in proportion to `n ^ 2`.  That of `natOfBytesPaired` forms numbers of about `n` bytes in
all in each of about `log₂ n` rounds. -/
def natOfBytesPaired (l : List UInt8) : Nat :=
  pairVal 64 256 (l.map UInt8.toNat)

theorem digitsVal_pairDigits (b : Nat) :
    ∀ l, digitsVal (b * b) (pairDigits b l) = digitsVal b l
  | [] => rfl
  | [x] => by simp [pairDigits, digitsVal]
  | x :: y :: l => by
      rw [pairDigits, digitsVal, digitsVal_pairDigits b l, digitsVal, digitsVal, Nat.mul_add,
        Nat.mul_assoc, Nat.add_assoc]

theorem pairVal_eq : ∀ fuel b l, pairVal fuel b l = digitsVal b l
  | 0, _, _ => by rw [pairVal]
  | _ + 1, _, [] => by rw [pairVal, digitsVal]
  | _ + 1, _, [x] => by simp [pairVal, digitsVal]
  | fuel + 1, b, x :: y :: l => by
      rw [pairVal, pairVal_eq fuel, digitsVal_pairDigits]
      · simp
      · simp

theorem natOfBytes_digitsVal : ∀ l, natOfBytes l = digitsVal 256 (l.map UInt8.toNat)
  | [] => rfl
  | b :: l => by rw [natOfBytes, List.map_cons, digitsVal, natOfBytes_digitsVal l]

theorem natOfBytesPaired_eq (l : List UInt8) : natOfBytesPaired l = natOfBytes l := by
  rw [natOfBytesPaired, pairVal_eq, natOfBytes_digitsVal]

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
