module

public import Library.Numerics.Bignum.Inverse
import all Init.Data.Repr
import all Init.Data.Int.Repr

@[expose] public section

/-!
# The calculator's messages and lines

The bare-metal program and the AArch64 Image read one message of bytes and write one line of
bytes.  A message names an operation and gives its operands, separated by single spaces (32):
`neg a`, or `name a b` for `name` one of `cmp`, `add`, `sub`, `mul`, `tdiv`, `tmod`, `ediv`, and
`emod`.  An operand is a text of the library's grammar `"0" / ["-"] nonzero *digit`, `operand`.
`calcSpec m` is the line for the message `m`.  For a message of at most `msgMax`, 65,536 bytes,
that names an operation on operands of the grammar, it is `0`, a space, and Lean's decimal text of
the exact result: `-a` for `neg`, the sign of `a - b`, `-1`, `0`, or `1`, for `cmp`, `a + b`,
`a - b`, and `a * b`, the truncated quotient and remainder `Int.tdiv` and `Int.tmod` for `tdiv` and
`tmod`, and Lean's Euclidean `/` and `%` for `ediv` and `emod`.  Otherwise it is one digit: `1` or
`2` when the first or the second operand is outside the grammar, `3` for a division by zero, and
`4` for a longer message, a name of no operation, or wrong separators: a number of spaces other
than the operation's, or an empty part, from a leading, a trailing, or a doubled space.

`calcSpec` splits the message with `List.splitOn` at each space, so an operand that holds a space
makes the number of parts wrong, and a leading, a trailing, or a doubled space, as in `add  1` or
`add 1 `, leaves an empty part; both give the line `4`.  No line holds the byte 0
(`zero_not_mem_calcSpec`).  `calcSpec_unary`, `calcSpec_binary`, and
`calcSpec_zero_divisor` state the line for a message written as the operation's name and Lean's
texts of integers.
-/

namespace Demos.BignumCalc

open Library.Numerics.Bignum

open Library.Numerics.Decimal.Shared.StrconvGrammar (ascii words)
open Library.Numerics.Decimal.Int64Text (denote)

/-- The longest message that the programs answer, in bytes. -/
def msgMax : ℕ := 65536

/-- The integer of an operand's bytes in the grammar `"0" / ["-"] nonzero *digit`, or `none`. -/
def operand (b : List UInt8) : Option ℤ := denote (b.map UInt8.toUInt64)

/-- The line of an error status: its decimal digit. -/
def errLine (s : ℕ) : List UInt8 := ascii (toString s)

/-- The line of a result: `0`, a space, and Lean's decimal text of `z`. -/
def okLine (z : ℤ) : List UInt8 := ascii ("0 " ++ toString z)

/-- The line of a unary operation `f` on the operand `a`. -/
def unaryLine (f : ℤ → ℤ) (a : List UInt8) : List UInt8 :=
  match operand a with
  | none => errLine 1
  | some x => okLine (f x)

/-- The line of a binary operation `f` on the operands `a` and `b`, with the status 3 for a zero
divisor when `division` holds. -/
def binaryLine (division : Bool) (f : ℤ → ℤ → ℤ) (a b : List UInt8) : List UInt8 :=
  match operand a with
  | none => errLine 1
  | some x =>
    match operand b with
    | none => errLine 2
    | some y => if division = true ∧ y = 0 then errLine 3 else okLine (f x y)

/-- The binary operations: each name, whether it divides, and its function. -/
def binaryOps : List (String × Bool × (ℤ → ℤ → ℤ)) :=
  [("cmp", false, fun x y => (x - y).sign), ("add", false, (· + ·)), ("sub", false, (· - ·)),
    ("mul", false, (· * ·)), ("tdiv", true, Int.tdiv), ("tmod", true, Int.tmod),
    ("ediv", true, (· / ·)), ("emod", true, (· % ·))]

/-- The line of the message `m`. -/
def calcSpec (m : List UInt8) : List UInt8 :=
  if msgMax < m.length then errLine 4
  else if [] ∈ m.splitOn 32 then errLine 4
  else
    match m.splitOn 32 with
    | [name, a] => if name = ascii "neg" then unaryLine (fun x => -x) a else errLine 4
    | [name, a, b] =>
      if name = ascii "cmp" then binaryLine false (fun x y => (x - y).sign) a b
      else if name = ascii "add" then binaryLine false (· + ·) a b
      else if name = ascii "sub" then binaryLine false (· - ·) a b
      else if name = ascii "mul" then binaryLine false (· * ·) a b
      else if name = ascii "tdiv" then binaryLine true Int.tdiv a b
      else if name = ascii "tmod" then binaryLine true Int.tmod a b
      else if name = ascii "ediv" then binaryLine true (· / ·) a b
      else if name = ascii "emod" then binaryLine true (· % ·) a b
      else errLine 4
    | _ => errLine 4

/-! ## Messages written as texts of integers -/

theorem words_size_eq (l : List UInt8) : (words l).size = l.length := by simp [words]

theorem ascii_append (s t : String) : ascii (s ++ t) = ascii s ++ ascii t := by
  simp [ascii, String.toList_append]

/-- Lean's text of an integer holds only `-` and the digits. -/
theorem byte_not_mem_toString (z : ℤ) (c : UInt8) (h45 : c ≠ 45) (hd : c.toNat < 48 ∨ 57 < c.toNat) :
    c ∉ ascii (toString z) := by
  intro h
  have hw : c.toUInt64 ∈ (printSpec z).toList := by
    have : (printSpec z).toList = (ascii (toString z)).map UInt8.toUInt64 := by
      simp [printSpec, words]
    rw [this]
    exact List.mem_map.mpr ⟨c, h, rfl⟩
  rw [printSpec_toList] at hw
  rcases List.mem_append.mp hw with h1 | h2
  · split at h1
    · simp only [List.mem_singleton] at h1
      exact h45 (UInt8.toUInt64_inj.mp (by rw [h1]; rfl))
    · simp at h1
  · obtain ⟨hdig, -⟩ := Library.Numerics.Decimal.Int64Text.digitWords_facts z.natAbs
    have := (Library.Numerics.Decimal.Int64Text.isDigitWord_iff _).mp (hdig _ h2)
    rw [UInt8.toNat_toUInt64] at this
    omega

/-- Lean's text of an integer holds no space. -/
theorem space_not_mem_toString (z : ℤ) : (32 : UInt8) ∉ ascii (toString z) :=
  byte_not_mem_toString z 32 (by decide) (by decide)

/-- The grammar reads Lean's text of an integer as the integer. -/
theorem operand_toString (z : ℤ) : operand (ascii (toString z)) = some z := by
  have : (ascii (toString z)).map UInt8.toUInt64 = (printSpec z).toList := by
    simp [printSpec, words]
  rw [operand, this, denote_print]

/-- Lean's text of an integer is not empty. -/
theorem nil_ne_toString (z : ℤ) : [] ≠ ascii (toString z) := by
  intro h
  have hs : (printSpec z).size = 0 := by rw [printSpec, words_size_eq, ← h]; rfl
  rw [printSpec_size] at hs
  obtain ⟨-, -, d, rest, hdr, -⟩ := Library.Numerics.Decimal.Int64Text.digitWords_facts z.natAbs
  rw [hdr, List.length_cons] at hs
  omega

theorem nil_not_mem2 {a b : List UInt8} (ha : [] ≠ a) (hb : [] ≠ b) : [] ∉ [a, b] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
  exact ⟨ha, hb⟩

theorem nil_not_mem3 {a b c : List UInt8} (ha : [] ≠ a) (hb : [] ≠ b) (hc : [] ≠ c) :
    [] ∉ [a, b, c] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
  exact ⟨ha, hb, hc⟩

theorem splitOn_three {name a b : List UInt8} (hn : (32 : UInt8) ∉ name) (ha : (32 : UInt8) ∉ a)
    (hb : (32 : UInt8) ∉ b) : (name ++ 32 :: (a ++ 32 :: b)).splitOn 32 = [name, a, b] := by
  rw [List.splitOn_append_cons_self_of_not_mem hn, List.splitOn_append_cons_self_of_not_mem ha,
    List.splitOn_eq_singleton hb]

theorem splitOn_two {name a : List UInt8} (hn : (32 : UInt8) ∉ name) (ha : (32 : UInt8) ∉ a) :
    (name ++ 32 :: a).splitOn 32 = [name, a] := by
  rw [List.splitOn_append_cons_self_of_not_mem hn, List.splitOn_eq_singleton ha]

/-- The message `neg a`, for Lean's text of an integer `a`, of at most `msgMax` bytes, gives the
line `0`, a space, and the text of `-a`. -/
theorem calcSpec_unary (x : ℤ) (hlen : (ascii ("neg " ++ toString x)).length ≤ msgMax) :
    calcSpec (ascii ("neg " ++ toString x)) = ascii ("0 " ++ toString (-x)) := by
  have hm : ascii ("neg " ++ toString x) = ascii "neg" ++ 32 :: ascii (toString x) := by
    rw [ascii_append]; rfl
  unfold calcSpec
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), hm,
    splitOn_two (by decide) (space_not_mem_toString x),
    ite_eq_right_iff.mpr (fun h => absurd h (nil_not_mem2 (by decide) (nil_ne_toString x)))]
  simp only [ite_true, unaryLine, operand_toString, okLine]

/-- The message `name a b`, for a binary operation's name and Lean's texts of integers `a` and `b`,
of at most `msgMax` bytes, gives the line `0`, a space, and the text of the operation's exact
result, unless the operation divides and `b` is 0. -/
theorem calcSpec_binary (name : String) (division : Bool) (f : ℤ → ℤ → ℤ)
    (hop : (name, division, f) ∈ binaryOps) (x y : ℤ) (hdiv : ¬ (division = true ∧ y = 0))
    (hlen : (ascii (name ++ " " ++ toString x ++ " " ++ toString y)).length ≤ msgMax) :
    calcSpec (ascii (name ++ " " ++ toString x ++ " " ++ toString y)) =
      ascii ("0 " ++ toString (f x y)) := by
  have hm : ascii (name ++ " " ++ toString x ++ " " ++ toString y) =
      ascii name ++ 32 :: (ascii (toString x) ++ 32 :: ascii (toString y)) := by
    simp only [ascii_append]
    simp [ascii]
    decide
  unfold calcSpec
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), hm]
  simp only [binaryOps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hop
  rcases hop with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rw [splitOn_three (by decide) (space_not_mem_toString x) (space_not_mem_toString y),
      ite_eq_right_iff.mpr (fun h => absurd h
        (nil_not_mem3 (by decide) (nil_ne_toString x) (nil_ne_toString y)))] <;>
    simp (config := { decide := true }) only [binaryLine, operand_toString, okLine, ite_true,
      ite_false, false_and] <;> simp_all

/-- The message `name a b`, for a division's name, Lean's text of an integer `a`, and the text
`0`, of at most `msgMax` bytes, gives the line `3`. -/
theorem calcSpec_zero_divisor (name : String) (f : ℤ → ℤ → ℤ) (hop : (name, true, f) ∈ binaryOps)
    (x : ℤ) (hlen : (ascii (name ++ " " ++ toString x ++ " 0")).length ≤ msgMax) :
    calcSpec (ascii (name ++ " " ++ toString x ++ " 0")) = ascii "3" := by
  have hm : ascii (name ++ " " ++ toString x ++ " 0") =
      ascii name ++ 32 :: (ascii (toString x) ++ 32 :: ascii (toString (0 : ℤ))) := by
    simp only [ascii_append]
    simp [ascii]
    decide
  unfold calcSpec
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), hm]
  simp only [binaryOps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hop
  rcases hop with ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩ |
      ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ <;>
    first
    | exact absurd h (by decide)
    | (rw [splitOn_three (by decide) (space_not_mem_toString x) (space_not_mem_toString 0),
         ite_eq_right_iff.mpr (fun h => absurd h
           (nil_not_mem3 (by decide) (nil_ne_toString x) (nil_ne_toString 0)))]
       simp (config := { decide := true }) only [binaryLine, operand_toString, ite_true, ite_false])

/-! ## Lines hold no zero byte -/

theorem zero_not_mem_errLine {k : ℕ} (hk : k < 10) : (0 : UInt8) ∉ errLine k := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 by
    omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem zero_not_mem_okLine (z : ℤ) : (0 : UInt8) ∉ okLine z := by
  rw [okLine, ascii_append, List.mem_append, not_or]
  exact ⟨by decide, byte_not_mem_toString z 0 (by decide) (by decide)⟩

theorem zero_not_mem_unaryLine (f : ℤ → ℤ) (a : List UInt8) : (0 : UInt8) ∉ unaryLine f a := by
  unfold unaryLine
  split
  · exact zero_not_mem_errLine (by norm_num)
  · exact zero_not_mem_okLine _

theorem zero_not_mem_binaryLine (d : Bool) (f : ℤ → ℤ → ℤ) (a b : List UInt8) :
    (0 : UInt8) ∉ binaryLine d f a b := by
  unfold binaryLine
  split
  · exact zero_not_mem_errLine (by norm_num)
  · split
    · exact zero_not_mem_errLine (by norm_num)
    · split
      · exact zero_not_mem_errLine (by norm_num)
      · exact zero_not_mem_okLine _

/-- No line holds the byte 0, so a line followed by zeros determines the line. -/
theorem zero_not_mem_calcSpec (m : List UInt8) : (0 : UInt8) ∉ calcSpec m := by
  unfold calcSpec
  split
  · exact zero_not_mem_errLine (by norm_num)
  split
  · exact zero_not_mem_errLine (by norm_num)
  · split
    · split
      · exact zero_not_mem_unaryLine _ _
      · exact zero_not_mem_errLine (by norm_num)
    · split_ifs <;> first
        | exact zero_not_mem_binaryLine _ _ _ _
        | exact zero_not_mem_errLine (by norm_num)
    · exact zero_not_mem_errLine (by norm_num)

end Demos.BignumCalc
