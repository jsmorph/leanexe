module

public import LeanExe.Dialect.Bytes

@[expose] public section

/-! The specifications of the pure core of the request in `Demos/RandomChoice/request.txt`:
`parseSpec`, the value of an argument of the command line, `pickSpec`, the integer in [1, N] that a
random word gives or the word's rejection, and `renderSpec`, the lines of the output.

Decisions the request leaves to the specifications:

- The arguments reach the program as the buffer that WASI's `args_get` fills: each argument, the
  program name first, followed by a zero byte.  Argument `i` is the bytes between zero bytes `i`
  and `i + 1` of the buffer, counted from 1, and argument 0, the program name, the bytes before the
  first zero byte.  An argument that no zero byte ends is missing, and `parseSpec` refuses a
  missing argument.  The command's specification reads N as argument 1 and K as argument 2, so the
  command ignores the program name's bytes and the arguments after K.
- "Decimal" admits the bytes 48 to 57, `0` to `9`, and at least one of them, so an empty argument,
  a sign, a space, and every byte outside that range, the bytes of a digit outside ASCII among
  them, are refused.  Leading zeros are digits, so `007` gives 7 and `000` gives 0, which is
  refused.  A numeral may have any number of digits, and the range test applies to its value, so
  `0018446744073709551615` gives 2^64 - 1 and `018446744073709551616` is refused.
- `parseSpec` returns a word, and 0 marks a refusal, since neither N nor K may be 0.
- A random word is read as an unsigned integer.  For N ≥ 1, `pickSpec` accepts a word `w` when
  `w ≥ 2^64 mod N` and gives `(w mod N) + 1`.  For N = 0 the range [1, 0] holds no integer, and
  `pickSpec` accepts no word.  A rejected word gives 0, which no value in [1, N] equals.
- `renderSpec` writes one line for each element of its argument, in order.  A value is written as
  Lean's `toString` of the natural number writes it: its decimal digits, most significant first,
  with no leading zero, and `0` for zero.  The newline is the byte 10.  An empty array gives no
  bytes. -/

namespace Demos.RandomChoice

open LeanExe

/-- Argument `i` of `buffer`, in which each argument is followed by a zero byte: the bytes between
zero bytes `i` and `i + 1`, counted from 1, the bytes before the first zero byte for `i = 0`, or
`none` when `buffer` has at most `i` zero bytes. -/
def argument (buffer : List UInt8) (i : Nat) : Option (List UInt8) :=
  let parts := buffer.splitOn 0
  if i + 1 < parts.length then parts[i]? else none

/-- The value of `text` as a decimal numeral, when `text` has at least one byte and every byte is a
digit, `0` (48) to `9` (57), and `none` otherwise. -/
def decimal (text : List UInt8) : Option Nat :=
  if text ≠ [] ∧ ∀ b ∈ text, 48 ≤ b ∧ b ≤ 57 then
    some (text.foldl (fun value b => 10 * value + (b.toNat - 48)) 0)
  else none

/-- The value of argument `input.2` of the argument buffer `input.1` when that argument is a
decimal numeral whose value lies in [1, 2^64), and 0, a refusal, otherwise. -/
def parseSpec (input : Bytes × UInt64) : UInt64 :=
  match argument input.1.data.data.toList input.2.toNat >>= decimal with
  | some n => if 1 ≤ n ∧ n < 2 ^ 64 then UInt64.ofNat n else 0
  | none => 0

/-- Whether the word `w` is accepted for the range [1, n]: `n ≥ 1` and `w ≥ 2^64 mod n`. -/
def accepts (n w : UInt64) : Bool := n != 0 && decide (2 ^ 64 % n.toNat ≤ w.toNat)

/-- The value in [1, n] that the word `w` gives, `(w mod n) + 1`, when `n` accepts `w`, and 0 when
it rejects `w`, for `input = (n, w)`. -/
def pickSpec (input : UInt64 × UInt64) : UInt64 :=
  if accepts input.1 input.2 then UInt64.ofNat (input.2.toNat % input.1.toNat + 1) else 0

/-- The lines of `values`: for each element in order, its decimal digits followed by a newline. -/
def renderSpec (values : Array UInt64) : Bytes :=
  ⟨⟨(values.toList.flatMap fun v =>
      (toString v.toNat).toList.map (fun c => c.toNat.toUInt8) ++ [10]).toArray⟩⟩

end Demos.RandomChoice
