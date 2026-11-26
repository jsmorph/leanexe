module

public import LeanExe.Dialect.Bytes

@[expose] public section

/-! The specifications of the pure core of the request in `Demos/RandomHistogram/request.txt`:
`parseSpec`, the number N that the command line gives, `histogramSpec`, the counts of the residues
mod 10 of a sequence of words, and `renderSpec`, the ten lines of the output.

Decisions the request leaves to the specifications:

- The arguments reach the program as the buffer that WASI's `args_get` fills: each argument, the
  program name first, followed by a zero byte.  N is read from that buffer, so the argument is the
  bytes between the buffer's first and second zero bytes.  A buffer with fewer than two zero bytes
  has no argument after the program name, which the request calls a missing argument.  The program
  name's bytes and the arguments after the first one are ignored.
- "Decimal digits only" admits the bytes 48 to 57, `0` to `9`, and at least one of them, so an
  empty argument, a sign, a space, and every byte outside that range, the bytes of a digit outside
  ASCII among them, are refused.  Leading zeros are digits, so `007` gives 7 and `000` gives 0,
  which is refused.  A numeral may have any number of digits, and the range test applies to its
  value, so `0018446744073709551615` gives 2^64 - 1 and `018446744073709551616` is refused.
- `parseSpec` returns a word, and 0 marks a refusal, since no valid N is 0.
- A random number is a word read as an unsigned integer, so the residue of `w` mod 10 is
  `w.toNat % 10`.
- A count is a word, so `histogramSpec` of an array of 2^64 or more words would wrap.  The
  command counts N words, and N is below 2^64, so its counts never wrap.
- `renderSpec` writes ten lines from the first ten elements of its argument, an element past the
  end of a shorter array reading as 0, so its output always has ten lines.  A count is written as
  Lean's `toString` of the natural number writes it: its decimal digits, most significant first,
  with no leading zero, and `0` for zero.  The newline is the byte 10. -/

namespace Demos.RandomHistogram

open LeanExe

/-- The first argument after the program name in `buffer`, in which each argument is followed by a
zero byte: the bytes between the first and the second zero byte, or `none` when `buffer` has fewer
than two zero bytes. -/
def argument (buffer : List UInt8) : Option (List UInt8) :=
  match buffer.splitOn 0 with
  | _ :: arg :: _ :: _ => some arg
  | _ => none

/-- The value of `text` as a decimal numeral, when `text` has at least one byte and every byte is a
digit, `0` (48) to `9` (57), and `none` otherwise. -/
def decimal (text : List UInt8) : Option Nat :=
  if text ≠ [] ∧ ∀ b ∈ text, 48 ≤ b ∧ b ≤ 57 then
    some (text.foldl (fun value b => 10 * value + (b.toNat - 48)) 0)
  else none

/-- N from the argument buffer `buffer`: the value of the first argument after the program name
when that argument is a decimal numeral whose value lies in [1, 2^64), and 0, a refusal, otherwise. -/
def parseSpec (buffer : Bytes) : UInt64 :=
  match argument buffer.data.data.toList >>= decimal with
  | some n => if 1 ≤ n ∧ n < 2 ^ 64 then UInt64.ofNat n else 0
  | none => 0

/-- The counts of the words of `ws` by their residue mod 10: element `m`, for `m` from 0 to 9, is
the number of words `w` of `ws` with `w mod 10 = m`. -/
def histogramSpec (ws : Array UInt64) : Array UInt64 :=
  Array.ofFn fun (m : Fin 10) => UInt64.ofNat (ws.toList.countP fun w => w.toNat % 10 = m.val)

/-- The ten lines of `counts`: for `m` from 0 to 9, the decimal digits of element `m` of `counts`, 0
past its end, followed by a newline. -/
def renderSpec (counts : Array UInt64) : Bytes :=
  ⟨⟨((List.range 10).flatMap fun m =>
      (toString (counts.getD m 0).toNat).toList.map (fun c => c.toNat.toUInt8) ++ [10]).toArray⟩⟩

end Demos.RandomHistogram
