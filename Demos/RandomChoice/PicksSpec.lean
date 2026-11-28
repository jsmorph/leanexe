module

public import Demos.RandomChoice.Spec

@[expose] public section

/-! The specification of `putPicks`, a function of the WASI command `choose N K` of the request in
`Demos/RandomChoice/request.txt`.  The command draws random words into a buffer, one draw at a
time, and calls `putPicks` once for each draw with the buffer `out` that it reuses for its output,
N as `n`, the bytes of the draw as `draw`, and the number of values still to choose as `limit`.
`putPicksSpec (out, n, draw, limit)` is `out` with the lines of the values that the draw gives
written into it, the number of bytes of those lines, and the number of values.  The command fills
the whole draw buffer, 4,096 bytes, at each call of `random_get`, so every word of `draw` comes
from the draw, and its `out` of 10,752 bytes holds the lines of 512 values of at most 20 digits,
so the lines of a draw always fit.

The request fixes the reading of a word, its acceptance, and its value, which `accepts` and
`pickSpec` state, and the lines, which `renderSpec` states.  This specification records the choices
that the request leaves open:

- The words of `draw` are its 64-bit little-endian words: word `j` is the value of bytes `8 j` to
  `8 j + 7`, the first byte the least significant.  Bytes after the last whole word give no word.
- The values are those that `pickSpec (n, w)` gives for the words `w` that `accepts n w` accepts,
  in the order of the words, and at most `limit` of them: the first `limit` when more words are
  accepted.  A rejected word gives no value, and N = 0 accepts no word, as `accepts` states.
- The lines replace the bytes of `out` from position 0, the bytes of `out` after the lines keep
  their values, and the result has the size of `out`: when the lines are longer than `out`, their
  bytes past its end are dropped, possibly in the middle of a line.
- The second component is the number of bytes of the lines, those dropped included, and the third
  the number of values, those whose lines were dropped included, each reduced modulo `2^64`. -/

namespace Demos.RandomChoice

open LeanExe

/-- The value of the little-endian bytes `bs`, the first the least significant. -/
def littleEndian (bs : List UInt8) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The 64-bit little-endian words of `bytes`: word `j` is the value of bytes `8 j` to `8 j + 7`.
Bytes after the last whole word give no word. -/
def wordsOf (bytes : List UInt8) : List UInt64 :=
  (List.range (bytes.length / 8)).map fun j =>
    UInt64.ofNat (littleEndian ((bytes.drop (8 * j)).take 8))

/-- The values in [1, n] that the words `ws` give, in order: `pickSpec (n, w)` of each word `w`
that `n` accepts. -/
def valuesOf (n : UInt64) (ws : List UInt64) : List UInt64 :=
  (ws.filter fun w => accepts n w).map fun w => pickSpec (n, w)

/-- For `input = (out, n, draw, limit)`: `out` with its bytes from position 0 replaced by the lines
of the first `limit` values that the words of `draw` give, its size kept, the number of bytes of
those lines, and the number of values. -/
def putPicksSpec (input : Bytes × UInt64 × Bytes × UInt64) : Bytes × UInt64 × UInt64 :=
  let values := (valuesOf input.2.1 (wordsOf input.2.2.1.data.data.toList)).take input.2.2.2.toNat
  let text := (renderSpec values.toArray).data.data.toList
  let out := input.1.data.data.toList
  (⟨⟨(text.take out.length ++ out.drop text.length).toArray⟩⟩, UInt64.ofNat text.length,
    UInt64.ofNat values.length)

end Demos.RandomChoice
