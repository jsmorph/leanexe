import Library.Regex.Program
import TestSupport.Regex.Generate

/-! The cases of the module `regex`: random pattern trees against short inputs, word sequences
that do not decode, patterns of 62 to 65 sets, counts that exceed their arrays, whose missing
words read as zero, and a long input.  The expected code is native `matchWith`, which
`Library.Regex.Proof.matchWith_eq` equates with `Library.Regex.Spec.answer`.  Each case requires
two retained blocks, the host's pattern and input, and at most seven allocations with the host's
two: the scan's stack, follow table, and sets, updated in place at every word, and the tables of
`steps` and `masks`, which a call that returns 2 or 3 does not build. -/

namespace TestSupport.Regex.Cases

open Library.Regex TestSupport.Regex.Generate

def arg (xs : Array UInt64) : String :=
  "array-u64:" ++ ",".intercalate (xs.toList.map toString)

/-- A case of the pattern words `pat` read to `pn` and the input words `msg` read to `n` bytes. -/
def emitWords (pat : Array UInt64) (pn : Nat) (msg : Array UInt64) (n : Nat) : IO Unit :=
  let code := matchWith pat pn.toUInt64 msg n.toUInt64
  let allocs := if code ≤ 1 then 7 else 5
  IO.println s!"regex|matchWith|i64|{arg pat} i64:{pn} {arg msg} i64:{n}|{code}|2|{allocs}"

/-- A case of the pattern words `ws`, followed in the array by a word that `pn` excludes, and the
bytes `input`. -/
def emit (ws : List UInt64) (input : List UInt8) : IO Unit :=
  emitWords (ws.toArray.push 7) ws.length (pack input) input.length

def cases : IO Unit := do
  let mut x : UInt64 := 7
  for _ in [0:40] do
    let (t, x') := gen 5 x
    x := x'
    for s in [[], [0], [1], [1, 64], [255, 0, 1], List.replicate 9 64] do
      emit t.words s
  for ws in [[], [3], [4], [5], [6], [2], [2, 1], [2, 1, 2, 3], [0, 0], [0, 0, 3, 3], [9],
      [1, 5, 5], [0, 1, 4, 5]] do
    emit ws [] *> emit ws [1]
  let many (k : Nat) : List UInt64 :=
    (List.replicate k [2, 2, 0, 0, 0]).flatten ++ List.replicate (k - 1) 3
  for k in [62, 63, 64, 65] do
    emit (many k) (List.replicate k 1)
    emit (many k) (List.replicate (k - 1) 1)
  -- A count past the pattern array reads zero words, each of which pushes `empty`.
  emitWords #[] 1 (pack [1]) 1
  emitWords #[2, 2, 0, 0] 5 (pack [1]) 1
  -- A count past the input array reads zero bytes.
  emitWords #[2, 1, 0, 0, 0, 5] 6 #[] 3
  emitWords #[2, 1, 0, 0, 0, 5] 6 #[0x0101] 12
  -- The star of the set of byte 0 over 1,000 zero bytes, and a 1 at the end.
  emit [2, 1, 0, 0, 0, 5] (List.replicate 1000 0)
  emit [2, 1, 0, 0, 0, 5] (List.replicate 999 0 ++ [1])

end TestSupport.Regex.Cases
