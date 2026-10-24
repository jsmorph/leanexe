import TestSupport.Regex.Generate

/-! Writes cases for `tests/regex/python_check.py`: one line per pattern and input, with the
pattern's postfix words, the input's bytes in hexadecimal, and the answer of
`Library.Regex.matchWith`, separated by `|`.  The patterns are those of
`TestSupport.Regex.Generate` and random word sequences, and the inputs are every string of at
most three of its input bytes.  Run with `lake env lean --run` after building
`TestSupport.Regex.Generate`. -/

namespace TestSupport.Regex.PythonCases

open Library.Regex TestSupport.Regex.Generate

def hex (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length < 2 then "0" ++ s else s)

def emit (ws : List UInt64) (input : List UInt8) : IO Unit := do
  let pat := ws.toArray ++ #[7, 0xFFFFFFFFFFFFFFFF]
  let got := matchWith pat ws.length.toUInt64 (pack input) input.length.toUInt64
  IO.println s!"{",".intercalate (ws.map toString)}|{hex input}|{got}"

def main : IO Unit := do
  let strings := (inputs 3).eraseDups
  let mut x : UInt64 := 7
  for _ in [0:400] do
    let (t, x') := gen 4 x
    x := x'
    for s in strings do emit t.words s
  for _ in [0:500] do
    x := next x
    let len := pick x 12
    let mut ws : List UInt64 := []
    for _ in [0:len] do
      x := next x
      ws := ws ++ [(pick x 7).toUInt64]
    emit ws [1]

end TestSupport.Regex.PythonCases

def main : IO Unit := TestSupport.Regex.PythonCases.main
