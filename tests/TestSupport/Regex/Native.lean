import Library.Regex.Program
import Library.Regex.Spec
import Library.Bytes.Packed
import TestSupport.Regex.Generate

/-! A native check of `Library.Regex.matchWith` against `Library.Regex.Spec.answer` on the patterns
of `TestSupport.Regex.Generate` and every input of at most four bytes over its input bytes.
Random word sequences, most of which do not decode, and patterns with more than 63 sets check
codes 2 and 3.  The check exits with an error at the first difference.  Run with
`lake env lean --run` after building `TestSupport.Regex.Generate`. -/

namespace TestSupport.Regex.Native

open Library.Regex Library.Regex.Spec Library.Bytes TestSupport.Regex.Generate

def check (ws : List UInt64) (input : List UInt8) : IO Unit := do
  let pat := ws.toArray ++ #[7, 0xFFFFFFFFFFFFFFFF]
  let got := matchWith pat ws.length.toUInt64 (pack input) input.length.toUInt64
  let want := answer ws input
  unless got == want do
    throw <| IO.userError s!"pattern {ws} input {input}: matchWith {got}, answer {want}"

def main : IO Unit := do
  let strings := (inputs 4).eraseDups
  let mut x : UInt64 := 1
  let mut patterns := 0
  for _ in [0:600] do
    let (t, x') := gen 4 x
    x := x'
    patterns := patterns + 1
    for s in strings do check t.words s
  IO.println s!"trees: {patterns} patterns, {strings.length} inputs each"
  let mut codes := 0
  for _ in [0:3000] do
    x := next x
    let len := pick x 12
    let mut ws : List UInt64 := []
    for _ in [0:len] do
      x := next x
      ws := ws ++ [(pick x 7).toUInt64]
    check ws [] *> check ws [1]
    codes := codes + 1
  IO.println s!"word sequences: {codes}"
  let many (k : Nat) : List UInt64 :=
    (List.replicate k [2, 2, 0, 0, 0]).flatten ++ List.replicate (k - 1) 3
  for k in [62, 63, 64, 65, 80] do
    check (many k) (List.replicate k 1)
    check (many k ++ [9]) []
  IO.println "positions: 62 to 65 and 80"

end TestSupport.Regex.Native

def main : IO Unit := TestSupport.Regex.Native.main
