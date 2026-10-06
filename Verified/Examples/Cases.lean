import Verified.Examples.Poly
import Verified.Examples.Mix

/-! The cases of the verified compiler's examples, computed by native Lean, one line per case:
`module|export|result kind|host arguments|expected result`, as `tests/verified/run.sh` reads
them.  Run with `lake env lean --run`. -/

namespace Verified.Examples

def words : List UInt64 :=
  [0, 1, 2, 7, 8, 255, 4294967295, 4294967296, 9223372036854775807, 9223372036854775808,
    18446744073709551614, 18446744073709551615]

def polyCases : List (UInt64 × UInt64 × UInt64) :=
  (words.flatMap fun a => words.map fun b => (a, b, b + a)) ++
    (List.range 40).map fun i =>
      let k := UInt64.ofNat i
      (k * 0x9e3779b97f4a7c15, (k + 1) * 0xbf58476d1ce4e5b9, (k + 2) * 0x94d049bb133111eb)

/-- Zero divisors where `b` or `c` is 0, and shift amounts of 64 or more where `b` or `c` is at
least 64. -/
def mixCases : List (UInt64 × UInt64 × UInt64) :=
  (words.flatMap fun a => words.map fun b => (a, b, a - b)) ++
    (List.range 40).map fun i =>
      let k := UInt64.ofNat i
      (k * 0xd6e8feb86659fd93, (k + 3) * 0xa0761d6478bd642f, k % 70)

end Verified.Examples

open Verified.Examples in
def main : IO Unit := do
  for (a, b, c) in polyCases do
    IO.println s!"poly|poly|i64|i64:{a} i64:{b} i64:{c}|{Poly.poly a b c}"
  for (a, b, c) in mixCases do
    IO.println s!"mix|mix|i64|i64:{a} i64:{b} i64:{c}|{Mix.mix a b c}"
