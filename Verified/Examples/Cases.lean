import Verified.Examples.Poly
import Verified.Examples.Mix
import Verified.Examples.Lets
import Verified.Examples.Select

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

/-- `a = 2^64 - 7` makes the remainder's divisor `a + 7` zero. -/
def letsCases : List (UInt64 × UInt64) :=
  (words.flatMap fun a => words.map fun b => (a, b)) ++
    (words.map fun b => (18446744073709551609, b)) ++
    (List.range 40).map fun i =>
      let k := UInt64.ofNat i
      (k * 0xc2b2ae3d27d4eb4f, (k + 5) * 0x165667b19e3779f9)

/-- Each pair of words with a third chosen from the pair's positions, and every order of four
triples, three of them with equal words. -/
def selectCases : List (UInt64 × UInt64 × UInt64) :=
  ((words.zipIdx.flatMap fun (a, i) => words.zipIdx.map fun (b, j) =>
      (a, b, words.getD ((5 * i + 7 * j) % words.length) 0))) ++
    ([(1, 2, 3), (5, 5, 1), (5, 1, 5), (0, 0, 0)].flatMap fun (a, b, c) =>
      [(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)])

end Verified.Examples

open Verified.Examples in
def main : IO Unit := do
  for (a, b, c) in polyCases do
    IO.println s!"poly|poly|i64|i64:{a} i64:{b} i64:{c}|{Poly.poly a b c}"
  for (a, b, c) in mixCases do
    IO.println s!"mix|mix|i64|i64:{a} i64:{b} i64:{c}|{Mix.mix a b c}"
  for (a, b) in letsCases do
    IO.println s!"lets|scramble|i64|i64:{a} i64:{b}|{Lets.scramble a b}"
  for (a, b, c) in selectCases do
    IO.println s!"select|median|i64|i64:{a} i64:{b} i64:{c}|{Select.median a b c}"
    IO.println s!"select|inBand|i64|i64:{a} i64:{b} i64:{c}|{if Select.inBand a b c then 1 else 0}"
