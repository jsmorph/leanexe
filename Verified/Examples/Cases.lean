import Verified.Examples.Poly
import Verified.Examples.Mix
import Verified.Examples.Lets
import Verified.Examples.Select
import Verified.Examples.Calls
import Verified.Examples.Pairs
import Verified.Examples.Loops
import Verified.Examples.Arrays
import Verified.Examples.Owned

/-! The cases of the verified compiler's examples, computed by native Lean, one line per case:
`module|export|result kind|host arguments|expected result`, as `tests/verified/run.sh` reads
them, with a sixth field for the cases that check the allocation counters: the number of blocks
live after the call, the host's array arguments and the arrays of the result.  The expected
result `trap` stands for a trap at `unreachable`.  Run with `lake env lean --run`. -/

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

/-- Loop counts: none, one, a few, and enough to wrap the Fibonacci numbers and the powers.
`sumPowers` takes time quadratic in its count and runs only on the counts up to 100. -/
def counts : List UInt64 := [0, 1, 2, 3, 7, 8, 64, 65, 100, 1000, 65537]

/-- Arrays: empty, one element, a few, the words, and 100 elements. -/
def arrays : List (Array UInt64) :=
  [#[], #[5], #[1, 2, 3], words.toArray, (List.range 100).toArray.map UInt64.ofNat]

/-- The host's argument for an array. -/
def arrayArg (xs : Array UInt64) : String :=
  "array-u64:" ++ ",".intercalate (xs.toList.map toString)

/-- The host's output for an array result. -/
def arrayOut (xs : Array UInt64) : String :=
  "[" ++ ", ".intercalate (xs.toList.map toString) ++ "]"

def boolArg (b : Bool) : String := if b then "i64:1" else "i64:0"

end Verified.Examples

open Verified.Examples in
def main : IO Unit := do
  for (a, b, c) in polyCases do
    IO.println s!"poly|poly|i64|i64:{a} i64:{b} i64:{c}|{Poly.poly a b c}"
  for (a, b, c) in mixCases do
    IO.println s!"mix|mix|i64|i64:{a} i64:{b} i64:{c}|{Mix.mix a b c}"
  for (a, b) in letsCases do
    IO.println s!"lets|scramble|i64|i64:{a} i64:{b}|{Lets.scramble a b}"
  for x in words ++ [99, 100, 101] do
    IO.println s!"calls|sq|i64|i64:{x}|{Calls.sq x}"
    IO.println s!"calls|small|i64|i64:{x}|{if Calls.small x then 1 else 0}"
  for (a, b, c) in selectCases ++ [(99, 7, 3), (100, 7, 3), (5, 3, 7)] do
    IO.println s!"calls|sumSq|i64|i64:{a} i64:{b}|{Calls.sumSq a b}"
    IO.println s!"calls|pick|i64|i64:{a} i64:{b} i64:{c}|{Calls.pick a b c}"
  for (a, b, c) in selectCases do
    let (q, r) := Pairs.divMod a b
    IO.println s!"pairs|divMod|list:i64,i64|i64:{a} i64:{b}|{q} {r}"
    let (x, y) := Pairs.swapAdd (a, b)
    IO.println s!"pairs|swapAdd|list:i64,i64|i64:{a} i64:{b}|{x} {y}"
    IO.println s!"pairs|sumPair|i64|i64:{a} i64:{b}|{Pairs.sumPair (a, b)}"
    let (lo, hi) := Pairs.minMax a b
    IO.println s!"pairs|minMax|list:i64,i64|i64:{a} i64:{b}|{lo} {hi}"
    IO.println s!"pairs|spread|i64|i64:{a} i64:{b} i64:{c}|{Pairs.spread a b c}"
    let ((n1, n2), n3) := Pairs.nested a b
    let n2w := if n2 then 1 else 0
    IO.println s!"pairs|nested|list:i64,i64,i64|i64:{a} i64:{b}|{n1} {n2w} {n3}"
    for flag in [false, true] do
      let f := if flag then 1 else 0
      IO.println s!"pairs|unnest|i64|i64:{a} i64:{f} i64:{b}|{Pairs.unnest ((a, flag), b)}"
  for (a, b, c) in selectCases do
    IO.println s!"select|median|i64|i64:{a} i64:{b} i64:{c}|{Select.median a b c}"
    IO.println s!"select|inBand|i64|i64:{a} i64:{b} i64:{c}|{if Select.inBand a b c then 1 else 0}"
    IO.println s!"select|clamp|i64|i64:{a} i64:{b} i64:{c}|{Select.clamp a b c}"
    for flag in [false, true] do
      let f := if flag then 1 else 0
      IO.println s!"select|pickNe|i64|i64:{a} i64:{b} i64:{f}|{Select.pickNe a b flag}"
  for n in counts do
    IO.println s!"loops|triangle|i64|i64:{n}|{Loops.triangle n}"
    IO.println s!"loops|fib|i64|i64:{n}|{Loops.fib n}"
    for x in words do
      IO.println s!"loops|power|i64|i64:{x} i64:{n}|{Loops.power x n}"
      IO.println s!"loops|collatz|i64|i64:{x} i64:{n}|{Loops.collatz x n}"
      let (found, seen) := Loops.firstAbove x n
      let seenWord := if seen then 1 else 0
      IO.println s!"loops|firstAbove|list:i64,i64|i64:{x} i64:{n}|{found} {seenWord}"
  for n in counts.filter (· ≤ 100) do
    for x in [0, 1, 2, 3, 18446744073709551615] do
      IO.println s!"loops|sumPowers|i64|i64:{x} i64:{n}|{Loops.sumPowers x n}"
  for n in [0, 1, 3, 10, 50] do
    for k in [0, 1, 3, 10, 50] do
      IO.println s!"loops|grid|i64|i64:{n} i64:{k}|{Loops.grid n k}"
  for xs in arrays do
    IO.println s!"arrays|sum|i64|{arrayArg xs}|{Arrays.sum xs}"
    for key in [0, 1, 2, 5, 255] do
      IO.println s!"arrays|count|i64|{arrayArg xs} i64:{key}|{Arrays.count xs key}"
    for limit in [0, 2, 50, 255, 18446744073709551615] do
      let (found, seen) := Arrays.firstAbove xs limit
      let seenWord := if seen then 1 else 0
      IO.println s!"arrays|firstAbove|list:i64,i64|{arrayArg xs} i64:{limit}|{found} {seenWord}"
    for i in [0, 1, 2, 3, 11, 99, 100, 18446744073709551615] do
      IO.println s!"arrays|at3|i64|{arrayArg xs} i64:{i}|{Arrays.at3 xs i}"
    for ys in arrays do
      IO.println s!"arrays|dot|i64|{arrayArg xs} {arrayArg ys}|{Arrays.dot xs ys}"
      IO.println s!"arrays|sumBoth|i64|{arrayArg xs} {arrayArg ys}|{Arrays.sumBoth (xs, ys)}"
      IO.println s!"arrays|larger|i64|{arrayArg xs} {arrayArg ys}|{Arrays.larger xs ys}"
  for xs in arrays do
    let a := arrayArg xs
    IO.println s!"owned|copy|array-u64|{a}|{arrayOut (Owned.copy xs)}|2"
    let (t1, t2) := Owned.twice xs
    IO.println s!"owned|twice|list:array-u64,array-u64|{a}|{arrayOut t1} {arrayOut t2}|3"
    let (w, n) := Owned.withSize xs
    IO.println s!"owned|withSize|list:array-u64,i64|{a}|{arrayOut w} {n}|2"
    IO.println s!"owned|sizeOfCopy|i64|{a}|{Owned.sizeOfCopy xs}|1"
    IO.println s!"owned|sumCopy|i64|{a}|{Owned.sumCopy xs}|1"
    IO.println s!"owned|unused|i64|{a}|{Owned.unused xs}|1"
    IO.println s!"owned|moved|array-u64|{a}|{arrayOut (Owned.moved xs)}|2"
    for b in [false, true] do
      IO.println s!"owned|branch|i64|{boolArg b} {a}|{Owned.branch b xs}|1"
    for n in [0, 1, 2, 3, 10] do
      IO.println s!"owned|grow|array-u64|{a} i64:{n}|{arrayOut (Owned.grow xs n)}|2"
    for ys in arrays do
      let c := arrayArg ys
      for b in [false, true] do
        IO.println s!"owned|pick|array-u64|{boolArg b} {a} {c}|{arrayOut (Owned.pick b xs ys)}|3"
      let (s1, s2) := Owned.swap xs ys
      IO.println s!"owned|swap|list:array-u64,array-u64|{a} {c}|{arrayOut s1} {arrayOut s2}|4"
  for n in [0, 1, 5, 100] do
    IO.println s!"owned|squares|array-u64|i64:{n}|{arrayOut (Owned.squares n)}|1"
    IO.println s!"owned|sumSquares|i64|i64:{n}|{Owned.sumSquares n}|0"
  for n in [0, 1, 4, 20] do
    IO.println s!"owned|rowSums|array-u64|i64:{n}|{arrayOut (Owned.rowSums n)}|1"
  -- An array of `2 ^ 29` words does not fit in 32-bit memory, so the module traps; native Lean
  -- does not compute it.
  IO.println "owned|squares|array-u64|i64:536870912|trap"
  for xs in arrays do
    let a := arrayArg xs
    IO.println s!"owned|bothSides|array-u64|{a}|{arrayOut (Owned.bothSides xs)}|2"
    for k in [0, 3] do
      IO.println s!"owned|scaled|array-u64|{a} i64:{k}|{arrayOut (Owned.scaled xs k)}|2"
    for n in [0, 3] do
      IO.println s!"owned|onlyInside|array-u64|{a} i64:{n}|{arrayOut (Owned.onlyInside xs n)}|2"
  -- `firstOfCopy` reads past the end of an empty array, which native Lean reports.
  for xs in arrays.filter (·.size > 0) do
    IO.println s!"owned|firstOfCopy|i64|{arrayArg xs}|{Owned.firstOfCopy xs}|1"
