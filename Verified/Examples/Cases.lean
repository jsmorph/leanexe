import Verified.Examples.Poly
import Verified.Examples.Mix
import Verified.Examples.Lets
import Verified.Examples.Select
import Verified.Examples.Calls
import Verified.Examples.Pairs
import Verified.Examples.Loops
import Verified.Examples.Arrays
import Verified.Examples.Owned
import Verified.Examples.Updates
import Verified.Examples.Grow
import Verified.Examples.Modes
import Verified.Examples.Floats

/-! The cases of the verified compiler's examples, computed by native Lean, one line per case:
`module|export|result kind|host arguments|expected result`, as `tests/verified/run.sh` reads
them, with a sixth field for the cases that check the allocation counters: the number of blocks
live after the call, the host's array arguments and the arrays of the result, and a seventh field
for the cases that bound the number of allocations, the host's included.  The expected result
`trap` stands for a trap at `unreachable`.  Run with `lake env lean --run`. -/

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

def bit (b : Bool) : Nat := if b then 1 else 0

/-- Floats: both zeros, small and large magnitudes of each sign, the smallest subnormal, both
infinities, and NaN. -/
def floats : List Float :=
  [0.0, -0.0, 1.0, -1.0, 0.5, 1.5, -3.25, 2.0, 1e300, -1e-300, Float.ofBits 1, 1.0 / 0.0,
    -1.0 / 0.0, 0.0 / 0.0]

/-- Floats for the functions of two or three floats: both zeros, both infinities, NaN, and
values of each sign. -/
def someFloats : List Float := [0.0, -0.0, 1.0, -1.5, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, 1e300]

/-- Bands for the functions of a float and a band: ordinary, reversed, empty, unbounded, from
`-0` to `0`, and with a NaN bound. -/
def bands : List (Float × Float) :=
  [(0.0, 1.0), (-1.0, 2.0), (1.0, 0.0), (1.5, 1.5), (-1.0 / 0.0, 1.0 / 0.0), (-0.0, 0.0),
    (0.0 / 0.0, 1.0)]

def floatArg (x : Float) : String := s!"f64:{x.toBits}"

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
    IO.println s!"owned|copy|array-u64|{a}|{arrayOut (Owned.copy xs)}|1"
    let (t1, t2) := Owned.twice xs
    IO.println s!"owned|twice|list:array-u64,array-u64|{a}|{arrayOut t1} {arrayOut t2}|2"
    let (w, n) := Owned.withSize xs
    IO.println s!"owned|withSize|list:array-u64,i64|{a}|{arrayOut w} {n}|2"
    IO.println s!"owned|sizeOfCopy|i64|{a}|{Owned.sizeOfCopy xs}|0"
    IO.println s!"owned|sumCopy|i64|{a}|{Owned.sumCopy xs}|0"
    IO.println s!"owned|unused|i64|{a}|{Owned.unused xs}|0"
    IO.println s!"owned|moved|array-u64|{a}|{arrayOut (Owned.moved xs)}|1"
    for b in [false, true] do
      IO.println s!"owned|branch|i64|{boolArg b} {a}|{Owned.branch b xs}|0"
    for n in [0, 1, 2, 3, 10] do
      IO.println s!"owned|grow|array-u64|{a} i64:{n}|{arrayOut (Owned.grow xs n)}|1"
    for ys in arrays do
      let c := arrayArg ys
      for b in [false, true] do
        IO.println s!"owned|pick|array-u64|{boolArg b} {a} {c}|{arrayOut (Owned.pick b xs ys)}|1"
      let (s1, s2) := Owned.swap xs ys
      IO.println s!"owned|swap|list:array-u64,array-u64|{a} {c}|{arrayOut s1} {arrayOut s2}|2"
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
    IO.println s!"owned|bothSides|array-u64|{a}|{arrayOut (Owned.bothSides xs)}|1"
    for k in [0, 3] do
      IO.println s!"owned|scaled|array-u64|{a} i64:{k}|{arrayOut (Owned.scaled xs k)}|2"
    for n in [0, 3] do
      IO.println s!"owned|onlyInside|array-u64|{a} i64:{n}|{arrayOut (Owned.onlyInside xs n)}|1"
  let positions : List UInt64 := [0, 1, 2, 4, 100, 9223372036854775808, 18446744073709551615]
  for xs in arrays do
    let a := arrayArg xs
    IO.println s!"updates|swapEnds|array-u64|{a}|{arrayOut (Updates.swapEnds xs)}|2|3"
    for b in [0, 1, 3, 16] do
      let h := arrayOut (Updates.histogram xs b)
      IO.println s!"updates|histogram|array-u64|{a} i64:{b}|{h}|2|2"
    for i in positions do
      let u := arrayOut (Updates.setParam xs i 77)
      IO.println s!"updates|setParam|array-u64|{a} i64:{i} i64:77|{u}|1|1"
  for n in [0, 1, 3, 10] do
    for i in positions do
      let u := arrayOut (Updates.setBuilt n i 5)
      IO.println s!"updates|setBuilt|array-u64|i64:{n} i64:{i} i64:5|{u}|1|1"
      let (k1, k2) := Updates.keepBoth n i 5
      let kinds := "list:array-u64,array-u64"
      IO.println s!"updates|keepBoth|{kinds}|i64:{n} i64:{i} i64:5|{arrayOut k1} {arrayOut k2}|2|2"
  -- Growth by doubling: a loop of `n` pushes allocates at most `2 + log₂ (n + 1)` blocks.
  let counts : List UInt64 := [0, 1, 2, 3, 7, 8, 64, 65, 1000]
  for n in counts do
    let bound := 2 + Nat.log2 (n.toNat + 1)
    IO.println s!"grow|evens|array-u64|i64:{n}|{arrayOut (Grow.evens n)}|1|{bound}"
    IO.println s!"grow|pushBuilt|array-u64|i64:{n} i64:9|{arrayOut (Grow.pushBuilt n 9)}|1|2"
    let two := arrayOut (Grow.pushTwo n 5 6)
    IO.println s!"grow|pushTwo|array-u64|i64:{n} i64:5 i64:6|{two}|1|3"
    IO.println s!"grow|pushSize|array-u64|i64:{n}|{arrayOut (Grow.pushSize n)}|1|2"
    let (k1, k2) := Grow.pushKeep n 4
    let kinds := "list:array-u64,array-u64"
    IO.println s!"grow|pushKeep|{kinds}|i64:{n} i64:4|{arrayOut k1} {arrayOut k2}|2|2"
    IO.println s!"grow|appendSelfOwned|array-u64|i64:{n}|{arrayOut (Grow.appendSelfOwned n)}|1|2"
  for xs in arrays do
    let a := arrayArg xs
    IO.println s!"grow|pushParam|array-u64|{a} i64:3|{arrayOut (Grow.pushParam xs 3)}|1|2"
    IO.println s!"grow|appendSelf|array-u64|{a}|{arrayOut (Grow.appendSelf xs)}|2|2"
    for n in [0, 1, 5] do
      let r := arrayOut (Grow.appendOwnedRight xs n)
      IO.println s!"grow|appendOwnedRight|array-u64|{a} i64:{n}|{r}|1|3"
      let b := arrayOut (Grow.appendBuilt n xs)
      IO.println s!"grow|appendBuilt|array-u64|i64:{n} {a}|{b}|2|3"
      let room := arrayOut (Grow.appendRoom n xs)
      IO.println s!"grow|appendRoom|array-u64|i64:{n} {a}|{room}|2|4"
    for n in [0, 1, 3, 20] do
      let bound := 4 + Nat.log2 (n.toNat * xs.size + 1)
      let r := arrayOut (Grow.repeated xs n)
      IO.println s!"grow|repeated|array-u64|{a} i64:{n}|{r}|2|{bound}"
    for ys in arrays do
      let r := arrayOut (Grow.appendParams xs ys)
      IO.println s!"grow|appendParams|array-u64|{a} {arrayArg ys}|{r}|2|3"
  for xs in arrays do
    let a := arrayArg xs
    IO.println s!"modes|same|array-u64|{a}|{arrayOut (Modes.same xs)}|1|1"
    let (c, w) := Modes.withCount xs
    IO.println s!"modes|withCount|list:i64,array-u64|{a}|{c} {arrayOut w}|1|1"
    for i in [0, 1, 5, 18446744073709551615] do
      IO.println s!"modes|bump|array-u64|{a} i64:{i}|{arrayOut (Modes.bump xs i)}|1|1"
    IO.println s!"modes|bumpFirst|array-u64|{a}|{arrayOut (Modes.bumpFirst xs)}|1|1"
    IO.println s!"modes|bumpTwice|array-u64|{a}|{arrayOut (Modes.bumpTwice xs)}|1|1"
    IO.println s!"modes|bumpLast|array-u64|{a}|{arrayOut (Modes.bumpLast xs)}|1|1"
    IO.println s!"modes|bumpAll|array-u64|{a}|{arrayOut (Modes.bumpAll xs)}|1|1"
    IO.println s!"modes|addSelf|array-u64|{a}|{arrayOut (Modes.addSelf xs)}|2|2"
    let (s, p) := Modes.pairArg xs
    IO.println s!"modes|pairArg|list:i64,array-u64|{a}|{s} {arrayOut p}|1|1"
    let (t1, t2) := Modes.twoSame xs
    let kinds := "list:array-u64,array-u64"
    IO.println s!"modes|twoSame|{kinds}|{a}|{arrayOut t1} {arrayOut t2}|3|3"
    let (k1, k2) := Modes.bumpKeep xs
    IO.println s!"modes|bumpKeep|{kinds}|{a}|{arrayOut k1} {arrayOut k2}|2|2"
    IO.println s!"byhand|dropArg|i64|{a} i64:7|7|0|1"
    IO.println s!"byhand|sizeOwned|i64|{a}|{xs.size}|0|1"
    for ys in arrays do
      let c := arrayArg ys
      let (s1, s2) := Modes.swapPair (xs, ys)
      IO.println s!"modes|swapPair|{kinds}|{a} {c}|{arrayOut s1} {arrayOut s2}|4|4"
      let (b1, b2) := Modes.both xs ys
      IO.println s!"modes|both|{kinds}|{a} {c}|{arrayOut b1} {arrayOut b2}|2|2"
  for x in floats do
    let a := floatArg x
    IO.println s!"floats|negate|f64|{a}|{(Floats.negate x).toBits}"
    for (lo, hi) in bands do
      let band := s!"{a} {floatArg lo} {floatArg hi}"
      IO.println s!"floats|piecewise|f64|{band}|{(Floats.piecewise x lo hi).toBits}"
      IO.println s!"floats|inBand|i64|{band}|{bit (Floats.inBand x lo hi)}"
      IO.println s!"floats|clamp|f64|{band}|{(Floats.clamp x lo hi).toBits}"
      IO.println s!"floats|hypot|f64|{band}|{(Floats.hypot x lo hi).toBits}"
  for a in someFloats do
    for b in someFloats do
      let ab := s!"{floatArg a} {floatArg b}"
      IO.println s!"floats|least|f64|{ab}|{(Floats.least a b).toBits}"
      IO.println s!"floats|most|f64|{ab}|{(Floats.most a b).toBits}"
      IO.println s!"floats|combined|f64|{ab}|{(Floats.combined a b).toBits}"
      for c in [0.0, -0.0, 0.0 / 0.0, 2.5] do
        IO.println s!"floats|minSum|f64|{ab} {floatArg c}|{(Floats.minSum a b c).toBits}"
  for n in counts do
    IO.println s!"floats|harmonic|f64|i64:{n}|{(Floats.harmonic n).toBits}"
  for x in someFloats do
    for xs in [#[], #[1, 2, 3]] do
      for (y, k) in [(2.0, 5), (0.0 / 0.0, 18446744073709551615), (-0.0, 0)] do
        for n in [0, 18446744073709551615] do
          let (r, m) := Floats.mixed n x xs (y, k)
          let args := s!"i64:{n} {floatArg x} {arrayArg xs} {floatArg y} i64:{k}"
          IO.println s!"floats|mixed|list:f64,i64|{args}|{r.toBits} {m}"
  -- `firstOfCopy` reads past the end of an empty array, which native Lean reports.
  for xs in arrays.filter (·.size > 0) do
    IO.println s!"owned|firstOfCopy|i64|{arrayArg xs}|{Owned.firstOfCopy xs}|0"
