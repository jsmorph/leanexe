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
import Verified.Examples.Elements
import Verified.Examples.Tuples
import Verified.Examples.Records
import Verified.Examples.Grids
import Verified.Examples.Repeat

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

/-- Arrays of floats: empty, one element, a few, the special floats, and 50 elements. -/
def floatArrays : List (Array Float) :=
  [#[], #[1.5], #[1.0, -2.0, 0.5], floats.toArray,
    (List.range 50).toArray.map fun i => (UInt64.ofNat i).toFloat * 0.25 - 3.0]

/-- Arrays of `Bool`s: empty, one element, a few, and 40 elements. -/
def boolArrays : List (Array Bool) :=
  [#[], #[true], #[false, true, true], (List.range 40).toArray.map fun i => i % 3 == 0]

/-- The host's argument and output for an array of floats, by bit patterns. -/
def floatArrayArg (xs : Array Float) : String := arrayArg (xs.map Float.toBits)

def floatArrayOut (xs : Array Float) : String := arrayOut (xs.map Float.toBits)

/-- The host's argument and output for an array of `Bool`s, as 1 or 0. -/
def boolArrayArg (bs : Array Bool) : String := arrayArg (bs.map fun b => if b then 1 else 0)

def boolArrayOut (bs : Array Bool) : String := arrayOut (bs.map fun b => if b then 1 else 0)

/-- Arrays of tuples of a float and a word: empty, one element, special floats, and built ones. -/
def pointArrays : List (Array (Float × UInt64)) :=
  [#[], #[(1.5, 7)], #[(0.0 / 0.0, 1), (-0.0, 18446744073709551615), (1.0 / 0.0, 0)],
    Tuples.points 10]

/-- The host's argument and output for an array of tuples, by their words. -/
def pointWords (xs : Array (Float × UInt64)) : Array UInt64 :=
  (xs.toList.flatMap fun (x, k) => [x.toBits, k]).toArray

def nestedWords (xs : Array ((UInt64 × Bool) × Float)) : Array UInt64 :=
  (xs.toList.flatMap fun ((k, b), x) => [k, if b then 1 else 0, x.toBits]).toArray

open Records in
/-- Structures of three floats: ordinary, with both zeros, and with NaN and a large value. -/
def conserveds : List Conserved :=
  [⟨1.0, 2.0, 3.0⟩, ⟨0.0, -0.0, 1.5⟩, ⟨0.0 / 0.0, 1e300, -2.5⟩]

open Records in
/-- The host's arguments and output for a `Conserved` and a `Cell`, field by field. -/
def conservedArg (c : Conserved) : String :=
  s!"f64:{c.density.toBits} f64:{c.momentum.toBits} f64:{c.energy.toBits}"

open Records in
def conservedOut (c : Conserved) : String :=
  s!"{c.density.toBits} {c.momentum.toBits} {c.energy.toBits}"

open Records in
def cellArg (c : Cell) : String :=
  s!"i64:{c.index} {conservedArg c.state} f64:{c.pressure.toBits} {boolArg c.ok}"

open Records in
def cellOut (c : Cell) : String :=
  s!"{c.index} {conservedOut c.state} {c.pressure.toBits} {bit c.ok}"

open Records in
/-- The host's arguments and outputs for arrays of structures, by their words. -/
def conservedWords (us : Array Conserved) : Array UInt64 :=
  (us.toList.flatMap fun u => [u.density.toBits, u.momentum.toBits, u.energy.toBits]).toArray

open Records in
def cellWords (cs : Array Cell) : Array UInt64 :=
  (cs.toList.flatMap fun c => c.index :: (conservedWords #[c.state]).toList ++
    [c.pressure.toBits, if c.ok then 1 else 0]).toArray

open Records in
/-- Arrays of structures: empty, one element, the special structures, and built ones. -/
def conservedArrays : List (Array Conserved) :=
  [#[], #[⟨1.0, 2.0, 3.0⟩], conserveds.toArray, Grids.ramp 10]

/-- Words for `Float.ofBits`: NaN patterns with either sign and a signaling one, both
infinities, both zeros, the smallest subnormal, and words. -/
def floatWords : List UInt64 :=
  [0x7FF0000000000001, 0x7FF8000000000001, 0xFFF8000000000000, 0xFFFFFFFFFFFFFFFF,
    0x7FF0000000000000, 0xFFF0000000000000, 0x8000000000000000, 0x3FF0000000000000] ++ words

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
    IO.println s!"floats|mean|f64|i64:{n}|{(Floats.mean n).toBits}"
  for x in floats ++ [0.0005, 0.9994, 1.8446744073709552e16, 1.8446744073709552e19, -0.5] do
    let a := floatArg x
    IO.println s!"floats|truncate|i64|{a}|{Floats.truncate x}"
    IO.println s!"floats|bits|i64|{a}|{Floats.bits x}"
    let (l1, l2) := Floats.literals x
    IO.println s!"floats|literals|list:f64,f64|{a}|{l1.toBits} {l2.toBits}"
    for k in [0, 1, 52, 1023] do
      IO.println s!"floats|scaleByPower|f64|{a} i64:{k}|{(Floats.scaleByPower x k).toBits}"
  for w in floatWords do
    IO.println s!"floats|ofBits|f64|i64:{w}|{(Floats.ofBits w).toBits}"
    IO.println s!"floats|roundTrip|i64|i64:{w}|{Floats.roundTrip w}"
  for x in someFloats do
    for xs in [#[], #[1, 2, 3]] do
      for (y, k) in [(2.0, 5), (0.0 / 0.0, 18446744073709551615), (-0.0, 0)] do
        for n in [0, 18446744073709551615] do
          let (r, m) := Floats.mixed n x xs (y, k)
          let args := s!"i64:{n} {floatArg x} {arrayArg xs} {floatArg y} i64:{k}"
          IO.println s!"floats|mixed|list:f64,i64|{args}|{r.toBits} {m}"
  for xs in floatArrays do
    let a := floatArrayArg xs
    IO.println s!"elements|total|f64|{a}|{(Elements.total xs).toBits}|1"
    IO.println s!"elements|largest|f64|{a}|{(Elements.largest xs).toBits}|1"
    IO.println s!"elements|negatives|array-u64|{a}|{boolArrayOut (Elements.negatives xs)}|2"
    for x in [0.0, -0.0, 2.5, 0.0 / 0.0] do
      let r := floatArrayOut (Elements.extend xs x)
      IO.println s!"elements|extend|array-u64|{a} {floatArg x}|{r}|2"
    for ys in floatArrays do
      let c := floatArrayArg ys
      IO.println s!"elements|dot|f64|{a} {c}|{(Elements.dot xs ys).toBits}|2"
      let r := floatArrayOut (Elements.axpy 2.0 xs ys)
      IO.println s!"elements|axpy|array-u64|{floatArg 2.0} {a} {c}|{r}|2|2"
    for bs in boolArrays do
      IO.println s!"elements|select|f64|{boolArrayArg bs} {a}|{(Elements.select bs xs).toBits}|2"
  for n in [0, 1, 5, 100] do
    for (x0, dx) in [(0.0, 1.0), (-1.5, 0.1), (1e300, 1e300)] do
      let g := floatArrayOut (Elements.grid n x0 dx)
      IO.println s!"elements|grid|array-u64|i64:{n} {floatArg x0} {floatArg dx}|{g}|1"
  for bs in boolArrays do
    let a := boolArrayArg bs
    IO.println s!"elements|countTrue|i64|{a}|{Elements.countTrue bs}|1"
    for b in [false, true] do
      let r := boolArrayOut (Elements.pushFlag bs b)
      IO.println s!"elements|pushFlag|array-u64|{a} {boolArg b}|{r}|1"
    for i in [0, 1, 2, 39, 40, 18446744073709551615] do
      IO.println s!"elements|flip|array-u64|{a} i64:{i}|{boolArrayOut (Elements.flip bs i)}|1|1"
  for n in [0, 1, 2, 10, 30] do
    IO.println s!"elements|sieve|array-u64|i64:{n}|{boolArrayOut (Elements.sieve n)}|1|1"
  for n in [0, 1, 5, 100] do
    IO.println s!"tuples|points|array-u64|i64:{n}|{arrayOut (pointWords (Tuples.points n))}|1"
    IO.println s!"tuples|flags|array-u64|i64:{n}|{arrayOut (nestedWords (Tuples.flags n))}|1"
    for i in [0, 1, 4, 5, 18446744073709551615] do
      let fs := Tuples.flags n
      let a := arrayArg (nestedWords fs)
      IO.println s!"tuples|flagAt|i64|{a} i64:{i}|{bit (Tuples.flagAt fs i)}|1"
  for xs in pointArrays do
    let a := arrayArg (pointWords xs)
    IO.println s!"tuples|sumFirst|f64|{a}|{(Tuples.sumFirst xs).toBits}|1"
    IO.println s!"tuples|count|i64|{a}|{Tuples.count xs}|1"
    for i in [0, 1, 2, 9, 10, 18446744073709551615] do
      let r := arrayOut (pointWords (Tuples.bump xs i))
      IO.println s!"tuples|bump|array-u64|{a} i64:{i}|{r}|1|1"
    let r := arrayOut (pointWords (Tuples.pushPoint xs 2.5 9))
    IO.println s!"tuples|pushPoint|array-u64|{a} {floatArg 2.5} i64:9|{r}|1"
    for ys in pointArrays do
      let j := arrayOut (pointWords (Tuples.joined xs ys))
      IO.println s!"tuples|joined|array-u64|{a} {arrayArg (pointWords ys)}|{j}|2"
  let three := "list:f64,f64,f64"
  let cellKinds := "list:i64,f64,f64,f64,f64,i64"
  for c in conserveds do
    let a := conservedArg c
    IO.println s!"records|kinetic|f64|{a}|{(Records.kinetic c).toBits}"
    IO.println s!"records|reversed|{three}|{a}|{conservedOut (Records.reversed c)}"
    for x in [2.0, -0.5, 0.0 / 0.0] do
      IO.println s!"records|scale|{three}|{floatArg x} {a}|{conservedOut (Records.scale x c)}"
    for n in [0, 1, 5] do
      IO.println s!"records|repeated|{three}|i64:{n} {a}|{conservedOut (Records.repeated n c)}"
    for d in conserveds do
      let b := conservedArg d
      IO.println s!"records|add|{three}|{a} {b}|{conservedOut (Records.add c d)}"
      for f in [false, true] do
        let r := conservedOut (Records.pick f c d)
        IO.println s!"records|pick|{three}|{boolArg f} {a} {b}|{r}"
    for i in [0, 7, 18446744073709551615] do
      for p in [1.5, -1.0, -0.0, 0.0 / 0.0] do
        let cell := Records.mkCell i c p
        let args := s!"i64:{i} {a} {floatArg p}"
        IO.println s!"records|mkCell|{cellKinds}|{args}|{cellOut cell}"
        IO.println s!"records|cellEnergy|f64|{cellArg cell}|{(Records.cellEnergy cell).toBits}"
        let r := cellOut (Records.bumpIndex cell)
        IO.println s!"records|bumpIndex|{cellKinds}|{cellArg cell}|{r}"
        let (b, k) := Records.withCount cell
        IO.println s!"records|withCount|{cellKinds},i64|{cellArg cell}|{cellOut b} {k}"
  for n in [0, 1, 5, 100] do
    IO.println s!"grids|ramp|array-u64|i64:{n}|{arrayOut (conservedWords (Grids.ramp n))}|1"
    IO.println s!"grids|pairTotal|f64|i64:{n}|{(Grids.pairTotal n).toBits}|0"
  for us in conservedArrays do
    let a := arrayArg (conservedWords us)
    IO.println s!"grids|totalEnergy|f64|{a}|{(Grids.totalEnergy us).toBits}|1"
    for x in [2.0, -0.5] do
      let r := arrayOut (conservedWords (Grids.scaled x us))
      IO.println s!"grids|scaled|array-u64|{floatArg x} {a}|{r}|1|1"
    let (ws, t) := Grids.withTotal us
    let r := s!"{arrayOut (conservedWords ws)} {t.toBits}"
    IO.println s!"grids|withTotal|list:array-u64,f64|{a}|{r}|1|1"
    for vs in conservedArrays do
      let r := arrayOut (conservedWords (Grids.joined us vs))
      IO.println s!"grids|joined|array-u64|{a} {arrayArg (conservedWords vs)}|{r}|2"
    let grid := Grids.cells us
    let g := arrayArg (cellWords grid)
    IO.println s!"grids|cells|array-u64|{a}|{arrayOut (cellWords grid)}|2"
    IO.println s!"grids|allOk|i64|{g}|{bit (Grids.allOk grid)}|1"
    IO.println s!"grids|count|i64|{g}|{Grids.count grid}|1"
    for i in [0, 1, 2, 9, 10, 18446744073709551615] do
      IO.println s!"grids|density|f64|{g} i64:{i}|{(Grids.density grid i).toBits}|1"
    for p in [1.5, -1.0] do
      let r := arrayOut (cellWords (Grids.addCell grid ⟨1.0, 2.0, 3.0⟩ p))
      let args := s!"{g} {conservedArg ⟨1.0, 2.0, 3.0⟩} {floatArg p}"
      IO.println s!"grids|addCell|array-u64|{args}|{r}|1"
  for n in [0, 1, 2, 3, 6, 7, 27, 97, 18446744073709551615] do
    IO.println s!"repeat|collatzSteps|i64|i64:{n}|{Repeat.collatzSteps n}"
  for k in [1, 2, 7, 1000] do
    for x in [0, 1, 999, 18446744073709551615] do
      IO.println s!"repeat|firstMultiple|i64|i64:{k} i64:{x}|{Repeat.firstMultiple k x}"
  IO.println s!"repeat|firstMultiple|i64|i64:0 i64:0|{Repeat.firstMultiple 0 0}"
  for a in [2.0, 0.0, 1e10, 0.25, 0.0 / 0.0, -1.0, 1.0 / 0.0, 1e-300] do
    IO.println s!"repeat|newtonSqrt|f64|{floatArg a}|{(Repeat.newtonSqrt a).toBits}"
  for xs in arrays do
    let a := arrayArg xs
    for limit in [0, 50, 1000000] do
      for count in [0, 3, 100] do
        let r := arrayOut (Repeat.below xs limit count)
        IO.println s!"repeat|below|array-u64|{a} i64:{limit} i64:{count}|{r}|2"
    for v in [0, 1, 7] do
      IO.println s!"repeat|clearUntil|array-u64|{a} i64:{v}|{arrayOut (Repeat.clearUntil xs v)}|1|1"
  for h0 in [10.0, 0.0, -1.0, 100.0] do
    for dt in [0.01, 0.1] do
      let f := Repeat.fall h0 dt
      let r := s!"{f.height.toBits} {f.speed.toBits} {f.steps}"
      IO.println s!"repeat|fall|list:f64,f64,i64|{floatArg h0} {floatArg dt}|{r}"
  for xs in arrays.take 3 do
    let (ys, n) := Repeat.countUp xs
    IO.println s!"repeat|countUp|list:array-u64,i64|{arrayArg xs}|{arrayOut ys} {n}|1"
    IO.println s!"repeat|rest|i64|{arrayArg xs}|{Repeat.rest xs}"
  for k in [0, 7] do
    IO.println s!"repeat|sumTo|i64|i64:{k}|{Repeat.sumTo k}"
    IO.println s!"repeat|fallSteps|i64|i64:{k}|{Repeat.fallSteps k}"
  for x in [0, 5, 18446744073709551615] do
    IO.println s!"repeat|offset|i64|i64:{x}|{Repeat.offset x}"
  -- `firstOfCopy` reads past the end of an empty array, which native Lean reports.
  for xs in arrays.filter (·.size > 0) do
    IO.println s!"owned|firstOfCopy|i64|{arrayArg xs}|{Owned.firstOfCopy xs}|0"
