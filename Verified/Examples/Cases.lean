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
import Verified.Examples.Enums
import Verified.Examples.Recursion
import Verified.Examples.Fields
import Verified.Examples.Trig
import Verified.Examples.Fourier
import Verified.Examples.Insert
import Verified.Examples.Clob
import Verified.Examples.Tables
import Verified.Examples.Exp

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

/-! Order books for `Clob`: books of up to eight levels with descending prices, mismatched sides,
and a level of the largest size, with command streams of the three kinds near the book's prices. -/

def clobBelow (n i : Nat) : UInt64 := UInt64.ofNat ((i * 2654435761 + 7) % n)

def clobBook (n top seed : Nat) : Array UInt64 × Array UInt64 :=
  ((List.range n).toArray.map fun k => UInt64.ofNat (top - 3 * k - (seed + k) % 3),
    (List.range n).toArray.map fun k => 1 + clobBelow 20 (seed + 5 * k))

def clobBooks : List (Array UInt64 × Array UInt64) :=
  [(#[], #[]), (#[100], #[5]), (#[105, 102, 101, 100, 98], #[4, 4, 6, 7, 10]), (#[100, 98], #[5]),
    (#[100], #[5, 6]), (#[100, 99], #[18446744073709551615, 2])] ++
    (List.range 30).map fun i => clobBook (i % 9) (200 + 7 * i) i

/-- An output array of up to two words, to which `stepCommand` and `runOut` append. -/
def clobOutputs (i : Nat) : Array UInt64 :=
  (List.range (i % 3)).toArray.map fun k => UInt64.ofNat (7 + k)

def clobCommands (ps : Array UInt64) (count seed : Nat) : Array UInt64 :=
  ((List.range count).flatMap fun j =>
    let near := if ps.isEmpty then 100 else ps[(seed + j) % ps.size]!
    [clobBelow 3 (seed + 7 * j), if (seed + j) % 4 = 0 then near + 1 else near,
      1 + clobBelow 9 (seed + 3 * j)]).toArray

def pairOut (r : Array UInt64 × Array UInt64) : String := s!"{arrayOut r.1} {arrayOut r.2}"

def tripleOut (r : Array UInt64 × Array UInt64 × Array UInt64) : String :=
  s!"{arrayOut r.1} {arrayOut r.2.1} {arrayOut r.2.2}"

/-! The host's words for enumerations and a calculator, by their `Flat` instances. -/

open Enums in
def opWord (o : Op) : UInt64 := LeanExe.Pipeline.Flat.flat o

open Enums in
def phaseWord (p : Phase) : UInt64 := LeanExe.Pipeline.Flat.flat p

open Enums in
def calcArg (c : Calc) : String := s!"i64:{c.value} i64:{c.steps} i64:{opWord c.last}"

open Enums in
def calcOut (c : Calc) : String := s!"{c.value} {c.steps} {opWord c.last}"

open Enums in
def allOps : List Op := [.add, .sub, .mul, .neg]

open Enums in
def allPhases : List Phase := [.solid, .liquid, .gas]

/-- Words for `Float.ofBits`: NaN patterns with either sign and a signaling one, both
infinities, both zeros, the smallest subnormal, and words. -/
def floatWords : List UInt64 :=
  [0x7FF0000000000001, 0x7FF8000000000001, 0xFFF8000000000000, 0xFFFFFFFFFFFFFFFF,
    0x7FF0000000000000, 0xFFF0000000000000, 0x8000000000000000, 0x3FF0000000000000] ++ words

/-- The host's arguments and output for a `Fields.Book`: its tuple's arrays and word. -/
def bookArg (b : Fields.Book) : String :=
  s!"{arrayArg b.prices} {arrayArg b.sizes} i64:{b.fills}"

def bookOut (b : Fields.Book) : String := s!"{arrayOut b.prices} {arrayOut b.sizes} {b.fills}"

/-- The words of an array of `Fields.Cell`s: each cell's level bits and count. -/
def fieldCellWords (cs : Array Fields.Cell) : Array UInt64 :=
  cs.flatMap fun c => #[c.level.toBits, c.count]

/-- The host's arguments and output for a `Fields.Grid`: its cells' words, time, and steps. -/
def gridArg (g : Fields.Grid) : String :=
  s!"{arrayArg (fieldCellWords g.cells)} {floatArg g.time} i64:{g.steps}"

def gridOut (g : Fields.Grid) : String :=
  s!"{arrayOut (fieldCellWords g.cells)} {g.time.toBits} {g.steps}"

/-- Arguments for `Trig.sin` and `Trig.cos`: zeros, infinities, NaN, the smallest subnormal, the
doubles at and around the high words where fdlibm's branches change, the doubles next to
`k · π/2` for `k` up to 8, large arguments up to the largest double, among them the double closest
to a multiple of `π/2`, hashed values spread over the exponents from `2 ^ -30` to `2 ^ 21` and from
there to the largest double, and the negatives of all of these. -/
def trigArgs : List Float :=
  let special := [0.0, 1.0 / 0.0, 0.0 / 0.0, Float.ofBits 1, Float.ofBits 0x000FFFFFFFFFFFFF,
    1.0, 2.0, 3.0, 0.5, 1e6, 1e7, 1e22, 1e300, Float.ofBits 0x7FEFFFFFFFFFFFFF,
    Float.ofBits (((1872 : UInt64) <<< (52 : UInt64)) ||| (6381956970095103 - 4503599627370496))]
  let highWords : List UInt64 := [0x3e46a09e, 0x3e500000, 0x3fe921fb, 0x4002d97c, 0x400f6a7a,
    0x4012d97c, 0x4015fdbc, 0x401921fb, 0x401c463b, 0x413921fb]
  let thresholds := highWords.flatMap fun w =>
    [Float.ofBits (w <<< (32 : UInt64)), Float.ofBits ((w <<< (32 : UInt64)) ||| 0xFFFFFFFF),
      Float.ofBits ((w + 1) <<< (32 : UInt64))]
  let multiples := (List.range 8).flatMap fun k =>
    let b := ((UInt64.ofNat (k + 1)).toFloat * 1.5707963267948966).toBits
    [b - 2, b - 1, b, b + 1, b + 2].map Float.ofBits
  let hashed := (List.range 200).map fun i =>
    let h := (UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15
    let e : UInt64 := 993 + (h >>> (58 : UInt64)) % 52
    Float.ofBits ((e <<< (52 : UInt64)) ||| (h &&& 0xFFFFFFFFFFFFF))
  let huge := (List.range 100).map fun i =>
    let h := (UInt64.ofNat i + 3) * 0xbf58476d1ce4e5b9
    let e : UInt64 := 1044 + (h >>> (52 : UInt64)) % 1003
    Float.ofBits ((e <<< (52 : UInt64)) ||| (h &&& 0xFFFFFFFFFFFFF))
  let all := special ++ thresholds ++ multiples ++ hashed ++ huge
  all ++ all.map (- ·)

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
    let (t1, t2, t3) := Pairs.triple a
    IO.println s!"pairs|triple|list:i64,i64,i64|i64:{a}|{t1} {t2} {t3}"
    IO.println s!"pairs|sumTriple|i64|i64:{a}|{Pairs.sumTriple a}"
    IO.println s!"pairs|leftNested|i64|i64:{a} i64:{b}|{Pairs.leftNested a b}"
    IO.println s!"pairs|skipMiddle|i64|i64:{a}|{Pairs.skipMiddle a}"
    IO.println s!"pairs|keepPair|i64|i64:{a}|{Pairs.keepPair a}"
    IO.println s!"pairs|literalTwice|i64|i64:{a} i64:{b}|{Pairs.literalTwice a b}"
    IO.println s!"pairs|literalCall|i64|i64:{a} i64:{b}|{Pairs.literalCall a b}"
  for xs in arrays do
    IO.println s!"pairs|sizesOf|i64|{arrayArg xs}|{Pairs.sizesOf xs}"
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
  -- The order book.
  let two := "list:array-u64,array-u64"
  let three := "list:array-u64,array-u64,array-u64"
  for (i, (p, s)) in (List.range clobBooks.length).zip clobBooks do
    let (ap, as) := (arrayArg p, arrayArg s)
    let q := clobBelow 60 i
    let (filled, cost) := Clob.marketBuy p s q
    IO.println s!"clob|marketBuy|list:i64,i64|{ap} {as} i64:{q}|{filled} {cost}"
    for k in [0, p.size / 2, p.size, p.size + 2].map UInt64.ofNat do
      let a := clobBelow 8 (i + k.toNat)
      IO.println s!"clob|fillLevel|array-u64|{as} i64:{k} i64:{a}|{arrayOut (Clob.fillLevel s k a)}"
      let r := arrayOut (Clob.fillTwice s k a 1)
      IO.println s!"clob|fillTwice|array-u64|{as} i64:{k} i64:{a} i64:1|{r}"
      IO.println s!"clob|fillKeep|{two}|{as} i64:{k} i64:{a}|{pairOut (Clob.fillKeep s k a)}"
      let r := pairOut (Clob.insertLevel p s k 97 3)
      IO.println s!"clob|insertLevel|{two}|{ap} {as} i64:{k} i64:97 i64:3|{r}"
      IO.println s!"clob|setLevel|{two}|{ap} {as} i64:{k} i64:9|{pairOut (Clob.setLevel p s k 9)}"
      IO.println s!"clob|removeLevel|{two}|{ap} {as} i64:{k}|{pairOut (Clob.removeLevel p s k)}"
    let top := if p.isEmpty then [] else [p[0]!, p[p.size - 1]!, p[0]! + 1]
    for price in [0, 99, 100, 150, 18446744073709551615] ++ top do
      IO.println s!"clob|findLevel|i64|{ap} i64:{price}|{Clob.findLevel p price}"
      IO.println s!"clob|depth|i64|{ap} {as} i64:{price}|{Clob.depth p s price}"
      let r := pairOut (Clob.addBid p s price 4)
      IO.println s!"clob|addBid|{two}|{ap} {as} i64:{price} i64:4|{r}"
      let c := clobBelow 12 (i + price.toNat)
      let r := pairOut (Clob.cancelBid p s price c)
      IO.println s!"clob|cancelBid|{two}|{ap} {as} i64:{price} i64:{c}|{r}"
      for kind in [0, 1, 2] do
        let r := pairOut (Clob.applyCommand p s kind price 5)
        IO.println s!"clob|applyCommand|{two}|{ap} {as} i64:{kind} i64:{price} i64:5|{r}"
        let o := clobOutputs i
        let r := tripleOut (Clob.stepCommand p s o kind price 5)
        let args := s!"{ap} {as} {arrayArg o} i64:{kind} i64:{price} i64:5"
        IO.println s!"clob|stepCommand|{three}|{args}|{r}"
    -- Command streams, the last with a trailing partial command, which the runs ignore.
    for cs in [0, 1, 4, 13].map (clobCommands p · i) ++ [clobCommands p 2 i ++ #[0, 5]] do
      let o := clobOutputs i
      let r := pairOut (Clob.runCommands p s cs)
      IO.println s!"clob|runCommands|{two}|{ap} {as} {arrayArg cs}|{r}"
      let r := tripleOut (Clob.runOut p s o cs)
      IO.println s!"clob|runOut|{three}|{ap} {as} {arrayArg o} {arrayArg cs}|{r}"
  -- `exp` over its whole range, at its thresholds, and at the special values.
  let expArgs := floats ++ [-746.0, -745.2, -740.0, -708.5, -708.3, -100.0, -1.0, -0.5, 1e-20,
    -1e-20, 0.5, 1.0, 2.0, 10.0, 100.0, 511.9, 512.0, 600.0, 709.7, 709.8, 710.0, 1023.0,
    1024.0] ++ (List.range 300).map fun i => -750.0 + i.toFloat * 4.9
  for x in expArgs do
    IO.println s!"exp|exp|f64|{floatArg x}|{(Exp.exp x).toBits}"
  -- Constant tables, read in range and past the end, and an update of an owned array from one.
  for k in [0, 1, 3, 5, 7, 8, 100, 18446744073709551615] do
    IO.println s!"tables|square|i64|i64:{k}|{Tables.square k}"
    IO.println s!"tables|sum|i64|i64:{k}|{Tables.sum k}"
    for xs in arrays do
      let r := arrayOut (Tables.setSquare xs k)
      IO.println s!"tables|setSquare|array-u64|{arrayArg xs} i64:{k}|{r}|1|1"
  -- Insertions and removals, out of range as well.
  for xs in arrays do
    let a := arrayArg xs
    for i in [0, 1, 2, 5, 11, 12, 13, 99, 100, 101, 18446744073709551615] do
      let r := arrayOut (Insert.insertParam xs i 7)
      IO.println s!"insert|insertParam|array-u64|{a} i64:{i} i64:7|{r}|1|2"
      IO.println s!"insert|eraseParam|array-u64|{a} i64:{i}|{arrayOut (Insert.eraseParam xs i)}|1|1"
    let bound := 3 + Nat.log2 (xs.size + 1)
    IO.println s!"insert|sortInsert|array-u64|{a}|{arrayOut (Insert.sortInsert xs)}|2|{bound}"
    for v in [0, 1, 5, 255] do
      IO.println s!"insert|removeAll|array-u64|{a} i64:{v}|{arrayOut (Insert.removeAll xs v)}|1|1"
  for n in [0, 1, 3, 10] do
    for i in [0, 1, 2, 3, 9, 10, 11, 18446744073709551615] do
      let r := arrayOut (Insert.insertBuilt n i 7)
      IO.println s!"insert|insertBuilt|array-u64|i64:{n} i64:{i} i64:7|{r}|1|2"
      let r := arrayOut (Insert.eraseBuilt n i)
      IO.println s!"insert|eraseBuilt|array-u64|i64:{n} i64:{i}|{r}|1|1"
      let (k1, k2) := Insert.insertKeep n i 7
      let kinds := "list:array-u64,array-u64"
      IO.println s!"insert|insertKeep|{kinds}|i64:{n} i64:{i} i64:7|{arrayOut k1} {arrayOut k2}|2|2"
      let t := Insert.pointTotal n i 2.5 9
      IO.println s!"insert|pointTotal|i64|i64:{n} i64:{i} {floatArg 2.5} i64:9|{t}|0|2"
  for us in conservedArrays do
    let a := arrayArg (conservedWords us)
    let u : Records.Conserved := ⟨4.0, -0.0, 0.0 / 0.0⟩
    for i in [0, 1, 2, 3, 4, 10, 11, 18446744073709551615] do
      let r := arrayOut (conservedWords (Insert.insertConserved us i u))
      IO.println s!"insert|insertConserved|array-u64|{a} i64:{i} {conservedArg u}|{r}|1|2"
      let r := arrayOut (conservedWords (Insert.eraseConserved us i))
      IO.println s!"insert|eraseConserved|array-u64|{a} i64:{i}|{r}|1|1"
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
  for op in allOps do
    for (a, b) in [((5 : UInt64), (3 : UInt64)), (0, 1), (18446744073709551615, 2)] do
      IO.println s!"enums|apply|i64|i64:{opWord op} i64:{a} i64:{b}|{Enums.apply op a b}"
    for op2 in allOps do
      let args := s!"i64:{opWord op} i64:{opWord op2}"
      IO.println s!"enums|same|i64|{args}|{bit (Enums.same op op2)}"
      IO.println s!"enums|differ|i64|{args}|{bit (Enums.differ op op2)}"
    for c in [(⟨7, 2, .mul⟩ : Enums.Calc), ⟨0, 0, .add⟩] do
      let r := calcOut (Enums.step c op 3)
      IO.println s!"enums|step|list:i64,i64,i64|{calcArg c} i64:{opWord op} i64:3|{r}"
    let c : Enums.Calc := ⟨10, 1, op⟩
    IO.println s!"enums|lastOp|i64|{calcArg c}|{opWord (Enums.lastOp c)}"
    IO.println s!"enums|undo|i64|{calcArg c}|{Enums.undo c}"
    IO.println s!"enums|opCode|i64|i64:{opWord op}|{Enums.opCode op}"
    let (t, n) := Enums.tagged op 41
    IO.println s!"enums|tagged|list:i64,i64|i64:{opWord op} i64:41|{opWord t} {n}"
    for op2 in allOps do
      let args := s!"i64:{opWord op} i64:{opWord op2}"
      IO.println s!"enums|notSame|i64|{args}|{bit (Enums.notSame op op2)}"
      IO.println s!"enums|ifDiffer|i64|{args} i64:9|{Enums.ifDiffer op op2 9}"
      IO.println s!"enums|combine|i64|{args}|{Enums.combine op op2}"
  for t in [0.0, 273.15, 300.0, 373.15, 500.0, -1.0 / 0.0, 0.0 / 0.0] do
    IO.println s!"enums|phaseOf|i64|{floatArg t}|{phaseWord (Enums.phaseOf t)}"
    IO.println s!"enums|phaseHeat|f64|{floatArg t}|{(Enums.phaseHeat t).toBits}"
  for p in allPhases do
    IO.println s!"enums|isGas|i64|i64:{phaseWord p}|{bit (Enums.isGas p)}"
    IO.println s!"enums|heat|f64|i64:{phaseWord p}|{(Enums.heat p).toBits}"
    for k in [0, 3] do
      IO.println s!"enums|cool|i64|i64:{phaseWord p} i64:{k}|{phaseWord (Enums.cool p k)}"
  for (x, y) in [((0 : UInt64), (0 : UInt64)), (1, 2),
      (18446744073709551615, 18446744073709551615)] do
    IO.println s!"enums|wordsDiffer|i64|i64:{x} i64:{y}|{bit (Enums.wordsDiffer x y)}"
  IO.println s!"enums|onlyWord|i64|i64:0|{Enums.onlyWord .only}"
  for l in [Enums.Level.low, .high] do
    let w : UInt64 := LeanExe.Pipeline.Flat.flat l
    IO.println s!"enums|raise|i64|i64:{w}|{(LeanExe.Pipeline.Flat.flat (Enums.raise l) : UInt64)}"
    IO.println s!"enums|isHigh|i64|i64:{w}|{bit (Enums.isHigh l)}"
  for w in [0, 1, 2, 3, 4, 18446744073709551615] do
    IO.println s!"enums|ofWord|i64|i64:{w}|{opWord (Enums.ofWord w)}"
  let opArrays : List (Array Enums.Op) :=
    [#[], #[.add], #[.add, .mul, .sub, .neg],
      (Array.range 10).map fun i => Enums.ofWord (i % 4).toUInt64]
  for ops in opArrays do
    for xs in arrays.take 4 do
      let args := s!"{arrayArg (ops.map opWord)} {arrayArg xs}"
      IO.println s!"enums|run|list:i64,i64,i64|{args}|{calcOut (Enums.run ops xs)}|2"
  for ts in floatArrays ++ [#[250.0, 300.0, 400.0, 373.15, 273.15]] do
    let ps := Enums.phases ts
    IO.println s!"enums|phases|array-u64|{floatArrayArg ts}|{arrayOut (ps.map phaseWord)}|2"
    let a := arrayArg (ps.map phaseWord)
    IO.println s!"enums|countGas|i64|{a}|{Enums.countGas ps}|1"
    IO.println s!"enums|firstPhase|i64|{a}|{phaseWord (Enums.firstPhase ps)}|1"
    for i in [0, 1, 5, 18446744073709551615] do
      let r := arrayOut ((Enums.melt ps i).map phaseWord)
      IO.println s!"enums|melt|array-u64|{a} i64:{i}|{r}|1|1"
  -- `firstOfCopy` reads past the end of an empty array, which native Lean reports.
  for xs in arrays.filter (·.size > 0) do
    IO.println s!"owned|firstOfCopy|i64|{arrayArg xs}|{Owned.firstOfCopy xs}|0"
  for a in words do
    for b in words do
      IO.println s!"recursion|gcd|i64|i64:{a} i64:{b}|{Recursion.gcd a b}"
      IO.println s!"recursion|pow|i64|i64:{a} i64:{b}|{Recursion.pow a b}"
      IO.println s!"recursion|powGcd|i64|i64:{a} i64:{b}|{Recursion.powGcd a b}"
  -- Consecutive Fibonacci numbers make Euclid's algorithm take the most steps.
  for (a, b) in [((12200160415121876738 : UInt64), (7540113804746346429 : UInt64)),
      (7540113804746346429, 12200160415121876738)] do
    IO.println s!"recursion|gcd|i64|i64:{a} i64:{b}|{Recursion.gcd a b}"
  for xs in floatArrays do
    for (lo, hi) in [((0 : UInt64), xs.size.toUInt64), (1, 3), (2, 5), (3, 3), (0, 0),
        (18446744073709551615, 1)] do
      let r := (Recursion.sumRange xs lo hi).toBits
      IO.println s!"recursion|sumRange|f64|{floatArrayArg xs} i64:{lo} i64:{hi}|{r}|1"
  for xs in arrays.take 4 do
    for (i, n) in [((0 : UInt64), (0 : UInt64)), (0, 5), (3, 10), (7, 2), (0, 300)] do
      let r := arrayOut (Recursion.fill xs i n)
      IO.println s!"recursion|fill|array-u64|{arrayArg xs} i64:{i} i64:{n}|{r}|1"
  for n in [0, 1, 2, 500, 999] do
    IO.println s!"recursion|chain|i64|i64:{n}|{Recursion.chain n}"
  for n in [1000, 1001, 18446744073709551615] do
    IO.println s!"recursion|chain|i64|i64:{n}|trap"
  for (a, b) in [((0 : UInt64), (1 : UInt64)), (5, 8), (18446744073709551615, 2)] do
    for k in [0, 1, 2, 10, 93, 200, 999] do
      let (x, y) := Recursion.fibPair (a, b) k
      IO.println s!"recursion|fibPair|list:i64,i64|i64:{a} i64:{b} i64:{k}|{x} {y}"
      let p := Recursion.walk ⟨a, b⟩ k
      IO.println s!"recursion|walk|list:i64,i64|i64:{a} i64:{b} i64:{k}|{p.x} {p.y}"
  for (a, b) in [((0 : UInt64), (1 : UInt64)), (5, 8)] do
    IO.println s!"recursion|fibPair|list:i64,i64|i64:{a} i64:{b} i64:1000|trap"
  let pointArrays : List (Array Recursion.Point) :=
    [#[], #[⟨3, 4⟩], #[⟨1, 2⟩, ⟨18446744073709551615, 0⟩, ⟨5, 5⟩],
      (Array.range 60).map fun i => ⟨i.toUInt64 * 7, i.toUInt64⟩]
  for ps in pointArrays do
    let a := arrayArg (ps.flatMap fun p => #[p.x, p.y])
    for i in [0, 1, 2, 59, 60, 18446744073709551615] do
      IO.println s!"recursion|sumXs|i64|{a} i64:{i}|{Recursion.sumXs ps i}|1"
  for (a, b) in [((1 : UInt64), (2 : UInt64)), (18446744073709551615, 3)] do
    IO.println s!"recursion|top1|i64|i64:{a} i64:{b}|{Recursion.top1 a b}"
    for n in [0, 1, 998, 999] do
      IO.println s!"recursion|deep|i64|i64:{n} i64:{a} i64:{b}|{Recursion.deep n a b}"
    IO.println s!"recursion|deep|i64|i64:1000 i64:{a} i64:{b}|trap"
  let bookKinds := "array-u64,array-u64,i64"
  let books : List Fields.Book :=
    [⟨#[], #[], 0⟩, ⟨#[5], #[3], 1⟩, Fields.mkBook 4, ⟨#[1, 2, 3], #[10], 7⟩]
  for n in [0, 1, 5] do
    IO.println s!"fields|mkBook|list:{bookKinds}|i64:{n}|{bookOut (Fields.mkBook n)}|2"
  for b in books do
    IO.println s!"fields|bookTotal|i64|{bookArg b}|{Fields.bookTotal b}|2"
    IO.println s!"fields|bookValue|i64|{bookArg b}|{Fields.bookValue b}|2"
    IO.println s!"fields|bookShape|i64|{bookArg b}|{Fields.bookShape b}|2"
    let (b', t) := Fields.withTotal b
    IO.println s!"fields|withTotal|list:{bookKinds},i64|{bookArg b}|{bookOut b'} {t}|4"
    for (i, q) in [((0 : UInt64), (9 : UInt64)), (2, 4), (100, 1)] do
      let r := bookOut (Fields.fillOrder b i q)
      IO.println s!"fields|fillOrder|list:{bookKinds}|{bookArg b} i64:{i} i64:{q}|{r}|4"
    for c in [true, false] do
      let other := Fields.mkBook 2
      let r := bookOut (Fields.pickBook c b other)
      IO.println s!"fields|pickBook|list:{bookKinds}|{boolArg c} {bookArg b} {bookArg other}|{r}|6"
  let grids : List Fields.Grid :=
    [⟨#[], 0.0, 0⟩, ⟨#[⟨1.5, 2⟩], 0.25, 3⟩,
      ⟨(Array.range 5).map fun i => ⟨i.toUInt64.toFloat, i.toUInt64⟩, -1.0, 7⟩]
  for g in grids do
    for (k, dt) in [((0 : UInt64), (0.5 : Float)), (1, 0.5), (7, 0.125), (100, 1e-3)] do
      let r := gridOut (Fields.advance g k dt)
      IO.println s!"fields|advance|list:array-u64,f64,i64|{gridArg g} i64:{k} {floatArg dt}|{r}|2|2"
    IO.println s!"fields|gridLevel|f64|{gridArg g}|{(Fields.gridLevel g).toBits}|1"
    let cells := arrayOut (fieldCellWords (Fields.gridCells g))
    IO.println s!"fields|gridCells|array-u64|{gridArg g}|{cells}|2"
    for label in [(0 : UInt64), 5] do
      let w : Fields.World := ⟨g, label⟩
      IO.println s!"fields|worldLevel|f64|{gridArg g} i64:{label}|{(Fields.worldLevel w).toBits}|1"
      let w' := Fields.relabel w 3
      let r := s!"{gridOut w'.grid} {w'.label}"
      IO.println s!"fields|relabel|list:array-u64,f64,i64,i64|{gridArg g} i64:{label} i64:3|{r}|2"
  for x in trigArgs do
    IO.println s!"trig|sin|f64|{floatArg x}|{(Trig.sin x).toBits}"
    IO.println s!"trig|cos|f64|{floatArg x}|{(Trig.cos x).toBits}"
  for xs in floatArrays ++ [0, 1, 2, 3, 4, 5, 7, 8, 12, 16, 31, 64, 100].map (Fourier.signal · 1) do
    let a := floatArrayArg xs
    IO.println s!"fourier|dft|array-u64|{a}|{floatArrayOut (Fourier.dft xs)}|2|3"
    IO.println s!"fourier|inverse|array-u64|{a}|{floatArrayOut (Fourier.inverse xs)}|2|3"
    let p := floatArrayOut (Fourier.powerSpectrum xs)
    IO.println s!"fourier|powerSpectrum|array-u64|{a}|{p}|2|5"
  for n in [(1 : UInt64), 2, 3, 4, 8, 12, 360, 1000] do
    for m in [0, 1, n / 8, n / 4, n / 2, n - 1, n, 3 * n + 1] do
      let (c, s) := Fourier.twiddle n m
      IO.println s!"fourier|twiddle|list:f64,f64|i64:{n} i64:{m}|{c.toBits} {s.toBits}"
