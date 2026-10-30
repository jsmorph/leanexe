import Library.Numerics.Bounds.Program
import Library.Numerics.Limiters.Minmod.Program
import Library.Numerics.Reductions.Word.Program
import Library.Numerics.Statistics.Mean.Program
import Library.Numerics.Statistics.SumSquares.Program
import Library.Random.SplitMix64.Program
import Library.Arrays.Search.Program
import TestSupport.Host
import TestSupport.Modules.Gcd

namespace TestSupport.LibraryCases

open TestSupport.Host Library.Numerics.Bounds

private def checked (name : String) (args : List String) (result : Checked) : IO Unit :=
  line "libbounds" name "list:i64,f64" args s!"{result.status} {result.value.toBits}"

/-- The seeds of the SplitMix64 cases: 0, 1, and four words whose advance wraps or reaches zero, 40
arbitrary words, and 50 successive states from 0. -/
private def splitMixSeeds : List UInt64 :=
  let gamma : UInt64 := 0x9e3779b97f4a7c15
  let chain := (List.range 50).foldl (fun (s, acc) _ =>
    let next := (Library.Random.SplitMix64.splitMix s).1
    (next, acc ++ [next])) ((0 : UInt64), ([] : List UInt64))
  [0, 1, 9223372036854775808, maxU, gamma, 0 - gamma] ++ (List.range 40).map rw ++ chain.2

def cases : IO Unit := do
  for xs in wordArrays do
    let values := xs.toArray
    line "libwordreductions" "productArray" "i64" [arrU xs]
      (toString (Library.Numerics.Reductions.Word.productArray values))
    line "libwordreductions" "xorArray" "i64" [arrU xs]
      (toString (Library.Numerics.Reductions.Word.xorArray values))
    for count in [0, xs.length.toUInt64, xs.length.toUInt64 + 1] do
      line "libsearch" "firstZero" "i64" [arrU xs, u count]
        (toString (Library.Arrays.Search.firstZero values count))
  for a in specialFloats do
    for up in [false, true] do
      let direction := u (if up then 1 else 0)
      checked "endpoint" [direction, fl a] (endpoint up a)
      checked "outSqrt" [direction, fl a] (outSqrt up a)
      for b in specialFloats do
        let args := [direction, fl a, fl b]
        checked "outAdd" args (outAdd up a b)
        checked "outSub" args (outSub up a b)
        checked "outMul" args (outMul up a b)
        checked "outDiv" args (outDiv up a b)
    for b in specialFloats do
      line "libminmod" "minmod" "f64" [fl a, fl b]
        (toString (Library.Numerics.Limiters.Minmod.minmod a b).toBits)
  -- The verified modules of the LeanExe compiler's library programs, against the specification
  -- of `gcd` and the Lean definitions of the others, with the allocation counters.
  for (a, b) in Library.Numerics.Arithmetic.Gcd.gcdPairs do
    IO.println s!"gcd|gcd|i64|{u a} {u b}|{Library.Numerics.Arithmetic.Gcd.expected (a, b)}|0|0"
  for xs in floatArrays do
    let values := xs.toArray
    IO.println s!"mean|mean|f64|{arrF xs}|\
      {(Library.Numerics.Statistics.Mean.mean values).toBits}|1|1"
    IO.println s!"sumSquares|sumSquares|f64|{arrF xs}|\
      {(Library.Numerics.Statistics.SumSquares.sumSquares values).toBits}|1|1"
  for x in splitMixSeeds do
    let (s, w) := Library.Random.SplitMix64.splitMix x
    IO.println s!"prng|splitMix|list:i64,i64|{u x}|{s} {w}|0|0"
    IO.println s!"prng|unitFloat|f64|{u x}|{(Library.Random.SplitMix64.unitFloat x).toBits}|0|0"

end TestSupport.LibraryCases
