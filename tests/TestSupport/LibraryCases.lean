import Library.Numerics.Bounds.Program
import Library.Numerics.Interval.Program
import Library.Numerics.Limiters.Minmod.Program
import Library.Numerics.Reductions.Word.Program
import Library.Numerics.Statistics.Mean.Program
import Library.Numerics.Statistics.SumSquares.Program
import Library.Random.SplitMix64.Program
import Library.Arrays.Search.Program
import TestSupport.Host
import Library.Combinatorics.DancingLinks.Count
import TestSupport.Modules.BinaryGcd
import TestSupport.Modules.BinaryHeap
import TestSupport.Modules.BinarySearch
import TestSupport.Modules.DancingLinks
import TestSupport.Modules.Gcd
import TestSupport.Modules.Heapsort
import TestSupport.Modules.LinearProbing
import TestSupport.Modules.MergeSort
import TestSupport.Modules.MillerRabin
import TestSupport.Modules.ModInverse
import TestSupport.Modules.MultiPrecision
import TestSupport.Modules.StraightInsertion
import TestSupport.Modules.Quicksort
import TestSupport.Modules.Shellsort
import TestSupport.Modules.RadixSort
import TestSupport.Modules.Find
import TestSupport.Modules.PrimeFactors
import TestSupport.Modules.Sieve
import TestSupport.Modules.Sampling
import TestSupport.Modules.TopologicalSort
import TestSupport.Modules.UnionFind
import TestSupport.Modules.WeightedUnionFind
import TestSupport.Modules.Kmp
import TestSupport.Modules.Dijkstra
import TestSupport.Modules.TreeSearch
import TestSupport.Modules.Avl
import TestSupport.Modules.AvlDelete
import TestSupport.Modules.NextPermutation
import TestSupport.Modules.Int64Text

namespace TestSupport.LibraryCases

open TestSupport.Host Library.Numerics.Bounds

private def checked (name : String) (args : List String) (result : Checked) : IO Unit :=
  line "libbounds" name "list:i64,f64" args s!"{result.status} {result.value.toBits}"

private abbrev Interval := Library.Numerics.Interval.Interval

private def interval (name : String) (args : List String) (result : Interval) : IO Unit :=
  line "libinterval" name "list:i64,f64,f64" args
    s!"{result.status} {result.lo.toBits} {result.hi.toBits}"

private def intervalChecked (name : String) (args : List String) (result : Checked) : IO Unit :=
  line "libinterval" name "list:i64,f64" args s!"{result.status} {result.value.toBits}"

private def intervalArgs (a : Interval) : List String := [u a.status, fl a.lo, fl a.hi]

private def checkedArgs (c : Checked) : List String := [u c.status, fl c.value]

/-- Accepted intervals of both signs, points, intervals at the ends of the finite range, a
rejected interval, and records with a nonfinite endpoint or with `lo > hi`, which only a caller
that skips `make` can build. -/
private def intervals : List Interval :=
  [⟨0, 1.0, 2.0⟩, ⟨0, -2.0, -1.0⟩, ⟨0, -1.0, 3.0⟩, ⟨0, 0.0, 0.0⟩, ⟨0, -0.0, 0.5⟩,
    ⟨0, 1e308, 1e308⟩, ⟨0, -1e308, 1e308⟩, ⟨0, 5e-324, 5e-324⟩, ⟨0, -5e-324, 5e-324⟩,
    ⟨0, 0.1, 0.1⟩, ⟨0, 1e-200, 1e200⟩, ⟨0, 7.25, 7.25⟩, ⟨1, 0.0, 0.0⟩, ⟨0, 1.0, inf⟩,
    ⟨0, nan, 1.0⟩, ⟨0, 2.0, 1.0⟩]

private def intervalCases : IO Unit := do
  for a in specialFloats do
    interval "point" [fl a] (Library.Numerics.Interval.point a)
    for up in [false, true] do
      intervalChecked "outward2" [u (if up then 1 else 0), fl a]
        (Library.Numerics.Interval.outward2 up a)
    for b in specialFloats do
      interval "make" [fl a, fl b] (Library.Numerics.Interval.make a b)
      line "libinterval" "fmin" "f64" [fl a, fl b]
        (toString (Library.Numerics.Interval.fmin a b).toBits)
      line "libinterval" "fmax" "f64" [fl a, fl b]
        (toString (Library.Numerics.Interval.fmax a b).toBits)
  for a in intervals do
    let x := intervalArgs a
    interval "neg" x (Library.Numerics.Interval.neg a)
    interval "sqrt" x (Library.Numerics.Interval.sqrt a)
    interval "abs" x (Library.Numerics.Interval.abs a)
    interval "clamp" (x ++ [fl (-1.0), fl 1.0]) (Library.Numerics.Interval.clamp a (-1.0) 1.0)
    interval "clamp" (x ++ [fl 0.0, fl inf]) (Library.Numerics.Interval.clamp a 0.0 inf)
    interval "increasing" (x ++ [fl a.lo, fl a.hi])
      (Library.Numerics.Interval.increasing a a.lo a.hi)
    interval "decreasing" (x ++ [fl a.hi, fl a.lo])
      (Library.Numerics.Interval.decreasing a a.hi a.lo)
    for b in intervals do
      let xy := x ++ intervalArgs b
      interval "add" xy (Library.Numerics.Interval.add a b)
      interval "sub" xy (Library.Numerics.Interval.sub a b)
      interval "mul" xy (Library.Numerics.Interval.mul a b)
      interval "div" xy (Library.Numerics.Interval.div a b)
      interval "divCore" xy (Library.Numerics.Interval.divCore a b)
      for up in [false, true] do
        let direction := u (if up then 1 else 0)
        intervalChecked "mulEnd" (direction :: xy) (Library.Numerics.Interval.mulEnd up a b)
        intervalChecked "divEnd" (direction :: xy) (Library.Numerics.Interval.divEnd up a b)
        let p : Checked := ⟨a.status, a.lo⟩
        let q : Checked := ⟨0, a.hi⟩
        let r : Checked := ⟨b.status, b.lo⟩
        let s : Checked := ⟨0, b.hi⟩
        intervalChecked "extreme"
          (direction :: (checkedArgs p ++ checkedArgs q ++ checkedArgs r ++ checkedArgs s))
          (Library.Numerics.Interval.extreme up p q r s)
        interval "join" (direction :: (checkedArgs p ++ checkedArgs s))
          (Library.Numerics.Interval.join up p s)

/-- The seeds of the SplitMix64 cases: 0, 1, and four words whose advance wraps or reaches zero, 40
arbitrary words, and 50 successive states from 0. -/
private def splitMixSeeds : List UInt64 :=
  let gamma : UInt64 := 0x9e3779b97f4a7c15
  let chain := (List.range 50).foldl (fun (s, acc) _ =>
    let next := (Library.Random.SplitMix64.splitMix s).1
    (next, acc ++ [next])) ((0 : UInt64), ([] : List UInt64))
  [0, 1, 9223372036854775808, maxU, gamma, 0 - gamma] ++ (List.range 40).map rw ++ chain.2

def cases : IO Unit := do
  intervalCases
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
  -- The verified modules of the GCD, prime-factor, mean, sum-of-squares, and SplitMix64
  -- programs, against the specification of `gcd` and the Lean definitions of the others, with the
  -- allocation counters.
  for (a, b) in Library.Numerics.Arithmetic.Gcd.gcdPairs do
    IO.println s!"gcd|gcd|i64|{u a} {u b}|{Library.Numerics.Arithmetic.Gcd.expected (a, b)}|0|0"
  for (a, b) in Library.Numerics.Arithmetic.BinaryGcd.gcdInputs do
    IO.println s!"binaryGcd|binaryGcd|i64|{u a} {u b}|\
      {Library.Numerics.Arithmetic.BinaryGcd.expected (a, b)}|0|0"
  for (a, m) in Library.Numerics.Arithmetic.ModInverse.inverseInputs do
    IO.println s!"modInverse|modInverse|i64|{u a} {u m}|\
      {Library.Numerics.Arithmetic.ModInverse.expected (a, m)}|0|0"
  for xs in Library.Sorting.Heapsort.sortInputs do
    IO.println s!"heapsort|heapsort|array-u64|{arrU xs}|\
      [{", ".intercalate ((Library.Sorting.Heapsort.expected xs.toArray).toList.map toString)}]|1|1"
  for (us, xs) in Library.Random.Sampling.shuffleInputs do
    IO.println s!"sampling|shuffle|array-u64|{arrU us} {arrU xs}|\
      [{", ".intercalate ((Library.Random.Sampling.shuffle us.toArray xs.toArray).toList.map toString)}]|2|2"
  for (us, xs, n) in Library.Random.Sampling.sampleInputs do
    IO.println s!"sampling|sample|array-u64|{arrU us} {arrU xs} {u n}|\
      [{", ".intercalate ((Library.Random.Sampling.sample us.toArray xs.toArray n).toList.map toString)}]|3|3"
  for (us, xs, n) in Library.Random.Sampling.reservoirInputs do
    IO.println s!"sampling|reservoir|array-u64|{arrU us} {arrU xs} {u n}|\
      [{", ".intercalate ((Library.Random.Sampling.reservoir us.toArray xs.toArray n).toList.map toString)}]|3|3"
  for xs in Library.Sorting.StraightInsertion.insertionInputs do
    IO.println s!"straightInsertion|straightInsertion|array-u64|{arrU xs}|\
      [{", ".intercalate ((Library.Sorting.StraightInsertion.expected xs.toArray).toList.map toString)}]|1|1"
  for xs in Library.Sorting.Quicksort.quicksortInputs do
    IO.println s!"quicksort|quicksort|array-u64|{arrU xs}|\
      [{", ".intercalate ((Library.Sorting.Quicksort.expected xs.toArray).toList.map toString)}]|1|2"
  for xs in Library.Sorting.RadixSort.radixInputs do
    IO.println s!"radixSort|radixSort|array-u64|{arrU xs}|\
      [{", ".intercalate ((Library.Sorting.RadixSort.expected xs.toArray).toList.map toString)}]|1|3"
  for xs in Library.Sorting.Shellsort.shellsortInputs do
    IO.println s!"shellsort|shellsort|array-u64|{arrU xs}|\
      [{", ".intercalate ((Library.Sorting.Shellsort.expected xs.toArray).toList.map toString)}]|1|1"
  for xs in Library.Combinatorics.NextPermutation.nextPermInputs do
    let (flag, ys) := Library.Combinatorics.NextPermutation.expectedOf xs
    IO.println s!"nextPermutation|nextPerm|list:i64,array-u64|{arrU xs}|\
      {flag} [{", ".intercalate (ys.map toString)}]|1|1"
  for (xs, k) in Library.Sorting.Find.selectInputs do
    IO.println s!"find|select|i64|{arrU xs} {u k}|{Library.Sorting.Find.expected xs.toArray k}|0|1"
  for (x, t) in Library.Trees.Search.searchInputs do
    let r := Library.Trees.Search.algorithmT x t
    let n := (Library.Trees.Search.keys t).length
    let m := (Library.Trees.Search.keys r.2).length
    let tree := s!"tree-u64:{Examples.Trees.KeyTree.describe t}"
    IO.println s!"treeSearch|search|i64|{u x} {tree}|{if r.1 then 1 else 0}|{n}|{n}"
    IO.println s!"treeSearch|insert|tree-u64|{u x} {tree}|\
      {Examples.Trees.KeyTree.describe r.2}|{m}|{m}"
  for (x, t) in Library.Trees.Avl.avlInputs do
    let r := (Library.Trees.Avl.algorithmA x t).2
    let n := Library.Trees.Avl.size t
    let m := Library.Trees.Avl.size r
    let tree := s!"records-u64:{Library.Trees.Avl.describe t}"
    let found := if Library.Trees.Avl.searchA x t then 1 else 0
    IO.println s!"avlTree|search|i64|{u x} {tree}|{found}|{n}|{n}"
    IO.println s!"avlTree|insert|records-u64|{u x} {tree}|{Library.Trees.Avl.describe r}|{m}|{m}"
  for (x, t) in Library.Trees.AvlDelete.deleteInputs do
    let r := (Library.Trees.AvlDelete.deleteA x t).2
    let n := Library.Trees.Avl.size t
    let m := Library.Trees.Avl.size r
    IO.println s!"avlDelete|delete|records-u64|{u x} records-u64:{Library.Trees.Avl.describe t}|\
      {Library.Trees.Avl.describe r}|{m}|{n}"
  for xs in Library.Sorting.MergeSort.mergeInputs do
    IO.println s!"mergeSort|mergeSort|array-u64|{arrU xs}|\
      [{", ".intercalate ((Library.Sorting.MergeSort.expected xs.toArray).toList.map toString)}]"
  for xs in Library.Graphs.TopologicalSort.topoInputs do
    IO.println s!"topoSort|topoSort|array-u64|{arrU xs}|\
      [{", ".intercalate ((Library.Graphs.TopologicalSort.topoSort xs.toArray).toList.map toString)}]"
  for (n, js, ks) in Library.Graphs.UnionFind.classInputs do
    IO.println s!"unionFind|classes|array-u64|{u (UInt64.ofNat n)} {arrU js} {arrU ks}|\
      [{", ".intercalate ((Library.Graphs.UnionFind.leastLabels n js ks).map toString)}]|3|5"
  for (pw, m, tw, n) in Library.Strings.Kmp.kmpInputs do
    IO.println s!"kmp|occurrences|array-u64|{arrU pw} {u m} {arrU tw} {u n}|\
      [{", ".intercalate ((Library.Strings.Kmp.expected pw.toArray m tw.toArray n).toList.map
        toString)}]|3|4"
  for (n, s, first, heads, lens) in Library.Graphs.Dijkstra.dijkstraInputs do
    IO.println s!"dijkstra|dijkstra|array-u64|{u n} {u s} {arrU first} {arrU heads} {arrU lens}|\
      [{", ".intercalate ((Library.Graphs.Dijkstra.shortest n s first heads lens).map
        toString)}]|4|7"
  for (n, js, ks) in Library.Graphs.WeightedUnionFind.weightedInputs do
    IO.println s!"weightedUnionFind|classes|array-u64|{u (UInt64.ofNat n)} {arrU js} {arrU ks}|\
      [{", ".intercalate ((Library.Graphs.UnionFind.leastLabels n js ks).map toString)}]|3|6"
  for xs in Library.Queues.BinaryHeap.heapInputs do
    IO.println s!"heapQueue|heapQueue|array-u64|{arrU xs}|\
      [{", ".intercalate ((Library.Queues.BinaryHeap.expected xs.toArray).toList.map toString)}]"
  for xs in Library.Combinatorics.DancingLinks.countInputs do
    IO.println s!"dancingLinks|count|i64|{arrU xs}|\
      {Library.Combinatorics.DancingLinks.countRef xs.toArray}|1|2"
  for xs in Library.Combinatorics.DancingLinks.validInputs do
    IO.println s!"dancingLinks|valid|i64|{arrU xs}|\
      {Library.Combinatorics.DancingLinks.validSpec xs.toArray}|1|2"
  for (x, n, m) in Library.Numerics.Arithmetic.MillerRabin.powInputs do
    IO.println s!"millerRabin|powMod|i64|{u x} {u n} {u m}|\
      {Library.Numerics.Arithmetic.MillerRabin.powModRef (x, n, m)}|0|0"
  for (n, x) in Library.Numerics.Arithmetic.MillerRabin.testInputs do
    IO.println s!"millerRabin|test|i64|{u n} {u x}|\
      {Library.Numerics.Arithmetic.MillerRabin.testRef (n, x)}|0|0"
  for (u, v) in Library.Numerics.MultiPrecision.mpInputs do
    let fmt := fun (r : Array UInt64) => s!"[{", ".intercalate (r.toList.map toString)}]"
    IO.println s!"multiPrecision|add|array-u64|{arrU u} {arrU v}|\
      {fmt (Library.Numerics.MultiPrecision.addSpec (u.toArray, v.toArray))}"
    IO.println s!"multiPrecision|sub|array-u64|{arrU u} {arrU v}|\
      {fmt (Library.Numerics.MultiPrecision.subSpec (u.toArray, v.toArray))}"
    IO.println s!"multiPrecision|mul|array-u64|{arrU u} {arrU v}|\
      {fmt (Library.Numerics.MultiPrecision.mulSpec (u.toArray, v.toArray))}"
  for (u, v) in Library.Numerics.MultiPrecision.divInputs do
    IO.println s!"multiPrecision|divide|array-u64|{arrU u} {arrU v}|\
      [{", ".intercalate ((Library.Numerics.MultiPrecision.divSpec (u.toArray, v.toArray)).toList.map
        toString)}]"
  for xs in Library.HashTables.LinearProbing.probeInputs do
    IO.println s!"hashTable|hashTable|array-u64|{arrU xs}|\
      [{", ".intercalate ((Library.HashTables.LinearProbing.expected xs.toArray).toList.map toString)}]"
  for (xs, key) in Library.Arrays.BinarySearch.searchInputs do
    IO.println s!"binarySearch|lowerBound|i64|{arrU xs} {u key}|\
      {Library.Arrays.BinarySearch.expected (xs.toArray, key)}|1|1"
  for n in Library.Numerics.Arithmetic.Sieve.sieveInputs do
    IO.println s!"sieve|primes|array-u64|{u n}|\
      [{", ".intercalate ((Library.Numerics.Arithmetic.Sieve.expected n).toList.map toString)}]|1|2"
  for n in Library.Numerics.Arithmetic.Sieve.sieveTraps do
    IO.println s!"sieve|primes|array-u64|{u n}|trap"
  for x in Library.Numerics.Decimal.Int64Text.printInputs do
    IO.println s!"int64Text|printInt64|array-u64|{u x.toUInt64}|\
      [{", ".intercalate ((Library.Numerics.Decimal.Int64Text.expectedPrint x).toList.map
        toString)}]|1|1"
  for xs in Library.Numerics.Decimal.Int64Text.readInputs do
    let (ok, v) := Library.Numerics.Decimal.Int64Text.expectedRead xs.toArray
    IO.println s!"int64Text|readInt64|list:i64,i64|{arrU xs}|\
      {if ok then 1 else 0} {v.toUInt64}|1|1"
  for n in Library.Numerics.Arithmetic.PrimeFactors.primeFactorInputs do
    IO.println s!"primeFactors|compute|i64|{u n}|\
      {Library.Numerics.Arithmetic.PrimeFactors.expected n}|0|0"
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
