import Verified.Examples.Signed
import Examples.Floor.Program
import Examples.Floor.Cases
import TestSupport.Host

/-! The cases of the modules `signed` and `floor`: each function of `Verified.Examples.Signed`
and of `Examples.Floor` on the extremes of `Int64`, the values near 0, and arbitrary words, each
`Int64` passed and printed as its word, against native Lean. -/

namespace Verified.Examples.Signed

open TestSupport.Host

/-- The words of the cases: the extremes, the values near 0, and arbitrary words. -/
def values : List Int64 :=
  Examples.Floor.samples ++ (List.range 6).map fun i => (rw (31 * i)).toInt64

def i (x : Int64) : String := s!"i64:{x.toUInt64}"

def intsArg (xs : Array Int64) : String :=
  "array-u64:" ++ ",".intercalate (xs.toList.map fun x => toString x.toUInt64)

def intsOut (xs : Array Int64) : String :=
  "[" ++ ", ".intercalate (xs.toList.map fun x => toString x.toUInt64) ++ "]"

def arrays : List (Array Int64) := [#[], #[-1], #[Int64.minValue, 0, Int64.maxValue], #[3, -3, 7]]

def cases : IO Unit := do
  for a in values do
    for b in values do
      let args := s!"{i a} {i b}"
      IO.println s!"signed|arith|i64|{args}|{(arith a b).toUInt64}|0|0"
      IO.println s!"signed|divs|i64|{args}|{(divs a b).toUInt64}|0|0"
      IO.println s!"signed|cmps|i64|{args}|{if cmps a b then 1 else 0}|0|0"
      IO.println s!"signed|dist|i64|{args}|{(dist a b).toUInt64}|0|0"
      IO.println s!"signed|least|i64|{args}|{(least a b).toUInt64}|0|0"
      IO.println s!"signed|most|i64|{args}|{(most a b).toUInt64}|0|0"
      for c in [Int64.minValue, -1, 0, 7, Int64.maxValue] do
        IO.println s!"floor|clamp|i64|{i a} {i b} {i c}|{(Examples.Floor.clamp a b c).toUInt64}|0|0"
      IO.println s!"floor|floorDiv|i64|{args}|{(Examples.Floor.floorDiv a b).toUInt64}|0|0"
      IO.println s!"floor|average|i64|{args}|{(Examples.Floor.average a b).toUInt64}|0|0"
    IO.println s!"signed|sign|i64|{i a}|{sign a}|0|0"
    IO.println s!"signed|grow|i64|{i a}|{(grow a).toUInt64}|0|0"
    for n in ([0, 1, 5, 64] : List UInt64) do
      IO.println s!"signed|triple|i64|i64:{n} {i a}|{(triple n a).toUInt64}|0|0"
      IO.println s!"signed|walk|i64|{i a} i64:{n}|{(walk a n).toUInt64}|0|0"
    for xs in arrays do
      for k in ([0, 1, 7] : List UInt64) do
        IO.println s!"signed|update|array-u64|{intsArg xs} i64:{k} {i a}|\
          {intsOut (update xs k a)}"
      let s : Acc := ⟨a, xs⟩
      let r := addItem s a
      IO.println s!"signed|addItem|list:i64,array-u64|{i a} {intsArg xs} {i a}|\
        {r.total.toUInt64} {intsOut r.items}"
  for n in ([0, 1, 3, 10] : List UInt64) do
    IO.println s!"signed|count|array-u64|i64:{n}|{intsOut (count n)}"
  IO.println s!"signed|lits|i64||{lits.toUInt64}|0|0"

end Verified.Examples.Signed
