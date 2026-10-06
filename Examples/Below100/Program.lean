import LeanExe.Dialect.RepeatWhile

/-!
Main's Demo 5 in this dialect: the elements of an array of at most eight words that are less than
100, in order, or the empty array for a longer input.  `keep` takes one element: it appends the
element to the owned output when it is less than 100.  `compute` repeats `keep` over the first
`count` elements, with `count` 0 for a longer input.
-/

namespace Examples.Below100

def keep (xs : Array UInt64) (i : UInt64) (out : Array UInt64) : UInt64 × Array UInt64 :=
  let x := xs[i.toNat]!
  if x < 100 then (i + 1, out.push x) else (i + 1, out)

def compute (xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  let count := if n ≤ 8 then n else 0
  match LeanExe.repeatWhile 8 ((0 : UInt64), (#[] : Array UInt64)) (fun (i, _) => i < count)
      (fun (i, out) => keep xs i out) with
  | (_, out) => out

end Examples.Below100
