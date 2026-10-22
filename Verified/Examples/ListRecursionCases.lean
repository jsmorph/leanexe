import Verified.Examples.ListRecursion
import Examples.Trees.Cases

namespace Verified.Examples.ListRecursion

open TestSupport.Host

def render (xs : List UInt64) : String := s!"[{", ".intercalate (xs.map toString)}]"

def cases : IO Unit := do
  let lists := wordArrays ++ ([63, 998, 999] : List Nat).map fun n =>
    (List.range n).map fun i => rw (n + i)
  for xs in lists do
    let n := xs.length
    IO.println s!"listrecursion|sum|i64|{chain xs}|{sum xs}|{n}|{n}"
    IO.println s!"listrecursion|increment|chain-u64|{chain xs}|{render (increment xs)}|{n}|{n}"
  for n in [1000, 1001, 4096] do
    let xs := (List.range n).map UInt64.ofNat
    for name in ["sum", "increment"] do
      let kind := if name = "sum" then "i64" else "chain-u64"
      IO.println s!"listrecursion|{name}|{kind}|{chain xs}|trap"

end Verified.Examples.ListRecursion
