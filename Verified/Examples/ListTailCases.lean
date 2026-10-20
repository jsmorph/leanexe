import Verified.Examples.ListTail
import Examples.Trees.Cases

namespace Verified.Examples.ListTail

open Examples.Host

def render (xs : List UInt64) : String := s!"[{", ".intercalate (xs.map toString)}]"

def cases : IO Unit := do
  let lists := wordArrays ++ ([999, 1000, 1001, 4096] : List Nat).map fun n =>
    (List.range n).map fun i => rw (n + i)
  for xs in lists do
    let n := xs.length
    for acc in [0, 1, maxU] do
      IO.println s!"listtail|sum|i64|{chain xs} {u acc}|{sum xs acc}|{n}|{n}"
    for acc in [[], [maxU], [0, maxU, 7]] do
      let blocks := n + acc.length
      IO.println s!"listtail|reverse|chain-u64|{chain xs} {chain acc}|{render (reverse xs acc)}|{blocks}|{blocks}"

end Verified.Examples.ListTail
