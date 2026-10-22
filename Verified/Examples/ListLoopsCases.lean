import Verified.Examples.ListLoops
import Examples.Trees.Cases

namespace Verified.Examples.ListLoops

open TestSupport.Host

def render (xs : List UInt64) : String := s!"[{", ".intercalate (xs.map toString)}]"

def cases : IO Unit := do
  for n in ([0, 1, 2, 7, 63, 999, 1000, 4096] : List UInt64) do
    IO.println s!"listloops|range|chain-u64|{u n}|{render (range n)}|{n}|{n}"
  for xs in wordArrays do
    for n in ([0, 1, 7, 63] : List UInt64) do
      let blocks := xs.length + n.toNat
      IO.println s!"listloops|extend|chain-u64|{u n} {chain xs}|{render (extend n xs)}|{blocks}|{blocks}"
  for xs in [[], [maxU], [0, maxU, 7]] do
    let n : UInt64 := 4096
    let blocks := xs.length + n.toNat
    IO.println s!"listloops|extend|chain-u64|{u n} {chain xs}|{render (extend n xs)}|{blocks}|{blocks}"

end Verified.Examples.ListLoops
