import Verified.Examples.Lists
import Examples.Trees.Cases

namespace Verified.Examples.Lists

open Examples.Host

def render (xs : List UInt64) : String := s!"[{", ".intercalate (xs.map toString)}]"

def cases : IO Unit := do
  IO.println s!"lists|empty|chain-u64||{render empty}|0|0"
  let lists := wordArrays ++ ([63, 999, 1000, 4096] : List Nat).map fun n =>
    (List.range n).map fun i => rw (n + i)
  for xs in lists do
    let n := xs.length
    IO.println s!"lists|keep|chain-u64|{chain xs}|{render (keep xs)}|{n}|{n}"
    IO.println s!"lists|keepViaCall|chain-u64|{chain xs}|{render (keepViaCall xs)}|{n}|{n}"
    let result := duplicate xs
    IO.println s!"lists|duplicate|list:chain-u64,chain-u64|{chain xs}|{render result.1} {render result.2}|{2 * n}|{2 * n}"
    for x in [0, 7, maxU] do
      IO.println s!"lists|cons|chain-u64|{u x} {chain xs}|{render (cons x xs)}|{n + 1}|{n + 1}"
      let y := maxU - x
      IO.println s!"lists|consTwice|chain-u64|{u x} {u y} {chain xs}|{render (consTwice x y xs)}|{n + 2}|{n + 2}"

end Verified.Examples.Lists
