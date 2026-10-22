import Verified.Examples.TreeCopyCases

namespace Verified.Examples.TreeCore

open TestSupport.Host

def render (xs : List UInt64) : String := s!"[{", ".intercalate (xs.map toString)}]"

def cases : IO Unit := do
  let lists := wordArrays ++ ([63, 999, 1000, 4096] : List Nat).map fun n =>
    (List.range n).map fun i => rw (n + i)
  for xs in lists do
    let n := xs.length
    for seed in [0, 1, maxU] do
      let hash := xs.foldl (fun acc value => acc * 3 + value) seed
      let built := xs.foldl (fun acc value => acc + (value + 1)) seed
      for (name, live) in [("foldWord", n), ("foldWordOwned", 0)] do
        IO.println s!"treecore|{name}|i64|{chain xs} {u seed}|{hash}|{live}|{n}"
      for (name, live) in [("foldBuild", n), ("foldBuildOwned", 0)] do
        IO.println s!"treecore|{name}|i64|{chain xs} {u seed}|{built}|{live}|{2 * n}"
      for values in [[], [maxU], [0, 3, maxU, 7]] do
        let total := xs.foldl (fun acc value => acc + values.toArray.getD value.toNat 0) seed
        for (name, live) in [("foldLookup", n + 1), ("foldLookupOwned", 0)] do
          IO.println s!"treecore|{name}|i64|{chain xs} {u seed} {arrU values}|{total}|{live}|{n + 1}"
    for (name, live) in [("first", n), ("firstOwned", 0)] do
      IO.println s!"treecore|{name}|i64|{chain xs}|{xs.headD 0}|{live}|{n}"
    for (name, live) in [("rest", n + (n - 1)), ("restOwned", n - 1)] do
      IO.println s!"treecore|{name}|chain-u64|{chain xs}|{render xs.tail}|{live}|{n + (n - 1)}"
    for (name, live) in [("rebuild", 2 * n), ("rebuildOwned", n)] do
      IO.println s!"treecore|{name}|chain-u64|{chain xs}|{render xs}|{live}|{live}"
    for (name, live) in [("duplicate", 3 * n), ("duplicateOwned", 2 * n)] do
      IO.println s!"treecore|{name}|list:chain-u64,chain-u64|{chain xs}|{render xs} {render xs}|{live}|{live}"
    for x in [0, 7, maxU] do
      for (name, live) in [("cons", 2 * n + 1), ("consOwned", n + 1)] do
        IO.println s!"treecore|{name}|chain-u64|{u x} {chain xs}|{render (x :: xs)}|{live}|{live}"
      let changed := match xs with | [] => [] | y :: ys => (y + x) :: ys
      for (name, live) in [("change", 2 * n), ("changeOwned", n)] do
        IO.println s!"treecore|{name}|chain-u64|{u x} {chain xs}|{render changed}|{live}|{live}"

end Verified.Examples.TreeCore

def Verified.Examples.treeCases : IO Unit := do
  TreeCopy.cases
  TreeCore.cases
