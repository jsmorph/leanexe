import Examples.Trees.Cases

namespace Verified.Examples.TreeCopy

open TestSupport.Host Examples.Trees

def treeNodes : KeyTree → Nat
  | .leaf => 0
  | .node left _ right => 1 + treeNodes left + treeNodes right

def cases : IO Unit := do
  IO.println "treecopy|headerWidth1|i64|i64:0|1|0|1"
  IO.println "treecopy|headerWidth64|i64|i64:0|64|0|1"
  let lists := wordArrays ++ ([63, 999, 1000, 4096] : List Nat).map fun n =>
    (List.range n).map fun i => rw (n + i)
  for xs in lists do
    for (name, live) in [("copyList", 2 * xs.length), ("takeList", xs.length),
        ("discardList", xs.length)] do
      IO.println s!"treecopy|{name}|chain-u64|{chain xs}|[{", ".intercalate (xs.map toString)}]|{live}|{2 * xs.length}"
    IO.println s!"treecopy|releaseList|i64|{chain xs}|0|0|{2 * xs.length}"
    IO.println s!"treecopy|headerAfterList|i64|{chain xs}|0|0|{xs.length + 1}"
  let trees := [.leaf, .node .leaf 0 .leaf,
    .node (.node .leaf maxU .leaf) 7 (.node .leaf 0 .leaf)] ++
    ([63, 999, 1000, 4096] : List Nat).map KeyTree.chain ++
    (List.range 30).map fun i => KeyTree.arbitrary (3 * i) (i + 1)
  for tree in trees do
    let n := treeNodes tree
    let description := tree.describe
    for (name, live) in [("copyTree", 2 * n), ("takeTree", n), ("discardTree", n)] do
      IO.println s!"treecopy|{name}|tree-u64|tree-u64:{description}|{description}|{live}|{2 * n}"
    IO.println s!"treecopy|releaseTree|i64|tree-u64:{description}|0|0|{2 * n}"

end Verified.Examples.TreeCopy
