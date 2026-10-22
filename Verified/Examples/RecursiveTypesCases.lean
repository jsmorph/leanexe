import Verified.Examples.RecursiveTypes
import Examples.Words.Cases
import Examples.Trees.Cases

namespace Verified.Examples.RecursiveTypes

open TestSupport.Host Examples.Words Examples.Trees

def render (xs : List UInt64) : String := s!"[{", ".intercalate (xs.map toString)}]"

def cases : IO Unit := do
  IO.println "recursivetypes|emptyWords|chain-u64||[]|0|0"
  IO.println "recursivetypes|emptyTree|tree-u64||.|0|0"
  let lists := wordArrays ++ [(List.range 4096).map rw]
  for xs in lists do
    let n := xs.length
    let value := Words.ofList xs
    let pair := duplicateWords value
    IO.println s!"recursivetypes|first|i64|{chain xs}|{value.first}|{n}|{n}"
    IO.println s!"recursivetypes|keepWords|chain-u64|{chain xs}|{render (keepWords value).toList}|{n}|{n}"
    IO.println s!"recursivetypes|duplicateWords|list:chain-u64,chain-u64|{chain xs}|{render pair.1.toList} {render pair.2.toList}|{2 * n}|{2 * n}"
    for head in [0, 7, maxU] do
      IO.println s!"recursivetypes|prependWords|chain-u64|{u head} {chain xs}|{render (prependWords head value).toList}|{n + 1}|{n + 1}"
    for acc in [0, maxU] do
      IO.println s!"recursivetypes|sumAcc|i64|{u acc} {chain xs}|{Words.sumAcc acc value}|{n}|{n}"
    for acc in [[], [maxU], [0, maxU, 7]] do
      let blocks := n + acc.length
      let result := reverseWords value (Words.ofList acc)
      IO.println s!"recursivetypes|reverseWords|chain-u64|{chain xs} {chain acc}|{render result.toList}|{blocks}|{blocks}"
  let trees := [.leaf, KeyTree.chain 4096, KeyTree.chain 999, KeyTree.chain 1000] ++
    (List.range 20).map fun i => KeyTree.arbitrary (3 * i) i
  for tree in trees do
    let n := tree.size.toNat
    let pair := duplicateTree tree
    IO.println s!"recursivetypes|keepTree|tree-u64|tree-u64:{(KeyTree.describe tree)}|{(KeyTree.describe (keepTree tree))}|{n}|{n}"
    IO.println s!"recursivetypes|duplicateTree|list:tree-u64,tree-u64|tree-u64:{(KeyTree.describe tree)}|{(KeyTree.describe pair.1)} {(KeyTree.describe pair.2)}|{2 * n}|{2 * n}"
    for key in [0, maxU] do
      IO.println s!"recursivetypes|setKey|tree-u64|{u key} tree-u64:{(KeyTree.describe tree)}|{(KeyTree.describe (tree.setKey key))}|{n}|{n}"
    let child := tree.leftChild
    IO.println s!"recursivetypes|leftChild|tree-u64|tree-u64:{(KeyTree.describe tree)}|{(KeyTree.describe child)}|{child.size}|{n}"
    let split := tree.splitRoot
    let live := split.1.size.toNat + split.2.size.toNat
    IO.println s!"recursivetypes|splitRoot|list:tree-u64,tree-u64|tree-u64:{(KeyTree.describe tree)}|{(KeyTree.describe split.1)} {(KeyTree.describe split.2)}|{live}|{n}"
    for count in [0, 1, 7, 999, 1000, 4096, maxU] do
      let result := followRight count tree
      IO.println s!"recursivetypes|followRight|tree-u64|{u count} tree-u64:{(KeyTree.describe tree)}|{(KeyTree.describe result)}|{result.size}|{n}"
    if tree.height < 1000 then
      IO.println s!"recursivetypes|size|i64|tree-u64:{(KeyTree.describe tree)}|{tree.size}|{n}|{n}"
      IO.println s!"recursivetypes|incr|tree-u64|tree-u64:{(KeyTree.describe tree)}|{(KeyTree.describe tree.incr)}|{n}|{n}"
    else
      IO.println s!"recursivetypes|size|i64|tree-u64:{(KeyTree.describe tree)}|trap"
      IO.println s!"recursivetypes|incr|tree-u64|tree-u64:{(KeyTree.describe tree)}|trap"
  for left in trees.take 8 do
    for right in trees.take 8 do
      for key in [0, maxU] do
        let n := left.size.toNat + right.size.toNat + 1
        IO.println s!"recursivetypes|nodeTree|tree-u64|tree-u64:{(KeyTree.describe left)} {u key} tree-u64:{(KeyTree.describe right)}|{(KeyTree.describe (nodeTree left key right))}|{n}|{n}"
  for n in ([0, 1, 7, 999, 1000, 4096] : List UInt64) do
    IO.println s!"recursivetypes|range|chain-u64|{u n}|{render (Words.range n).toList}|{n}|{n}"

end Verified.Examples.RecursiveTypes
