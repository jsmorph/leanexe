import Verified.Examples.RecursiveTypes
import Examples.Words.Cases
import Examples.Trees.Cases

namespace Verified.Examples.RecursiveTypes

open Examples.Host Examples.Words Examples.Trees

def render (xs : List UInt64) : String := s!"[{", ".intercalate (xs.map toString)}]"

def cases : IO Unit := do
  IO.println "recursivetypes|emptyWords|chain-u64||[]|0|0"
  IO.println "recursivetypes|emptyTree|tree-u64||.|0|0"
  let lists := wordArrays ++ [(List.range 4096).map rw]
  for xs in lists do
    let n := xs.length
    let value := Words.ofList xs
    let pair := duplicateWords value
    IO.println s!"recursivetypes|keepWords|chain-u64|{chain xs}|{render (keepWords value).toList}|{n}|{n}"
    IO.println s!"recursivetypes|duplicateWords|list:chain-u64,chain-u64|{chain xs}|{render pair.1.toList} {render pair.2.toList}|{2 * n}|{2 * n}"
    for head in [0, 7, maxU] do
      IO.println s!"recursivetypes|prependWords|chain-u64|{u head} {chain xs}|{render (prependWords head value).toList}|{n + 1}|{n + 1}"
  let trees := [.leaf, KeyTree.chain 4096] ++
    (List.range 20).map fun i => KeyTree.arbitrary (3 * i) i
  for tree in trees do
    let n := tree.size.toNat
    let pair := duplicateTree tree
    IO.println s!"recursivetypes|keepTree|tree-u64|tree-u64:{tree.describe}|{(keepTree tree).describe}|{n}|{n}"
    IO.println s!"recursivetypes|duplicateTree|list:tree-u64,tree-u64|tree-u64:{tree.describe}|{pair.1.describe} {pair.2.describe}|{2 * n}|{2 * n}"
  for left in trees.take 8 do
    for right in trees.take 8 do
      for key in [0, maxU] do
        let n := left.size.toNat + right.size.toNat + 1
        IO.println s!"recursivetypes|nodeTree|tree-u64|tree-u64:{left.describe} {u key} tree-u64:{right.describe}|{(nodeTree left key right).describe}|{n}|{n}"

end Verified.Examples.RecursiveTypes
