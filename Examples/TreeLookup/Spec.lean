/-! The specification of the request in `Examples/TreeLookup/request.txt` (the earlier system's
Demo 3).  Nodes are numbered 0 to 6 in breadth-first order: node `j` has its key at `2j + 1` and its
value at `2j + 2`, nodes `2j + 1` and `2j + 2` are its left and right children, and nodes 3 to 6 are
leaves.  Decisions the request leaves to the specification: none.  The request fixes the result for
every input, including keys that are not in search-tree order. -/

namespace Examples.TreeLookup

/-- The search from node `j`: compare the query with the node's key, return the node's value on
equality, stop with `#[0, 0]` at a leaf, and otherwise descend left when the query is less than the
key and right when it is greater. -/
def search (input : Array UInt64) (query : UInt64) (j : Nat) : Array UInt64 :=
  let key := input[2 * j + 1]!
  if query = key then #[input[2 * j + 2]!, 1]
  else if 3 ≤ j then #[0, 0]
  else if query < key then search input query (2 * j + 1)
  else search input query (2 * j + 2)
termination_by 3 - j

def expected (input : Array UInt64) : Array UInt64 :=
  if input.size = 15 then search input input[0]! 0 else #[0, 0]

end Examples.TreeLookup
