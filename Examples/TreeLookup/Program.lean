import LeanExe.Loop

/-!
Main's Demo 3 in this dialect: lookup in a complete binary search tree of seven nodes, stored in
breadth-first order after the query.  A loop of three steps, one per level, carries the node
index, a found flag, and the value of the node found; the node index advances at every step, and
the flag and value change only at the first match.
-/

namespace Examples.TreeLookup

def compute (xs : Array UInt64) : Array UInt64 :=
  let ok := xs.size.toUInt64 == 15
  let query := xs[(0 : UInt64).toNat]!
  let state := LeanExe.loop 3 ((0 : UInt64), (0 : UInt64), (0 : UInt64))
    fun _ (j, found, value) =>
      let key := xs[(2 * j + 1).toNat]!
      let hit := found == 0 && query == key
      (if query < key then 2 * j + 1 else 2 * j + 2, if hit then 1 else found,
        if hit then xs[(2 * j + 2).toNat]! else value)
  #[if ok then state.2.2 else 0, if ok then state.2.1 else 0]

end Examples.TreeLookup
