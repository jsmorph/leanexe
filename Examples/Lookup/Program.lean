import LeanExe.Dialect.Loop

/-!
The earlier system's Demo 2 in this dialect: the input `#[query, key1, value1, …, key10, value10]`
of 21 words gives `#[value, 1]` for the first pair whose key equals the query, and `#[0, 0]` when no
key matches or the input does not have 21 words.  A loop over the ten pairs keeps a found flag and
the value of the first match.
-/

namespace Examples.Lookup

def compute (xs : Array UInt64) : Array UInt64 :=
  let ok := xs.size.toUInt64 == 21
  let query := xs[(0 : UInt64).toNat]!
  let state := LeanExe.loop 10 ((0 : UInt64), (0 : UInt64)) fun k (found, value) =>
    let hit := found == 0 && xs[(2 * k + 1).toNat]! == query
    (if hit then 1 else found, if hit then xs[(2 * k + 2).toNat]! else value)
  #[if ok then state.2 else 0, if ok then state.1 else 0]

end Examples.Lookup
