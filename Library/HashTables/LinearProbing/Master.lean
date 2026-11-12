import Library.HashTables.LinearProbing.Compiled
import Verified.Master

namespace Library.HashTables.LinearProbing

/-- The export `hashTable`, called on an array of words whose first word, the slot count `M`, is
below `2 ^ 63` and whose later words are pairs of an operation code and a key, returns the outputs
of `runOps`, a table of at most `M - 1` distinct keys kept as a list, on those operations from the
empty table.  Code 0 inserts the key, code 1 looks it up, any other code deletes it, and each
operation outputs 1 when it succeeds and 0 otherwise. -/
theorem hashTable_master :
    Verified.Master compiled.module compiled.tables "hashTable" compiled.hashTable.bound
      (fun xs : Array UInt64 => xs[0]!.toNat < 2 ^ 63)
      (fun xs ys => ys = (runOps xs[0]!.toNat
        ((List.range ((xs.size - 1) / 2)).map fun i => (xs[2 * i + 1]!, xs[2 * i + 2]!))
        [] []).toArray) :=
  .of_trapFree (.ofA compiled.hashTable.trapFree) nofun hashTable_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ hm => hashTable_eq xs hxs.values.size_lt hm

#print axioms hashTable_master

end Library.HashTables.LinearProbing
