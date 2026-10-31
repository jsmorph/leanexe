import Library.HashTables.LinearProbing.Proof
import Verified.Reflect.Command
import Verified.Call
import Verified.Congr

/-! The verified compiler's module of the hash table.  The compiler translates the tail recursions
of `probe` and `close` into loops and unfolds `step` into the loop of `hashTable`, whose state owns
the outputs and the table, so each operation changes the table in place.  `hashTable_call` composes
the generated `compiled.hashTable.trapFree` with `hashTable_eq`.  It has the precondition
`slots xs < 2^63`, under which the word arithmetic on slot indices does not wrap. -/

namespace Library.HashTables.LinearProbing

open Wasm LeanExe.Pipeline

verified_compile compiled := [next, probe, move, gap, close, slot, hashTable]

theorem hashTable_export :
    ({ name := "hashTable", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 8, the export `hashTable`, called from a ready store with an input whose slot count is
below `2^63` and with room for `compiled.hashTable.bound xs` bytes, returns without a trap the
owned array `expected xs`, one output for each operation, and leaves a ready store. -/
theorem hashTable_call :
    Verified.Call compiled.module compiled.tables 8 expected
      (fun x heap store =>
        slots x < 2 ^ 63 ∧ heap.Within store compiled.module (compiled.hashTable.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.hashTable.bound x) :=
  Verified.call_on (fun x => slots x < 2 ^ 63)
    (Verified.ImplementsTables.call (.ofA compiled.hashTable.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, hxs⟩ hm => hashTable_eq x (show _ < 2 ^ 64 from hxs.values.size_lt) hm

#print axioms hashTable_call

end Library.HashTables.LinearProbing
