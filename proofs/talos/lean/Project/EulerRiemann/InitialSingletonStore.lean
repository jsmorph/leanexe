import Project.EulerRiemann.InitialSingletonShape

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

theorem initial_singleton_store_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (root : UInt64) (cell : Traversal.Cell)
    (hValues : frame.values = []) (hRoot : frame.get 21 = some (.i64 root))
    (hData : ∀ field : Nat, field < 7 →
      frame.get (24 + field) = some (.i64 ((Memory.cellWords cell).getD field 0)))
    (hFit32 : root.toNat + 64 ≤ 4294967296)
    (hFitMemory : root.toNat + 64 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (Memory.writeCell store root 0 cell) frame env) :
    wp module ((initialCellsBody.drop 80).take 84 ++ rest) Q store frame env := by
  rw [initial_singleton_store_shape]
  apply ArrayField.constantStores_spec 21 0 24 7 0 module env store frame root
    (Memory.cellWords cell).toList hValues hRoot
  · intro field hField
    have hSeven : field < 7 := by simpa [Memory.cellWords] using hField
    have h := hData field hSeven
    interval_cases field <;> exact h
  · intro field hField
    have hSeven : field < 7 := by simpa [Memory.cellWords] using hField
    rw [UInt64Array.wordAddress_toNat (words := 8) hFit32 (by omega)]
    omega
  · simpa [ArrayField.writeConstantFields, Memory.writeCell, Memory.writeField,
      Memory.cellWords, UInt64Array.wordAddress] using hNext

#print axioms initial_singleton_store_spec

end Project.EulerRiemann.Execution
