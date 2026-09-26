import Project.EulerRiemann.FrozenInitialSingletonAllocate

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit

def initialCellsEntryFrame (n : Nat) : Locals :=
  func96Def.toLocals [.i64 (UInt64.ofNat n)]

def initialSingletonSaved (n : Nat) : List Value :=
  [.i64 20, .i64 (UInt64.ofNat n), .i64 (UInt64.ofNat (n * n)), .i64 (UInt64.ofNat n), .i64 0] ++
    (Memory.cellWords (Traversal.initialCell n 0)).toList.map Value.i64 ++
    List.replicate 8 (.i64 0) ++ [.i64 (UInt64.ofNat n), .i64 (UInt64.ofNat n)] ++
    List.replicate 8 (.i64 0)

def initialSingletonPreparedFrame (n : Nat) : Locals :=
  FixedArraySearch.frame [.i64 (UInt64.ofNat n)] (initialSingletonSaved n) [] 64 0 0 0 0 0

theorem initial_singleton_prefix_shape : initialCellsBody.take 45 =
    [.constI64 20, .localSet 1, .localGet 0, .localSet 2, .localGet 0, .localSet 21,
      .localGet 0, .localSet 22] ++ CheckedNatMul.program 21 22 ++
    [.localSet 3, .localGet 0, .localSet 4, .constI64 0, .localSet 5,
      .localGet 4, .localGet 5, .call 94,
      .localSet 12, .localSet 11, .localSet 10, .localSet 9, .localSet 8, .localSet 7, .localSet 6] ++
    FixedArrayCapacity.constantProgram 1 7 31 := rfl

theorem initial_singleton_prefix_spec (env : HostEnv Unit) (store : Store Unit)
    (n : Nat) (hn : n ≤ 800) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialSingletonPreparedFrame n) env) :
    wp module (initialCellsBody.take 45 ++ rest) Q store (initialCellsEntryFrame n) env := by
  have hNat : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (by change n < 18446744073709551616; omega)
  have hProduct := Nat.mul_le_mul hn hn
  have hFit : (UInt64.ofNat n).toNat * (UInt64.ofNat n).toNat < UInt64.size := by
    rw [hNat]
    change n * n < 18446744073709551616
    omega
  rw [initial_singleton_prefix_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_run [initialCellsEntryFrame, func96Def, List.set, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte]
  apply CheckedNatMul.program_spec 21 22 module env store _ (UInt64.ofNat n) (UInt64.ofNat n) []
    rfl rfl rfl hFit
  wp_run [List.set, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte]
  refine wp_call_tw (initialCell_exact env store n 0 hn (by decide)) ?_
  rintro current values ⟨hStore, hResult⟩
  subst current
  subst values
  wp_run [cellValues, List.set, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte]
  apply FixedArrayCapacity.constantProgram_spec 1 7 31 module env store _ rfl (by simp)
    (by simp [Locals.validIndex])
  simpa [initialSingletonPreparedFrame, initialSingletonSaved, FixedArraySearch.frame,
    FixedArrayCapacity.capacityFrame, FixedArrayCapacity.normalizedCapacity,
    FixedArrayCapacity.unnormalizedCapacity, Memory.cellWords, ← UInt64.ofNat_mul] using hNext

theorem initial_singleton_saved_length (n : Nat) : (initialSingletonSaved n).length = 30 := by
  simp [initialSingletonSaved, Memory.cellWords]

theorem initial_singleton_prepared_data (n field : Nat) (hField : field < 7) :
    (initialSingletonPreparedFrame n).get (6 + field) =
      some (.i64 ((Memory.cellWords (Traversal.initialCell n 0)).getD field 0)) := by
  interval_cases field <;>
    simp [initialSingletonPreparedFrame, initialSingletonSaved, FixedArraySearch.frame,
      Memory.cellWords, Array.getD, Locals.get]

#print axioms initial_singleton_prefix_shape
#print axioms initial_singleton_prefix_spec
#print axioms initial_singleton_saved_length
#print axioms initial_singleton_prepared_data

end Project.EulerRiemann.Frozen.Execution
