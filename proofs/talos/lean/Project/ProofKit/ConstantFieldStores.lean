import Project.ProofKit.ArrayFieldConstant

namespace Project.ProofKit.ArrayField
open Wasm

def constantStoresProgram (pointerLocal index valueLocal width first : Nat) : Nat → Wasm.Program
  | 0 => []
  | count + 1 => constantStoreProgram pointerLocal index valueLocal width first ++
      constantStoresProgram pointerLocal index (valueLocal + 1) width (first + 1) count

def writeConstantFields (store : Store Unit) (pointer : UInt64) (index width first : Nat) :
    List UInt64 → Store Unit
  | [] => store
  | value :: values => writeConstantFields
      { store with mem := store.mem.write64 (UInt64Array.wordAddress pointer (width * index + first + 1)) value }
      pointer index width (first + 1) values

theorem constantStores_spec (pointerLocal index valueLocal width first : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer : UInt64) (words : List UInt64) (hValues : frame.values = [])
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hData : ∀ j : Nat, (hj : j < words.length) → frame.get (valueLocal + j) = some (.i64 words[j]))
    (hBound : ∀ j : Nat, j < words.length →
      (UInt64Array.wordAddress pointer (width * index + (first + j) + 1)).toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (writeConstantFields store pointer index width first words) frame env) :
    wp module_ (constantStoresProgram pointerLocal index valueLocal width first words.length ++ rest)
      Q store frame env := by
  have hEmpty : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
  induction words generalizing store valueLocal first with
  | nil => simpa only [List.length_nil, constantStoresProgram, List.nil_append, writeConstantFields] using hNext
  | cons value words ih =>
    have hHead := hData 0 (by simp)
    change frame.get (valueLocal + 0) = some (.i64 value) at hHead
    simp only [List.length_cons, constantStoresProgram, List.append_assoc]
    apply constantStore_spec pointerLocal index valueLocal width first module_ env store frame pointer value []
      hValues hPointer (by simpa only [Nat.add_zero] using hHead) (by simpa using hBound 0 (by simp))
    rw [hEmpty]
    apply ih
    · intro j hj
      have hRead := hData (j + 1) (by simp; omega)
      change frame.get (valueLocal + (j + 1)) = some (.i64 words[j]) at hRead
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hRead
    · intro j hj
      simpa only [Mem.write64_pages, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using hBound (j + 1) (by simp; omega)
    · exact hNext

#print axioms constantStores_spec

end Project.ProofKit.ArrayField
