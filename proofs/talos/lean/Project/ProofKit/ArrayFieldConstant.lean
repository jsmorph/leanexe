import Project.ProofKit.ArrayField

namespace Project.ProofKit.ArrayField
open Wasm

def constantAddressProgram (pointerLocal index width field : Nat) : Wasm.Program :=
  [.localGet pointerLocal, .constI64 (UInt64.ofNat index), .constI64 (UInt64.ofNat width), .mulI64,
    .constI64 (UInt64.ofNat (field + 1)), .addI64, .constI64 8, .mulI64, .addI64, .wrapI64]

def constantStoreProgram (pointerLocal index valueLocal width field : Nat) : Wasm.Program :=
  constantAddressProgram pointerLocal index width field ++ [.localGet valueLocal, .store64 0]

theorem constantAddress_spec (pointerLocal index width field : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer : UInt64) (tail : List Value)
    (hValues : frame.values = tail) (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := .i32 (UInt64Array.wordAddress pointer (width * index + field + 1)) :: tail } env) :
    wp module_ (constantAddressProgram pointerLocal index width field ++ rest) Q store frame env := by
  simpa only [constantAddressProgram, List.cons_append, List.nil_append, wp_simp,
    Frame.withValues_get, hPointer, hValues, field_word,
    UInt64Array.wordAddress, Memory.toUInt32_eq_ofNat, Nat.reducePow] using hNext

theorem constantStore_spec (pointerLocal index valueLocal width field : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer value : UInt64) (tail : List Value)
    (hValues : frame.values = tail) (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hValue : frame.get valueLocal = some (.i64 value))
    (hBound : (UInt64Array.wordAddress pointer (width * index + field + 1)).toNat + 8 ≤
      store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      { store with mem := store.mem.write64 (UInt64Array.wordAddress pointer (width * index + field + 1)) value }
      { frame with values := tail } env) :
    wp module_ (constantStoreProgram pointerLocal index valueLocal width field ++ rest) Q store frame env := by
  simp only [constantStoreProgram, List.append_assoc]
  apply constantAddress_spec pointerLocal index width field module_ env store frame pointer tail hValues hPointer
  simpa only [List.cons_append, List.nil_append, wp_localGet_cons, Frame.withValues_get,
    hValue, wp_store64_cons, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
    ite_eq_right (Nat.not_lt.mpr hBound)] using hNext

#print axioms constantAddress_spec
#print axioms constantStore_spec

end Project.ProofKit.ArrayField
