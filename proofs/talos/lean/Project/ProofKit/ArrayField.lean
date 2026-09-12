import Project.ProofKit.Array
import Project.ProofKit.Frame
import Project.ProofKit.Control

namespace Project.ProofKit.ArrayField
open Wasm

def addressProgram (pointerLocal indexLocal width field : Nat) : Wasm.Program :=
  [.localGet pointerLocal, .localGet indexLocal, .constI64 (UInt64.ofNat width), .mulI64,
    .constI64 (UInt64.ofNat (field + 1)), .addI64, .constI64 8, .mulI64, .addI64, .wrapI64]

def loadProgram (pointerLocal indexLocal width field : Nat) : Wasm.Program :=
  addressProgram pointerLocal indexLocal width field ++ [.load64 0]

def storeProgram (pointerLocal indexLocal valueLocal width field : Nat) : Wasm.Program :=
  addressProgram pointerLocal indexLocal width field ++ [.localGet valueLocal, .store64 0]

theorem field_word (width field index : Nat) :
    (UInt64.ofNat index * UInt64.ofNat width + UInt64.ofNat (field + 1)) * 8 =
      UInt64.ofNat (8 * (width * index + field + 1)) := by
  change (_ + _) * UInt64.ofNat 8 = _
  rw [← UInt64.ofNat_mul, ← UInt64.ofNat_add, ← UInt64.ofNat_mul,
    Nat.mul_comm index width, Nat.mul_comm _ 8, Nat.add_assoc]

theorem address_spec (pointerLocal indexLocal width field : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer : UInt64) (index : Nat) (tail : List Value)
    (hValues : frame.values = tail)
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hIndex : frame.get indexLocal = some (.i64 (UInt64.ofNat index)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := .i32 (UInt64Array.wordAddress pointer (width * index + field + 1)) :: tail } env) :
    wp module_ (addressProgram pointerLocal indexLocal width field ++ rest) Q store frame env := by
  simpa only [addressProgram, List.cons_append, List.nil_append, wp_simp,
    Frame.withValues_get, hPointer, hIndex, hValues, field_word,
    UInt64Array.wordAddress, Memory.toUInt32_eq_ofNat, Nat.reducePow] using hNext

theorem load_spec (pointerLocal indexLocal width field : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer value : UInt64) (index : Nat) (tail : List Value)
    (hValues : frame.values = tail)
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hIndex : frame.get indexLocal = some (.i64 (UInt64.ofNat index)))
    (hBound : (UInt64Array.wordAddress pointer (width * index + field + 1)).toNat + 8 ≤
      store.mem.pages * 65536)
    (hRead : store.mem.read64 (UInt64Array.wordAddress pointer (width * index + field + 1)) = value)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store { frame with values := .i64 value :: tail } env) :
    wp module_ (loadProgram pointerLocal indexLocal width field ++ rest) Q store frame env := by
  simp only [loadProgram, List.append_assoc]
  apply address_spec pointerLocal indexLocal width field module_ env store frame pointer index tail
    hValues hPointer hIndex
  simpa only [List.cons_append, List.nil_append,
    wp_load64_cons, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
    ite_eq_right (Nat.not_lt.mpr hBound), hRead] using hNext

theorem store_spec (pointerLocal indexLocal valueLocal width field : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer value : UInt64) (index : Nat) (tail : List Value)
    (hValues : frame.values = tail)
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hIndex : frame.get indexLocal = some (.i64 (UInt64.ofNat index)))
    (hValue : frame.get valueLocal = some (.i64 value))
    (hBound : (UInt64Array.wordAddress pointer (width * index + field + 1)).toNat + 8 ≤
      store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      { store with mem := store.mem.write64 (UInt64Array.wordAddress pointer (width * index + field + 1)) value }
      { frame with values := tail } env) :
    wp module_ (storeProgram pointerLocal indexLocal valueLocal width field ++ rest) Q store frame env := by
  simp only [storeProgram, List.append_assoc]
  apply address_spec pointerLocal indexLocal width field module_ env store frame pointer index tail
    hValues hPointer hIndex
  simpa only [List.cons_append, List.nil_append,
    wp_localGet_cons, Frame.withValues_get, hValue, wp_store64_cons,
    UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero, ite_eq_right (Nat.not_lt.mpr hBound)] using hNext

#print axioms field_word
#print axioms address_spec
#print axioms load_spec
#print axioms store_spec

end Project.ProofKit.ArrayField
