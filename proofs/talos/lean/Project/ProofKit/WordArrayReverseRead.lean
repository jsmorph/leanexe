import Project.ProofKit.ArrayPrefix
import Project.ProofKit.Frame

namespace Project.ProofKit.WordArrayReverse
open Wasm UInt64Array

def readProgram (sourceLocal lengthLocal counterLocal : Nat) : Wasm.Program :=
  [.localGet sourceLocal, .localGet lengthLocal, .localGet counterLocal, .subI64, .constI64 1,
    .subI64, .constI64 1, .mulI64, .constI64 1, .addI64, .constI64 8, .mulI64,
    .addI64, .wrapI64, .load64 0]

theorem read_spec (sourceLocal lengthLocal counterLocal : Nat) (module_ : Wasm.Module)
    (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (source : UInt64) (values : Array UInt64)
    (index : Nat) (destination : UInt32) (hIndex : index < values.size)
    (hSource : At store source values) (hValues : frame.values = [.i32 destination])
    (hPointer : frame.get sourceLocal = some (.i64 source))
    (hLength : frame.get lengthLocal = some (.i64 (UInt64.ofNat values.size)))
    (hCounter : frame.get counterLocal = some (.i64 (UInt64.ofNat index)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := [.i64 values[values.size - 1 - index], .i32 destination] } env) :
    wp module_ (readProgram sourceLocal lengthLocal counterLocal ++ rest) Q store frame env := by
  have hReverse : UInt64.ofNat values.size - UInt64.ofNat index - 1 =
      UInt64.ofNat (values.size - 1 - index) := by
    rw [← UInt64.ofNat_sub hIndex.le]
    change UInt64.ofNat (values.size - index) - UInt64.ofNat 1 = _
    rw [← UInt64.ofNat_sub (show 1 ≤ values.size - index by omega)]
    congr 1
    omega
  have hReadIndex : values.size - 1 - index < values.size := by omega
  have hBound := hSource.elementBound _ hReadIndex
  have hRead := hSource.elementRead _ hReadIndex
  simp only [readProgram, List.cons_append, List.nil_append, wp_localGet_cons,
    Frame.withValues_get, hValues, hPointer, hLength, hCounter, wp_subI64_cons,
    wp_constI64_cons, hReverse, wp_mulI64_cons, wp_addI64_cons, wp_wrapI64_cons,
    generatedElementAddress, wp_load64_cons, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, Nat.not_lt.mpr hBound, ite_false]
  simpa only [wordAddress, hRead, Nat.not_lt.mpr hBound, ite_false] using hNext

#print axioms read_spec
end Project.ProofKit.WordArrayReverse
