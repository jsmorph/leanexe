module

public import Verified.Reflect.Command
public import Verified.Native
public import LeanExe.Dialect.ArrayLemmas

@[expose] public section

/-!
A test of `LeanExe.Pipeline.ImplementsA.mono_borrowed`.  `count` returns the number of elements of
an array as a word, which equals the size only below `2 ^ 64`.  The representation of a borrowed
array bounds its size by `LeanExe.ProofKit.UInt64Array.At.size_lt_memory32`, and
`ImplementsA.mono_borrowed` passes the representation to the implication between the
postconditions, so `count_claims` adds the equation to the postcondition of
`compiled.count.trapFree` with no premise on the size.  `count_native` carries the claim to the C
function of the translation, as `p.f.native` carries `p.f.implements`.
-/

namespace TestSupport.Modules.Count

open LeanExe.Pipeline

/-- The number of elements as a word. -/
def count (xs : Array UInt64) : UInt64 := xs.size.toUInt64

verified_compile compiled := [count]

theorem count_toNat (xs : Array UInt64) (h : xs.size < 2 ^ 64) : (count xs).toNat = xs.size :=
  LeanExe.Dialect.size_toUInt64 xs h

/-- The theorem of `count` without a trap, with the equation of its result in the
postcondition. -/
theorem count_claims :
    ImplementsA false compiled.module 2 count (fun _ _ _ => True)
      (fun xs _ _ _ _ => (count xs).toNat = xs.size) :=
  compiled.count.trapFree.mono_borrowed (fun _ _ _ h => h) fun xs _ _ _ _ _ _ ⟨_, _, hb⟩ _ =>
    count_toNat xs (by have := hb.values.size_lt_memory32; omega)

/-- The C function of `count` computes it with the equation of `count_claims`. -/
theorem count_native (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl count_claims A X LeanExe.Native.nativeCap compiled.translation :=
  LeanExe.Native.ImplementsA.nativeImpl _ compiled.translation_eq
    (LeanExe.Native.translate_mem_funcs compiled.translation_eq compiled.translation_funcs
      (by decide))

#print axioms LeanExe.Pipeline.ImplementsA.mono_borrowed
#print axioms count_claims
#print axioms count_native

end TestSupport.Modules.Count
