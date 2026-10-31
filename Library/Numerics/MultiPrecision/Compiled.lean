import Library.Numerics.MultiPrecision.Proof
import Library.Numerics.MultiPrecision.DivideProof
import Verified.Reflect.Command
import Verified.Call
import Verified.Congr

/-! The verified compiler's module of multiple-precision arithmetic.  The call theorems compose the
generated `trapFree` theorems with `add_eq`, `sub_eq`, `mul_eq`, and `divide_eq`, with the
precondition that the arguments are arrays of digits, for the product that the two lengths sum to
less than `2^64`, and for the division that they sum to less than `2^62`.  The module also compiles
the Uscale module's `mulSmall` and `wordBits`, which the division calls. -/

namespace Library.Numerics.MultiPrecision

open Wasm LeanExe.Pipeline

verified_compile compiled := [width, add, sub, mul, significant,
  Library.Numerics.Arithmetic.Uscale.mulSmall, Library.Numerics.Arithmetic.Uscale.wordBits, shortDiv,
  tooBig, trial, longDiv, divide]

theorem add_export :
    ({ name := "add", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sub_export :
    ({ name := "sub", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem divide_export :
    ({ name := "divide", funcIdx := 13 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem mul_export :
    ({ name := "mul", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 3, the export `add`, called from a ready store with two arrays of digits and room for
`compiled.add.bound x` bytes, returns without a trap the owned array `addSpec x`. -/
theorem add_call :
    Verified.Call compiled.module compiled.tables 3 addSpec
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.add.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.add.bound x) :=
  Verified.call_on (fun x => Digits x.1 ∧ Digits x.2)
    (Verified.ImplementsTables.call (.ofA compiled.add.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      add_eq x.1 x.2 hu hv (show _ < 2 ^ 64 from h1.values.size_lt)
        (show _ < 2 ^ 64 from h2.values.size_lt)

/-- Function 4, the export `sub`, called from a ready store with two arrays of digits and room for
`compiled.sub.bound x` bytes, returns without a trap the owned array `subSpec x`. -/
theorem sub_call :
    Verified.Call compiled.module compiled.tables 4 subSpec
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.sub.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.sub.bound x) :=
  Verified.call_on (fun x => Digits x.1 ∧ Digits x.2)
    (Verified.ImplementsTables.call (.ofA compiled.sub.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      sub_eq x.1 x.2 hu hv (show _ < 2 ^ 64 from h1.values.size_lt)
        (show _ < 2 ^ 64 from h2.values.size_lt)

/-- Function 5, the export `mul`, called from a ready store with two arrays of digits whose lengths
sum to less than `2^64` and with room for `compiled.mul.bound x` bytes, returns without a trap the
owned array `mulSpec x`. -/
theorem mul_call :
    Verified.Call compiled.module compiled.tables 5 mulSpec
      (fun x heap store => (Digits x.1 ∧ Digits x.2 ∧ x.1.size + x.2.size < 2 ^ 64) ∧
        heap.Within store compiled.module (compiled.mul.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.mul.bound x) :=
  Verified.call_on (fun x => Digits x.1 ∧ Digits x.2 ∧ x.1.size + x.2.size < 2 ^ 64)
    (Verified.ImplementsTables.call (.ofA compiled.mul.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x _ ⟨hu, hv, hs⟩ => mul_eq x.1 x.2 hu hv hs

#print axioms add_call
#print axioms sub_call
/-- Function 13, the export `divide`, called from a ready store with two arrays of digits whose
lengths sum to less than `2^62` and with room for `compiled.divide.bound x` bytes, returns without a
trap the owned array `divSpec x`. -/
theorem divide_call :
    Verified.Call compiled.module compiled.tables 13 divSpec
      (fun x heap store => (Digits x.1 ∧ Digits x.2 ∧ x.1.size + x.2.size < 2 ^ 62) ∧
        heap.Within store compiled.module (compiled.divide.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.divide.bound x) :=
  Verified.call_on (fun x => Digits x.1 ∧ Digits x.2 ∧ x.1.size + x.2.size < 2 ^ 62)
    (Verified.ImplementsTables.call (.ofA compiled.divide.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x _ ⟨hu, hv, hs⟩ => divide_eq x.1 x.2 hu hv hs

#print axioms mul_call
#print axioms divide_call

end Library.Numerics.MultiPrecision
