module

public import Library.Numerics.Bignum.Call

@[expose] public section

/-!
The call theorems of the functions of MultiPrecision, Uscale, and Int64Text that the module also
exports, functions 2 to 19, since leanexe's compiler exports every function that it compiles.
They are not part of this library's interface, and each computes the Lean function of its leanexe
library, whose theorems give its meaning.  `add_call`, `sub_call`, `mul_call`, and `divide_call`
state MultiPrecision's specifications, as its own `Compiled.lean` does, and `le_call` states
Uscale's `le_spec` through `le_eq`; the others state the Lean function itself.  `divide`,
`shortDiv`, and `longDiv` follow MultiPrecision's conventions at a zero divisor and return no
error status.  Each function that allocates has a closed-form bound in `Bound.lean`, and
`reused_bounds_zero` states that the others allocate nothing.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open Library.Numerics.Arithmetic.Uscale (mulSmall wordBits limb cmpStep le)
open Library.Numerics.Decimal.Int64Text (digitCount digitByte isDigitW)
open LeanExe.ProofKit

theorem width_export :
    ({ name := "width", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem add_export :
    ({ name := "add", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sub_export :
    ({ name := "sub", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem mul_export :
    ({ name := "mul", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem significant_export :
    ({ name := "significant", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem mulSmall_export :
    ({ name := "mulSmall", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem wordBits_export :
    ({ name := "wordBits", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem shortDiv_export :
    ({ name := "shortDiv", funcIdx := 9 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem tooBig_export :
    ({ name := "tooBig", funcIdx := 10 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem trial_export :
    ({ name := "trial", funcIdx := 11 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem longDiv_export :
    ({ name := "longDiv", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem divide_export :
    ({ name := "divide", funcIdx := 13 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem limb_export :
    ({ name := "limb", funcIdx := 14 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem cmpStep_export :
    ({ name := "cmpStep", funcIdx := 15 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem le_export :
    ({ name := "le", funcIdx := 16 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem digitCount_export :
    ({ name := "digitCount", funcIdx := 17 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem digitByte_export :
    ({ name := "digitByte", funcIdx := 18 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem isDigitW_export :
    ({ name := "isDigitW", funcIdx := 19 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 3, MultiPrecision's `add`, called with two arrays of digits, returns the `k + 1` digits of the sum (`addSpec`). -/
theorem add_call :
    Verified.Call compiled.module compiled.tables 3 addSpec
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.add.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.add.bound x) :=
  Verified.call_on (fun x => Digits x.1 ∧ Digits x.2)
    (Verified.ImplementsTables.call (.ofA compiled.add.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ => by
      have := h1.values.size_lt_memory32
      have := h2.values.size_lt_memory32
      exact add_eq x.1 x.2 hu hv (by omega) (by omega)

/-- Function 4, MultiPrecision's `sub`, called with two arrays of digits, returns the `k` digits of `u + 2^(32 k) - v` (`subSpec`). -/
theorem sub_call :
    Verified.Call compiled.module compiled.tables 4 subSpec
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.sub.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.sub.bound x) :=
  Verified.call_on (fun x => Digits x.1 ∧ Digits x.2)
    (Verified.ImplementsTables.call (.ofA compiled.sub.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ => by
      have := h1.values.size_lt_memory32
      have := h2.values.size_lt_memory32
      exact sub_eq x.1 x.2 hu hv (by omega) (by omega)

/-- Function 5, MultiPrecision's `mul`, called with two arrays of digits, returns the `m + n` digits of the product (`mulSpec`). -/
theorem mul_call :
    Verified.Call compiled.module compiled.tables 5 mulSpec
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.mul.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.mul.bound x) :=
  Verified.call_on (fun x => Digits x.1 ∧ Digits x.2)
    (Verified.ImplementsTables.call (.ofA compiled.mul.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ => by
      have := h1.values.size_lt_memory32
      have := h2.values.size_lt_memory32
      exact mul_eq x.1 x.2 hu hv (by omega)

/-- Function 13, MultiPrecision's `divide`, called with two arrays of digits, returns the quotient's `m` digits and the remainder's `n` digits (`divSpec`), with quotient 0 and remainder `u` for a zero divisor. -/
theorem divide_call :
    Verified.Call compiled.module compiled.tables 13 divSpec
      (fun x heap store => (Digits x.1 ∧ Digits x.2) ∧
        heap.Within store compiled.module (compiled.divide.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.divide.bound x) :=
  Verified.call_on (fun x => Digits x.1 ∧ Digits x.2)
    (Verified.ImplementsTables.call (.ofA compiled.divide.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ => by
      have := h1.values.size_lt_memory32
      have := h2.values.size_lt_memory32
      exact divide_eq x.1 x.2 hu hv (by omega)

/-- Function 16, Uscale's `le`, called with two arrays of digits, returns whether the first
value is at most the second. -/
theorem le_call :
    Verified.Call compiled.module compiled.tables 16
      (fun x : Array UInt64 × Array UInt64 => decide (value x.1 ≤ value x.2))
      (fun x _ _ => Digits x.1 ∧ Digits x.2)
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.le.bound x) :=
  Verified.call_on (fun x => Digits x.1 ∧ Digits x.2)
    (Verified.ImplementsTables.call (.ofA compiled.le.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨h, trivial⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      le_eq hu hv (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 2, `width`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem width_call :
    Verified.CallSpec compiled.module compiled.tables 2 (fun x : Array UInt64 × Array UInt64 => width x.1 x.2)
      compiled.width.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.width.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 6, `significant`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem significant_call :
    Verified.CallSpec compiled.module compiled.tables 6 (fun x : Array UInt64 => significant x)
      compiled.significant.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.significant.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 7, `mulSmall`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem mulSmall_call :
    Verified.CallSpec compiled.module compiled.tables 7 (fun x : Array UInt64 × UInt64 × UInt64 => mulSmall x.1 x.2.1 x.2.2)
      compiled.mulSmall.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.mulSmall.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 8, `wordBits`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem wordBits_call :
    Verified.CallSpec compiled.module compiled.tables 8 (fun x : UInt64 => wordBits x)
      compiled.wordBits.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.wordBits.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 9, `shortDiv`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem shortDiv_call :
    Verified.CallSpec compiled.module compiled.tables 9 (fun x : Array UInt64 × UInt64 × UInt64 => shortDiv x.1 x.2.1 x.2.2)
      compiled.shortDiv.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.shortDiv.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 10, `tooBig`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem tooBig_call :
    Verified.CallSpec compiled.module compiled.tables 10 (fun x : UInt64 × UInt64 × UInt64 × UInt64 => tooBig x.1 x.2.1 x.2.2.1 x.2.2.2)
      compiled.tooBig.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.tooBig.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 11, `trial`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem trial_call :
    Verified.CallSpec compiled.module compiled.tables 11 (fun x : Array UInt64 × Array UInt64 × UInt64 × UInt64 => trial x.1 x.2.1 x.2.2.1 x.2.2.2)
      compiled.trial.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.trial.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 12, `longDiv`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem longDiv_call :
    Verified.CallSpec compiled.module compiled.tables 12 (fun x : Array UInt64 × Array UInt64 × UInt64 => longDiv x.1 x.2.1 x.2.2)
      compiled.longDiv.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.longDiv.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 14, `limb`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem limb_call :
    Verified.CallSpec compiled.module compiled.tables 14 (fun x : Array UInt64 × UInt64 => limb x.1 x.2)
      compiled.limb.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.limb.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 15, `cmpStep`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem cmpStep_call :
    Verified.CallSpec compiled.module compiled.tables 15 (fun x : Array UInt64 × Array UInt64 × UInt64 × UInt64 => cmpStep x.1 x.2.1 x.2.2.1 x.2.2.2)
      compiled.cmpStep.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.cmpStep.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 17, `digitCount`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem digitCount_call :
    Verified.CallSpec compiled.module compiled.tables 17 (fun x : UInt64 => digitCount x)
      compiled.digitCount.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.digitCount.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 18, `digitByte`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem digitByte_call :
    Verified.CallSpec compiled.module compiled.tables 18 (fun x : UInt64 × UInt64 => digitByte x.1 x.2)
      compiled.digitByte.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.digitByte.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 19, `isDigitW`, returns the Lean function's value, from a ready store with room for its
bound. -/
theorem isDigitW_call :
    Verified.CallSpec compiled.module compiled.tables 19 (fun x : UInt64 => isDigitW x)
      compiled.isDigitW.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.isDigitW.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- The reused functions other than `add`, `sub`, `mul`, `mulSmall`, `shortDiv`, `longDiv`, and
`divide` allocate nothing. -/
theorem reused_bounds_zero (u v : Array UInt64) (a b c d : UInt64) :
    compiled.width.bound (u, v) = 0 ∧ compiled.significant.bound u = 0 ∧
      compiled.wordBits.bound a = 0 ∧ compiled.tooBig.bound (a, b, c, d) = 0 ∧
      compiled.trial.bound (u, v, a, b) = 0 ∧ compiled.limb.bound (u, a) = 0 ∧
      compiled.cmpStep.bound (u, v, a, b) = 0 ∧ compiled.le.bound (u, v) = 0 ∧
      compiled.digitCount.bound a = 0 ∧ compiled.digitByte.bound (a, b) = 0 ∧
      compiled.isDigitW.bound a = 0 :=
  ⟨compiled.width.bound_eq u v, compiled.significant.bound_eq u, compiled.wordBits.bound_eq a,
    compiled.tooBig.bound_eq a b c d, compiled.trial.bound_eq u v a b, compiled.limb.bound_eq u a,
    compiled.cmpStep.bound_eq u v a b, compiled.le.bound_eq u v, compiled.digitCount.bound_eq a,
    compiled.digitByte.bound_eq a b, compiled.isDigitW.bound_eq a⟩

#print axioms width_call
#print axioms add_call
#print axioms sub_call
#print axioms mul_call
#print axioms significant_call
#print axioms mulSmall_call
#print axioms wordBits_call
#print axioms shortDiv_call
#print axioms tooBig_call
#print axioms trial_call
#print axioms longDiv_call
#print axioms divide_call
#print axioms limb_call
#print axioms cmpStep_call
#print axioms le_call
#print axioms digitCount_call
#print axioms digitByte_call
#print axioms isDigitW_call
#print axioms reused_bounds_zero
#print axioms longDiv_bound_le
#print axioms mulSmall_bound_le
#print axioms shortDiv_bound_le
#print axioms divide_bound_le
#print axioms add_bound_le
#print axioms sub_bound_le
#print axioms mul_bound_le
#print axioms intToText_of_read

end Library.Numerics.Bignum
