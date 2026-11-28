module

public import Library.Numerics.Bignum.Export
public import Verified.Call
public import Verified.Congr

@[expose] public section

/-!
The call theorems of the module's exports.  Each composes the generated `trapFree` theorem of the
export with its equation through `Verified.call_on`, as MultiPrecision's `add_call` does, with the
precondition that the arguments are canonical (limbs below `2^32` for `natTrim`, none for the text
exports) and the room `heap.Within store compiled.module (compiled.f.bound x)`.  The arguments'
representations give the size premises of the equations: an array in memory has fewer than `2^29`
words (`UInt64Array.At.size_lt_memory32`), and a `BigInt` is represented as its sign and its
magnitude, whose array the pattern `⟨_, _, _, _, ⟨_, _, h⟩⟩` reaches.  `Bound.lean` and
`Export.lean` bound each `compiled.f.bound x` by a closed form.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision (value Digits)
open LeanExe.ProofKit

/-! ## Export indices -/

theorem natTrim_export :
    ({ name := "natTrim", funcIdx := 20 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natCmp_export :
    ({ name := "natCmp", funcIdx := 21 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natAdd_export :
    ({ name := "natAdd", funcIdx := 22 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natSub_export :
    ({ name := "natSub", funcIdx := 23 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natMul_export :
    ({ name := "natMul", funcIdx := 24 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natDivModChecked_export :
    ({ name := "natDivModChecked", funcIdx := 25 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intNeg_export :
    ({ name := "intNeg", funcIdx := 26 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intCmp_export :
    ({ name := "intCmp", funcIdx := 27 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intAdd_export :
    ({ name := "intAdd", funcIdx := 28 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intSub_export :
    ({ name := "intSub", funcIdx := 29 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intMul_export :
    ({ name := "intMul", funcIdx := 30 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intTDivModChecked_export :
    ({ name := "intTDivModChecked", funcIdx := 31 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intEDivModChecked_export :
    ({ name := "intEDivModChecked", funcIdx := 32 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intToText_export :
    ({ name := "intToText", funcIdx := 33 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intOfText_export :
    ({ name := "intOfText", funcIdx := 34 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem textNeg_export :
    ({ name := "textNeg", funcIdx := 35 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem textCmp_export :
    ({ name := "textCmp", funcIdx := 36 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem textAdd_export :
    ({ name := "textAdd", funcIdx := 37 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem textSub_export :
    ({ name := "textSub", funcIdx := 38 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem textMul_export :
    ({ name := "textMul", funcIdx := 39 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem textTDiv_export :
    ({ name := "textTDiv", funcIdx := 40 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem textTMod_export :
    ({ name := "textTMod", funcIdx := 41 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem textEDiv_export :
    ({ name := "textEDiv", funcIdx := 42 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem textEMod_export :
    ({ name := "textEMod", funcIdx := 43 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-! ## Call theorems -/

/-- Function 20, `natTrim`, called with an array of limbs below `2^32`, returns the canonical limbs
of its value. -/
theorem natTrim_call :
    Verified.Call compiled.module compiled.tables 20
      (fun u : Array UInt64 => limbsOf (value u))
      (fun u heap store => Digits u ∧ heap.Within store compiled.module (compiled.natTrim.bound u))
      (fun u heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natTrim.bound u) :=
  Verified.call_on (fun u => Digits u)
    (Verified.ImplementsTables.call (.ofA compiled.natTrim.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ u ⟨_, _, h1⟩ hu =>
      natTrim_eq hu (by have := h1.values.size_lt_memory32; omega)

/-- Function 21, `natCmp`, called with two canonical naturals, returns the code 0, 1, or 2 of `cmpSpec` of their values. -/
theorem natCmp_call :
    Verified.Call compiled.module compiled.tables 21
      (fun x : Array UInt64 × Array UInt64 => cmpSpec (value x.1) (value x.2))
      (fun x _ _ => Canonical x.1 ∧ Canonical x.2)
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natCmp.bound x) :=
  Verified.call_on (fun x => Canonical x.1 ∧ Canonical x.2)
    (Verified.ImplementsTables.call (.ofA compiled.natCmp.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨h, trivial⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      natCmp_eq hu.1 hv.1
        (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 22, `natAdd`, called with two canonical naturals, returns the canonical limbs of the sum. -/
theorem natAdd_call :
    Verified.Call compiled.module compiled.tables 22
      (fun x : Array UInt64 × Array UInt64 => limbsOf (value x.1 + value x.2))
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natAdd.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natAdd.bound x) :=
  Verified.call_on (fun x => Canonical x.1 ∧ Canonical x.2)
    (Verified.ImplementsTables.call (.ofA compiled.natAdd.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      natAdd_eq hu.1 hv.1
        (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 23, `natSub`, called with two canonical naturals, returns the flag `a < b` and the canonical limbs of `|a - b|`. -/
theorem natSub_call :
    Verified.Call compiled.module compiled.tables 23
      (fun x : Array UInt64 × Array UInt64 => natSubSpec (value x.1) (value x.2))
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natSub.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natSub.bound x) :=
  Verified.call_on (fun x => Canonical x.1 ∧ Canonical x.2)
    (Verified.ImplementsTables.call (.ofA compiled.natSub.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      natSub_eq hu.1 hv.1
        (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 24, `natMul`, called with two canonical naturals, returns the canonical limbs of the product. -/
theorem natMul_call :
    Verified.Call compiled.module compiled.tables 24
      (fun x : Array UInt64 × Array UInt64 => limbsOf (value x.1 * value x.2))
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natMul.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natMul.bound x) :=
  Verified.call_on (fun x => Canonical x.1 ∧ Canonical x.2)
    (Verified.ImplementsTables.call (.ofA compiled.natMul.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      natMul_eq hu.1 hv.1
        (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 25, `natDivModChecked`, called with two canonical naturals, returns the status 1 and two zeros for a zero divisor, and otherwise the status 0 and the canonical limbs of the quotient and the remainder. -/
theorem natDivModChecked_call :
    Verified.Call compiled.module compiled.tables 25
      (fun x : Array UInt64 × Array UInt64 => natDivModCheckedSpec (value x.1) (value x.2))
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧ heap.Within store compiled.module (compiled.natDivModChecked.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natDivModChecked.bound x) :=
  Verified.call_on (fun x => Canonical x.1 ∧ Canonical x.2)
    (Verified.ImplementsTables.call (.ofA compiled.natDivModChecked.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      natDivModChecked_eq hu hv
        (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 27, `intCmp`, called with two canonical integers, returns the code 0, 1, or 2 of `cmpSpec` of their integers. -/
theorem intCmp_call :
    Verified.Call compiled.module compiled.tables 27
      (fun x : BigInt × BigInt => cmpSpec x.1.toInt x.2.toInt)
      (fun x _ _ => x.1.Canonical ∧ x.2.Canonical)
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intCmp.bound x) :=
  Verified.call_on (fun x => x.1.Canonical ∧ x.2.Canonical)
    (Verified.ImplementsTables.call (.ofA compiled.intCmp.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨h, trivial⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩, ⟨_, _, _, _, ⟨_, _, h2⟩⟩⟩ ⟨hx, hy⟩ =>
      by
      have s1 : x.1.mag.size < 536870912 := h1.values.size_lt_memory32
      have s2 : x.2.mag.size < 536870912 := h2.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      rw [BigInt.eq_ofInt hy] at s2
      have h := intCmp_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← BigInt.eq_ofInt hx, ← BigInt.eq_ofInt hy] at h
      exact h

/-- Function 28, `intAdd`, called with two canonical integers, returns the canonical integer of the sum. -/
theorem intAdd_call :
    Verified.Call compiled.module compiled.tables 28
      (fun x : BigInt × BigInt => BigInt.ofInt (x.1.toInt + x.2.toInt))
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intAdd.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intAdd.bound x) :=
  Verified.call_on (fun x => x.1.Canonical ∧ x.2.Canonical)
    (Verified.ImplementsTables.call (.ofA compiled.intAdd.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩, ⟨_, _, _, _, ⟨_, _, h2⟩⟩⟩ ⟨hx, hy⟩ =>
      by
      have s1 : x.1.mag.size < 536870912 := h1.values.size_lt_memory32
      have s2 : x.2.mag.size < 536870912 := h2.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      rw [BigInt.eq_ofInt hy] at s2
      have h := intAdd_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← BigInt.eq_ofInt hx, ← BigInt.eq_ofInt hy] at h
      exact h

/-- Function 29, `intSub`, called with two canonical integers, returns the canonical integer of the difference. -/
theorem intSub_call :
    Verified.Call compiled.module compiled.tables 29
      (fun x : BigInt × BigInt => BigInt.ofInt (x.1.toInt - x.2.toInt))
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intSub.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intSub.bound x) :=
  Verified.call_on (fun x => x.1.Canonical ∧ x.2.Canonical)
    (Verified.ImplementsTables.call (.ofA compiled.intSub.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩, ⟨_, _, _, _, ⟨_, _, h2⟩⟩⟩ ⟨hx, hy⟩ =>
      by
      have s1 : x.1.mag.size < 536870912 := h1.values.size_lt_memory32
      have s2 : x.2.mag.size < 536870912 := h2.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      rw [BigInt.eq_ofInt hy] at s2
      have h := intSub_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← BigInt.eq_ofInt hx, ← BigInt.eq_ofInt hy] at h
      exact h

/-- Function 30, `intMul`, called with two canonical integers, returns the canonical integer of the product. -/
theorem intMul_call :
    Verified.Call compiled.module compiled.tables 30
      (fun x : BigInt × BigInt => BigInt.ofInt (x.1.toInt * x.2.toInt))
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intMul.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intMul.bound x) :=
  Verified.call_on (fun x => x.1.Canonical ∧ x.2.Canonical)
    (Verified.ImplementsTables.call (.ofA compiled.intMul.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩, ⟨_, _, _, _, ⟨_, _, h2⟩⟩⟩ ⟨hx, hy⟩ =>
      by
      have s1 : x.1.mag.size < 536870912 := h1.values.size_lt_memory32
      have s2 : x.2.mag.size < 536870912 := h2.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      rw [BigInt.eq_ofInt hy] at s2
      have h := intMul_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← BigInt.eq_ofInt hx, ← BigInt.eq_ofInt hy] at h
      exact h

/-- Function 31, `intTDivModChecked`, called with two canonical integers, returns the status 1 and two zeros for a zero divisor, and otherwise the status 0 with `Int.tdiv` and `Int.tmod` of their integers. -/
theorem intTDivModChecked_call :
    Verified.Call compiled.module compiled.tables 31
      (fun x : BigInt × BigInt => intTDivModCheckedSpec x.1.toInt x.2.toInt)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intTDivModChecked.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intTDivModChecked.bound x) :=
  Verified.call_on (fun x => x.1.Canonical ∧ x.2.Canonical)
    (Verified.ImplementsTables.call (.ofA compiled.intTDivModChecked.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩, ⟨_, _, _, _, ⟨_, _, h2⟩⟩⟩ ⟨hx, hy⟩ =>
      by
      have s1 : x.1.mag.size < 536870912 := h1.values.size_lt_memory32
      have s2 : x.2.mag.size < 536870912 := h2.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      rw [BigInt.eq_ofInt hy] at s2
      have h := intTDivModChecked_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← BigInt.eq_ofInt hx, ← BigInt.eq_ofInt hy] at h
      exact h

/-- Function 32, `intEDivModChecked`, called with two canonical integers, returns the status 1 and two zeros for a zero divisor, and otherwise the status 0 with Lean's `/` and `%` of their integers. -/
theorem intEDivModChecked_call :
    Verified.Call compiled.module compiled.tables 32
      (fun x : BigInt × BigInt => intEDivModCheckedSpec x.1.toInt x.2.toInt)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧ heap.Within store compiled.module (compiled.intEDivModChecked.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intEDivModChecked.bound x) :=
  Verified.call_on (fun x => x.1.Canonical ∧ x.2.Canonical)
    (Verified.ImplementsTables.call (.ofA compiled.intEDivModChecked.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩, ⟨_, _, _, _, ⟨_, _, h2⟩⟩⟩ ⟨hx, hy⟩ =>
      by
      have s1 : x.1.mag.size < 536870912 := h1.values.size_lt_memory32
      have s2 : x.2.mag.size < 536870912 := h2.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      rw [BigInt.eq_ofInt hy] at s2
      have h := intEDivModChecked_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← BigInt.eq_ofInt hx, ← BigInt.eq_ofInt hy] at h
      exact h

/-- Function 26, `intNeg`, called with a canonical integer, returns the canonical integer of its
negation. -/
theorem intNeg_call :
    Verified.Call compiled.module compiled.tables 26
      (fun x : BigInt => BigInt.ofInt (-x.toInt))
      (fun x heap store => x.Canonical ∧ heap.Within store compiled.module (compiled.intNeg.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intNeg.bound x) :=
  Verified.call_on (fun x => x.Canonical)
    (Verified.ImplementsTables.call (.ofA compiled.intNeg.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, h1⟩⟩ hx => by
      have s1 : x.mag.size < 536870912 := h1.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      have h := intNeg_eq (a := x.toInt) (by omega)
      rw [← BigInt.eq_ofInt hx] at h
      exact h

/-- Function 33, `intToText`, called with a canonical integer, returns the bytes of Lean's
`toString` of its integer, one byte to a word. -/
theorem intToText_call :
    Verified.Call compiled.module compiled.tables 33
      (fun x : BigInt => printSpec x.toInt)
      (fun x heap store => x.Canonical ∧ heap.Within store compiled.module (compiled.intToText.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intToText.bound x) :=
  Verified.call_on (fun x => x.Canonical)
    (Verified.ImplementsTables.call (.ofA compiled.intToText.trapFree) compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, h1⟩⟩ hx => by
      have s1 : x.mag.size < 536870912 := h1.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      have h := intToText_eq (z := x.toInt) (by omega)
      rw [← BigInt.eq_ofInt hx] at h
      exact h

/-- Function 34, `intOfText`, called with any array of words, returns `readSpec` of it: the flag
`true` and the canonical integer of a text of the grammar, and `(false, 0)` otherwise. -/
theorem intOfText_call :
    Verified.Call compiled.module compiled.tables 34 readSpec
      (fun s heap store => heap.Within store compiled.module (compiled.intOfText.bound s))
      (fun s heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intOfText.bound s) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.intOfText.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ s ⟨_, _, h1⟩ _ =>
      intOfText_eq s (by have := h1.values.size_lt_memory32; omega)

/-- Function 35, `textNeg`, called with any array of words, returns `textNegSpec` of it. -/
theorem textNeg_call :
    Verified.Call compiled.module compiled.tables 35 textNegSpec
      (fun s heap store => heap.Within store compiled.module (compiled.textNeg.bound s))
      (fun s heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.textNeg.bound s) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.textNeg.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ s ⟨_, _, h1⟩ _ =>
      textNeg_eq s (by have := h1.values.size_lt_memory32; omega)

/-- Function 36, `textCmp`, called with any two arrays of words, returns `textCmpSpec` of them. -/
theorem textCmp_call :
    Verified.Call compiled.module compiled.tables 36
      (fun x : Array UInt64 × Array UInt64 => textCmpSpec x.1 x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.textCmp.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.textCmp.bound x) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.textCmp.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ _ =>
      textCmp_eq x.1 x.2 (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 37, `textAdd`, called with any two arrays of words, returns `textAddSpec` of them. -/
theorem textAdd_call :
    Verified.Call compiled.module compiled.tables 37
      (fun x : Array UInt64 × Array UInt64 => textAddSpec x.1 x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.textAdd.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.textAdd.bound x) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.textAdd.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ _ =>
      textAdd_eq x.1 x.2 (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 38, `textSub`, called with any two arrays of words, returns `textSubSpec` of them. -/
theorem textSub_call :
    Verified.Call compiled.module compiled.tables 38
      (fun x : Array UInt64 × Array UInt64 => textSubSpec x.1 x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.textSub.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.textSub.bound x) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.textSub.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ _ =>
      textSub_eq x.1 x.2 (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 39, `textMul`, called with any two arrays of words, returns `textMulSpec` of them. -/
theorem textMul_call :
    Verified.Call compiled.module compiled.tables 39
      (fun x : Array UInt64 × Array UInt64 => textMulSpec x.1 x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.textMul.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.textMul.bound x) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.textMul.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ _ =>
      textMul_eq x.1 x.2 (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 40, `textTDiv`, called with any two arrays of words, returns `textTDivSpec` of them. -/
theorem textTDiv_call :
    Verified.Call compiled.module compiled.tables 40
      (fun x : Array UInt64 × Array UInt64 => textTDivSpec x.1 x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.textTDiv.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.textTDiv.bound x) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.textTDiv.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ _ =>
      textTDiv_eq x.1 x.2 (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 41, `textTMod`, called with any two arrays of words, returns `textTModSpec` of them. -/
theorem textTMod_call :
    Verified.Call compiled.module compiled.tables 41
      (fun x : Array UInt64 × Array UInt64 => textTModSpec x.1 x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.textTMod.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.textTMod.bound x) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.textTMod.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ _ =>
      textTMod_eq x.1 x.2 (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 42, `textEDiv`, called with any two arrays of words, returns `textEDivSpec` of them. -/
theorem textEDiv_call :
    Verified.Call compiled.module compiled.tables 42
      (fun x : Array UInt64 × Array UInt64 => textEDivSpec x.1 x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.textEDiv.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.textEDiv.bound x) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.textEDiv.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ _ =>
      textEDiv_eq x.1 x.2 (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 43, `textEMod`, called with any two arrays of words, returns `textEModSpec` of them. -/
theorem textEMod_call :
    Verified.Call compiled.module compiled.tables 43
      (fun x : Array UInt64 × Array UInt64 => textEModSpec x.1 x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.textEMod.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.textEMod.bound x) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA compiled.textEMod.trapFree) compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ _ =>
      textEMod_eq x.1 x.2 (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-! ## The comparisons allocate nothing -/

theorem natCmp_bound (x : Array UInt64 × Array UInt64) : compiled.natCmp.bound x = 0 :=
  compiled.natCmp.bound_eq x.1 x.2

theorem intCmp_bound (x : BigInt × BigInt) : compiled.intCmp.bound x = 0 :=
  compiled.intCmp.bound_eq x.1 x.2

#print axioms natTrim_call
#print axioms natCmp_call
#print axioms natAdd_call
#print axioms natSub_call
#print axioms natMul_call
#print axioms natDivModChecked_call
#print axioms intNeg_call
#print axioms intCmp_call
#print axioms intAdd_call
#print axioms intSub_call
#print axioms intMul_call
#print axioms intTDivModChecked_call
#print axioms intEDivModChecked_call
#print axioms intToText_call
#print axioms intOfText_call
#print axioms textNeg_call
#print axioms textCmp_call
#print axioms textAdd_call
#print axioms textSub_call
#print axioms textMul_call
#print axioms textTDiv_call
#print axioms textTMod_call
#print axioms textEDiv_call
#print axioms textEMod_call
#print axioms natTrim_bound_le
#print axioms natAdd_bound_le
#print axioms natSub_bound_le
#print axioms natMul_bound_le
#print axioms natDivModChecked_bound_le
#print axioms intNeg_bound_le
#print axioms intAdd_bound_le
#print axioms intSub_bound_le
#print axioms intMul_bound_le
#print axioms intTDivModChecked_bound_le
#print axioms intEDivModChecked_bound_le
#print axioms intToText_bound_le
#print axioms intOfText_bound_le
#print axioms textNeg_bound_le
#print axioms textCmp_bound_le
#print axioms textAdd_bound_le
#print axioms textSub_bound_le
#print axioms textMul_bound_le
#print axioms textTDiv_bound_le
#print axioms textTMod_bound_le
#print axioms textEDiv_bound_le
#print axioms textEMod_bound_le
#print axioms value_limbsOf
#print axioms canonical_iff
#print axioms BigInt.canonical_iff
#print axioms natTrim_eq
#print axioms natCmp_eq
#print axioms natAdd_eq
#print axioms natSub_eq
#print axioms natMul_eq
#print axioms natDivMod_eq
#print axioms natDivModChecked_eq
#print axioms intNeg_eq
#print axioms intCmp_eq
#print axioms intAdd_eq
#print axioms intSub_eq
#print axioms intMul_eq
#print axioms intTDivMod_eq
#print axioms intEDivMod_eq
#print axioms intTDivModChecked_eq
#print axioms intEDivModChecked_eq
#print axioms intToText_eq
#print axioms intOfText_eq
#print axioms readSpec_print
#print axioms print_of_readSpec
#print axioms readSpec_reject
#print axioms read_print
#print axioms textNeg_eq
#print axioms textCmp_eq
#print axioms textAdd_eq
#print axioms textSub_eq
#print axioms textMul_eq
#print axioms textTDiv_eq
#print axioms textTMod_eq
#print axioms textEDiv_eq
#print axioms textEMod_eq

end Library.Numerics.Bignum
