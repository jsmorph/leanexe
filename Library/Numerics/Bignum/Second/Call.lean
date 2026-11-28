module

public import Library.Numerics.Bignum.Second.Bound
public import Verified.Call
public import Verified.Congr
public import Library.Numerics.Bignum.Second.Loops

@[expose] public section

/-!
The call theorems of the second iteration's module.  Functions 20, 21, 25, and 26 are the
library's new interface: `natMulKara` and `intMulKara`, the products of naturals and integers by
Karatsuba's method above 48 limbs, and `natOfTextDC` and `intOfTextDC`, the readers of decimal text
by divide and conquer.  Functions 19 and 24, `natMulKaraWith` and `natOfTextDCWith`, take the
threshold and the bound on the base elements as arguments, for the timings, and meet the same
specifications for every value of them.  The compiler exports every function that it compiles, so
the module also exports the helpers, functions 2 to 18, 22, and 23, whose theorems state that the
module computes the Lean function without a trap; `Seg.lean`, `Base.lean`, `Kara.lean`, and
`Read.lean` prove what those Lean functions compute.

Each call theorem composes the generated `trapFree` theorem with the export's equation through
`Verified.call_on`, as the first iteration's `natMul_call` does.  The code of each export except
`isDigitW`, `trimSeg`, `readInit`, and the in-place loops takes the call depth, since it calls the
recursion `kara`, and its `trapFree` holds under `fits 1000 x`, which `Bound.lean` proves for every
argument: the call theorems carry no depth premise.  The room is the generated bound at 1,000
frames, and `Bound.lean` bounds it by a closed form linear in the arguments' lengths.
-/

namespace Library.Numerics.Bignum.Second

open Library.Numerics.Bignum
open Library.Numerics.MultiPrecision (value Digits)
open Library.Numerics.Decimal.Int64Text (isDigitW)
open LeanExe.ProofKit

/-! ## Export indices -/

theorem isDigitW_export :
    ({ name := "isDigitW", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem addGen_export :
    ({ name := "addGen", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem subGen_export :
    ({ name := "subGen", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem baseMul_export :
    ({ name := "baseMul", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem trimSeg_export :
    ({ name := "trimSeg", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem mulAddSeg_export :
    ({ name := "mulAddSeg", funcIdx := 11 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem readInit_export :
    ({ name := "readInit", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem kara_export :
    ({ name := "kara", funcIdx := 18 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natMulKaraWith_export :
    ({ name := "natMulKaraWith", funcIdx := 19 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natMulKara_export :
    ({ name := "natMulKara", funcIdx := 20 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intMulKara_export :
    ({ name := "intMulKara", funcIdx := 21 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem readPass_export :
    ({ name := "readPass", funcIdx := 22 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem decimalValueDC_export :
    ({ name := "decimalValueDC", funcIdx := 23 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natOfTextDCWith_export :
    ({ name := "natOfTextDCWith", funcIdx := 24 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natOfTextDC_export :
    ({ name := "natOfTextDC", funcIdx := 25 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intOfTextDC_export :
    ({ name := "intOfTextDC", funcIdx := 26 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-! ## The interface -/

/-- Function 20, `natMulKara`, called with two canonical naturals, returns the canonical limbs of
the product. -/
theorem natMulKara_call :
    Verified.Call compiled.module compiled.tables 20
      (fun x : Array UInt64 × Array UInt64 => limbsOf (value x.1 * value x.2))
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧
        heap.Within store compiled.module (compiled.natMulKara.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natMulKara.bound 1000 x) :=
  Verified.call_on (fun x => Canonical x.1 ∧ Canonical x.2)
    (Verified.ImplementsTables.call (.ofA (compiled.natMulKara.trapFree.mono
      (fun x _ _ h => ⟨natMulKara_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      natMulKara_eq hu.1 hv.1
        (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 21, `intMulKara`, called with two canonical integers, returns the canonical integer of
the product. -/
theorem intMulKara_call :
    Verified.Call compiled.module compiled.tables 21
      (fun x : BigInt × BigInt => BigInt.ofInt (x.1.toInt * x.2.toInt))
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧
        heap.Within store compiled.module (compiled.intMulKara.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intMulKara.bound 1000 x) :=
  Verified.call_on (fun x => x.1.Canonical ∧ x.2.Canonical)
    (Verified.ImplementsTables.call (.ofA (compiled.intMulKara.trapFree.mono
      (fun x _ _ h => ⟨intMulKara_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩, ⟨_, _, _, _, ⟨_, _, h2⟩⟩⟩ ⟨hx, hy⟩ =>
      by
      have s1 : x.1.mag.size < 536870912 := h1.values.size_lt_memory32
      have s2 : x.2.mag.size < 536870912 := h2.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      rw [BigInt.eq_ofInt hy] at s2
      have h := intMulKara_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← BigInt.eq_ofInt hx, ← BigInt.eq_ofInt hy] at h
      exact h

/-- Function 25, `natOfTextDC`, called with any array of words, returns `natReadSpec` of it. -/
theorem natOfTextDC_call :
    Verified.Call compiled.module compiled.tables 25 natReadSpec
      (fun s heap store => heap.Within store compiled.module (compiled.natOfTextDC.bound 1000 s))
      (fun s heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natOfTextDC.bound 1000 s) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA (compiled.natOfTextDC.trapFree.mono
      (fun x _ _ h => ⟨natOfTextDC_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ s ⟨_, _, h1⟩ _ =>
      natOfTextDC_eq s (by have := h1.values.size_lt_memory32; omega)

/-- Function 26, `intOfTextDC`, called with any array of words, returns `readSpec` of it, the
result of the first iteration's `intOfText`. -/
theorem intOfTextDC_call :
    Verified.Call compiled.module compiled.tables 26 readSpec
      (fun s heap store => heap.Within store compiled.module (compiled.intOfTextDC.bound 1000 s))
      (fun s heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intOfTextDC.bound 1000 s) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA (compiled.intOfTextDC.trapFree.mono
      (fun x _ _ h => ⟨intOfTextDC_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ s ⟨_, _, h1⟩ _ =>
      intOfTextDC_eq s (by have := h1.values.size_lt_memory32; omega)

/-! ## The entries with parameters -/

/-- Function 19, `natMulKaraWith`, called with any threshold and two canonical naturals, returns the
canonical limbs of the product. -/
theorem natMulKaraWith_call :
    Verified.Call compiled.module compiled.tables 19
      (fun x : UInt64 × Array UInt64 × Array UInt64 => limbsOf (value x.2.1 * value x.2.2))
      (fun x heap store => (Canonical x.2.1 ∧ Canonical x.2.2) ∧
        heap.Within store compiled.module (compiled.natMulKaraWith.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natMulKaraWith.bound 1000 x) :=
  Verified.call_on (fun x => Canonical x.2.1 ∧ Canonical x.2.2)
    (Verified.ImplementsTables.call (.ofA (compiled.natMulKaraWith.trapFree.mono
      (fun x _ _ h => ⟨natMulKaraWith_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩⟩ ⟨hu, hv⟩ =>
      natMulKaraWith_eq _ hu.1 hv.1
        (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 24, `natOfTextDCWith`, called with any threshold, any bound on the base elements, and
any array of words, returns `natReadSpec` of the array. -/
theorem natOfTextDCWith_call :
    Verified.Call compiled.module compiled.tables 24
      (fun x : UInt64 × UInt64 × Array UInt64 => natReadSpec x.2.2)
      (fun x heap store => heap.Within store compiled.module (compiled.natOfTextDCWith.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natOfTextDCWith.bound 1000 x) :=
  Verified.call_on (fun _ => True)
    (Verified.ImplementsTables.call (.ofA (compiled.natOfTextDCWith.trapFree.mono
      (fun x _ _ h => ⟨natOfTextDCWith_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => ⟨trivial, h⟩)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩⟩ _ =>
      natOfTextDCWith_eq _ _ x.2.2 (by have := h1.values.size_lt_memory32; omega)

/-! ## The closed forms at 1,000 frames -/

theorem natMulKara_room (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natMulKara.bound 1000 (u, v) ≤ 24 * (u.size + v.size) + 80 * min u.size v.size + 112 :=
  natMulKara_bound_le 998 u v hu hv

theorem intMulKara_room (x y : BigInt) (hx : x.mag.size < 2 ^ 32) (hy : y.mag.size < 2 ^ 32) :
    compiled.intMulKara.bound 1000 (x, y) ≤
      24 * (x.mag.size + y.mag.size) + 80 * min x.mag.size y.mag.size + 112 :=
  intMulKara_bound_le 997 x y hx hy

theorem natOfTextDC_room (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    compiled.natOfTextDC.bound 1000 s ≤ 7 * s.size + 168 :=
  natOfTextDC_bound_le 997 s hs

theorem intOfTextDC_room (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    compiled.intOfTextDC.bound 1000 s ≤ 7 * s.size + 168 :=
  intOfTextDC_bound_le 998 s hs

theorem natMulKaraWith_room (t : UInt64) (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.natMulKaraWith.bound 1000 (t, u, v) ≤
      24 * (u.size + v.size) + 80 * min u.size v.size + 112 :=
  natMulKaraWith_bound_le 999 t u v hu hv

theorem natOfTextDCWith_room (t E : UInt64) (s : Array UInt64) (hE1 : 1 ≤ E.toNat)
    (hE : E.toNat ≤ 2 ^ 32) (hs : s.size < 2 ^ 32) :
    compiled.natOfTextDCWith.bound 1000 (t, E, s) ≤ 19 * s.size + 262 :=
  natOfTextDCWith_bound_le 998 t E s hE1 hE hs

/-! ## The helpers

Each helper's theorem states that the module computes the Lean function without a trap.  The
helpers that update a workspace in place take it moved, so their theorems are `ImplementsA`
theorems with `Moved` arguments, as leanexe's `putPicks_implements` is, and they allocate nothing:
they need no room and leave `top` where it was. -/

/-- Function 2, `isDigitW`, returns the Lean function's value, from a ready store with room for
its bound, 0. -/
theorem isDigitW_call :
    Verified.CallSpec compiled.module compiled.tables 2 (fun x : UInt64 => isDigitW x)
      compiled.isDigitW.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.isDigitW.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

theorem isDigitW_bound (x : UInt64) : compiled.isDigitW.bound x = 0 := compiled.isDigitW.bound_eq x

/-- Function 7, `trimSeg`, returns the Lean function's value, the canonical limbs of a segment of
limbs (`trimSeg_eq`), from a ready store with room for its bound, at most `8 len + 56` bytes. -/
theorem trimSeg_call :
    Verified.CallSpec compiled.module compiled.tables 7
      (fun x : Array UInt64 × UInt64 × UInt64 => trimSeg x.1 x.2.1 x.2.2) compiled.trimSeg.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.trimSeg.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 12, `readInit`, returns the Lean function's value, from a ready store with room for
its bound, the block of `6 N` or `N` words. -/
theorem readInit_call :
    Verified.CallSpec compiled.module compiled.tables 12
      (fun x : Array UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
        readInit x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) compiled.readInit.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.readInit.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 23, `decimalValueDC`, returns the Lean function's value, the canonical limbs of the
value of its digits (`decimalValueDC_eq`), from a ready store with room for its bound at 1,000
frames, which `decimalValueDC_bound_le` bounds. -/
theorem decimalValueDC_call :
    Verified.CallSpec compiled.module compiled.tables 23
      (fun x : UInt64 × UInt64 × Array UInt64 × UInt64 × UInt64 =>
        decimalValueDC x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x => compiled.decimalValueDC.bound 1000 x) :=
  (Verified.ImplementsTables.call (.ofA (compiled.decimalValueDC.trapFree.mono
      (fun x _ _ h => ⟨decimalValueDC_fits 999 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

theorem addGen_bound (x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64) : compiled.addGen.bound x = 0 := by
  obtain ⟨⟨W⟩, a, b, c, d, e⟩ := x; exact compiled.addGen.bound_eq W a b c d e

theorem subGen_bound (x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64) : compiled.subGen.bound x = 0 := by
  obtain ⟨⟨W⟩, a, b, c, d, e⟩ := x; exact compiled.subGen.bound_eq W a b c d e

theorem baseMul_bound (x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64) : compiled.baseMul.bound x = 0 := by
  obtain ⟨⟨W⟩, a, b, c, d, e⟩ := x; exact compiled.baseMul.bound_eq W a b c d e

theorem mulAddSeg_bound (x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
    UInt64) : compiled.mulAddSeg.bound x = 0 := by
  obtain ⟨⟨W⟩, a, b, c, d⟩ := x; exact compiled.mulAddSeg.bound_eq W a b c d

/-- Function 3, `addGen`, computes the Lean function in place, allocating nothing. -/
theorem addGen_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 3
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
      addGen x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.addGen.trapFree.mono (fun x _ _ h => by rw [addGen_bound x]; exact h)
    fun x _ _ _ _ _ h => by rw [addGen_bound x] at h; exact h

/-- Function 4, `subGen`, computes the Lean function in place, allocating nothing. -/
theorem subGen_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 4
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
      subGen x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.subGen.trapFree.mono (fun x _ _ h => by rw [subGen_bound x]; exact h)
    fun x _ _ _ _ _ h => by rw [subGen_bound x] at h; exact h

/-- Function 5, `baseMul`, computes the Lean function in place, allocating nothing. -/
theorem baseMul_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 5
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
      baseMul x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.baseMul.trapFree.mono (fun x _ _ h => by rw [baseMul_bound x]; exact h)
    fun x _ _ _ _ _ h => by rw [baseMul_bound x] at h; exact h

/-- Function 11, `mulAddSeg`, computes the Lean function in place, allocating nothing. -/
theorem mulAddSeg_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 11
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 =>
      mulAddSeg x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.mulAddSeg.trapFree.mono (fun x _ _ h => by rw [mulAddSeg_bound x]; exact h)
    fun x _ _ _ _ _ h => by rw [mulAddSeg_bound x] at h; exact h

/-- Function 18, `kara`, computes the Lean function in place for every argument, allocating
nothing, with no premise on the depth. -/
theorem kara_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 18
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
      kara x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.kara.trapFree.mono
    (fun x _ _ h => ⟨kara_fits_all 999 (by omega) x, by rw [kara_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [kara_bound] at h; exact h

/-- Function 22, `readPass`, computes the Lean function in place for every argument, allocating
nothing, with no premise on the depth. -/
theorem readPass_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 22
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 =>
      readPass x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.readPass.trapFree.mono
    (fun x _ _ h => ⟨readPass_fits 999 (by omega) x, by rw [readPass_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [readPass_bound] at h; exact h

end Library.Numerics.Bignum.Second

#print axioms Library.Numerics.Bignum.natMulKara_eq
#print axioms Library.Numerics.Bignum.intMulKara_eq
#print axioms Library.Numerics.Bignum.natMulKara_canonical
#print axioms Library.Numerics.Bignum.intMulKara_canonical
#print axioms Library.Numerics.Bignum.natMulKaraWith_eq
#print axioms Library.Numerics.Bignum.kara_spec
#print axioms Library.Numerics.Bignum.natOfTextDC_eq
#print axioms Library.Numerics.Bignum.natOfTextDCWith_eq
#print axioms Library.Numerics.Bignum.intOfTextDC_eq
#print axioms Library.Numerics.Bignum.intOfTextDC_eq_intOfText
#print axioms Library.Numerics.Bignum.natOfTextDC_canonical
#print axioms Library.Numerics.Bignum.intOfTextDC_canonical
#print axioms Library.Numerics.Bignum.decimalValueDC_eq
#print axioms Library.Numerics.Bignum.natReadSpec_eq
#print axioms Library.Numerics.Bignum.natAddS_eq_natAdd
#print axioms Library.Numerics.Bignum.natSubS_eq_natSub
#print axioms Library.Numerics.Bignum.natDivModCheckedS_eq_natDivModChecked
#print axioms Library.Numerics.Bignum.Second.natMulKara_call
#print axioms Library.Numerics.Bignum.Second.intMulKara_call
#print axioms Library.Numerics.Bignum.Second.natOfTextDC_call
#print axioms Library.Numerics.Bignum.Second.intOfTextDC_call
#print axioms Library.Numerics.Bignum.Second.natMulKaraWith_call
#print axioms Library.Numerics.Bignum.Second.natOfTextDCWith_call
#print axioms Library.Numerics.Bignum.Second.natMulKara_room
#print axioms Library.Numerics.Bignum.Second.intMulKara_room
#print axioms Library.Numerics.Bignum.Second.natOfTextDC_room
#print axioms Library.Numerics.Bignum.Second.intOfTextDC_room
#print axioms Library.Numerics.Bignum.Second.natMulKaraWith_room
#print axioms Library.Numerics.Bignum.Second.natOfTextDCWith_room
#print axioms Library.Numerics.Bignum.Second.kara_trapFree
#print axioms Library.Numerics.Bignum.Second.readPass_trapFree
#print axioms Library.Numerics.Bignum.Second.decimalValueDC_call
#print axioms Library.Numerics.Bignum.Second.kara_fits_all
