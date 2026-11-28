module

public import Library.Numerics.Bignum.Third.Bound
public import Verified.Call
public import Verified.Congr

@[expose] public section

/-!
The call theorems of the third iteration's module.  Functions 65, 66, and 67 are the library's new
divisions: `natDivModCheckedBZ`, the quotient and the remainder of naturals with a status for a
zero divisor, and `intTDivModCheckedBZ` and `intEDivModCheckedBZ`, the truncated and the Euclidean
divisions of integers, each by Burnikel and Ziegler's recursion above the threshold.  Functions 72
and 73, `natToTextDC` and `intToTextDC`, are the new printers of naturals and integers by
Algorithm 1.26.  Functions 64 and 71, `natDivModCheckedBZWith` and `natToTextDCWith`, take the
thresholds as arguments, for the timings, and meet the same specifications for every value of
them.  The compiler exports every function that it compiles, so the module also exports the
helpers; the theorems of the new helpers state that the module computes the Lean function without
a trap, and `DivBase.lean` to `PrintText.lean` prove what those Lean functions compute.

Each call theorem composes the generated `trapFree` theorem with the export's equation through
`Verified.call_on`, as the second iteration's `natMulKara_call` does.  The code of each export
takes the call depth, since it calls the recursions `rdiv`, `toChunks`, and `kara`, and its
`trapFree` holds under `fits 1000 x`, which `Bound.lean` proves for every argument: the call
theorems carry no depth premise.  The room is the generated bound at 1,000 frames, and
`Bound.lean` bounds it by a closed form linear in the lengths of the arguments.
-/

namespace Library.Numerics.Bignum.Third

open Library.Numerics.MultiPrecision (value Digits)
open LeanExe.ProofKit

/-! ## Export indices -/

theorem natDivModCheckedBZWith_export :
    ({ name := "natDivModCheckedBZWith", funcIdx := 64 } : Wasm.Export) ∈
      compiled.module.exports := by
  decide +kernel

theorem natDivModCheckedBZ_export :
    ({ name := "natDivModCheckedBZ", funcIdx := 65 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intTDivModCheckedBZ_export :
    ({ name := "intTDivModCheckedBZ", funcIdx := 66 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intEDivModCheckedBZ_export :
    ({ name := "intEDivModCheckedBZ", funcIdx := 67 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natToTextDCWith_export :
    ({ name := "natToTextDCWith", funcIdx := 71 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem natToTextDC_export :
    ({ name := "natToTextDC", funcIdx := 72 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem intToTextDC_export :
    ({ name := "intToTextDC", funcIdx := 73 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-! ## The interface -/

/-- Function 65, `natDivModCheckedBZ`, called with two canonical naturals, returns the status 1
and two zeros for a zero divisor, and otherwise the status 0 with the canonical limbs of the
quotient and the remainder: the first iteration's `natDivModCheckedSpec`. -/
theorem natDivModCheckedBZ_call :
    Verified.Call compiled.module compiled.tables 65
      (fun x : Array UInt64 × Array UInt64 => natDivModCheckedSpec (value x.1) (value x.2))
      (fun x heap store => (Canonical x.1 ∧ Canonical x.2) ∧
        heap.Within store compiled.module (compiled.natDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natDivModCheckedBZ.bound 1000 x) :=
  Verified.call_on (fun x => Canonical x.1 ∧ Canonical x.2)
    (Verified.ImplementsTables.call (.ofA (compiled.natDivModCheckedBZ.trapFree.mono
      (fun x _ _ h => ⟨natDivModCheckedBZ_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      natDivModCheckedBZ_eq hu hv
        (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 66, `intTDivModCheckedBZ`, called with two canonical integers, returns the status 1
and two zeros for a zero divisor, and otherwise the status 0 with `Int.tdiv` and `Int.tmod` of
their integers: the first iteration's `intTDivModCheckedSpec`. -/
theorem intTDivModCheckedBZ_call :
    Verified.Call compiled.module compiled.tables 66
      (fun x : BigInt × BigInt => intTDivModCheckedSpec x.1.toInt x.2.toInt)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧
        heap.Within store compiled.module (compiled.intTDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.intTDivModCheckedBZ.bound 1000 x) :=
  Verified.call_on (fun x => x.1.Canonical ∧ x.2.Canonical)
    (Verified.ImplementsTables.call (.ofA (compiled.intTDivModCheckedBZ.trapFree.mono
      (fun x _ _ h => ⟨intTDivModCheckedBZ_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩, ⟨_, _, _, _, ⟨_, _, h2⟩⟩⟩ ⟨hx, hy⟩ =>
      by
      have s1 : x.1.mag.size < 536870912 := h1.values.size_lt_memory32
      have s2 : x.2.mag.size < 536870912 := h2.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      rw [BigInt.eq_ofInt hy] at s2
      have h := intTDivModCheckedBZ_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← BigInt.eq_ofInt hx, ← BigInt.eq_ofInt hy] at h
      exact h

/-- Function 67, `intEDivModCheckedBZ`, called with two canonical integers, returns the status 1
and two zeros for a zero divisor, and otherwise the status 0 with Lean's `/` and `%` of their
integers: the first iteration's `intEDivModCheckedSpec`. -/
theorem intEDivModCheckedBZ_call :
    Verified.Call compiled.module compiled.tables 67
      (fun x : BigInt × BigInt => intEDivModCheckedSpec x.1.toInt x.2.toInt)
      (fun x heap store => (x.1.Canonical ∧ x.2.Canonical) ∧
        heap.Within store compiled.module (compiled.intEDivModCheckedBZ.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.intEDivModCheckedBZ.bound 1000 x) :=
  Verified.call_on (fun x => x.1.Canonical ∧ x.2.Canonical)
    (Verified.ImplementsTables.call (.ofA (compiled.intEDivModCheckedBZ.trapFree.mono
      (fun x _ _ h => ⟨intEDivModCheckedBZ_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩, ⟨_, _, _, _, ⟨_, _, h2⟩⟩⟩ ⟨hx, hy⟩ =>
      by
      have s1 : x.1.mag.size < 536870912 := h1.values.size_lt_memory32
      have s2 : x.2.mag.size < 536870912 := h2.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      rw [BigInt.eq_ofInt hy] at s2
      have h := intEDivModCheckedBZ_eq (a := x.1.toInt) (b := x.2.toInt) (by omega) (by omega)
      rw [← BigInt.eq_ofInt hx, ← BigInt.eq_ofInt hy] at h
      exact h

/-- Function 72, `natToTextDC`, called with a canonical natural, returns the bytes of Lean's
`toString` of it, one byte to a word: `printSpec` of the natural as an integer, the text of the
first iteration's `intToText`. -/
theorem natToTextDC_call :
    Verified.Call compiled.module compiled.tables 72
      (fun u : Array UInt64 => printSpec (value u : ℤ))
      (fun u heap store => Canonical u ∧
        heap.Within store compiled.module (compiled.natToTextDC.bound 1000 u))
      (fun u heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.natToTextDC.bound 1000 u) :=
  Verified.call_on (fun u => Canonical u)
    (Verified.ImplementsTables.call (.ofA (compiled.natToTextDC.trapFree.mono
      (fun x _ _ h => ⟨natToTextDC_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ u ⟨_, _, h1⟩ hu =>
      natToTextDC_eq hu (by have := h1.values.size_lt_memory32; omega)

/-- Function 73, `intToTextDC`, called with a canonical integer, returns the bytes of Lean's
`toString` of its integer, one byte to a word: the first iteration's `printSpec`. -/
theorem intToTextDC_call :
    Verified.Call compiled.module compiled.tables 73
      (fun x : BigInt => printSpec x.toInt)
      (fun x heap store => x.Canonical ∧
        heap.Within store compiled.module (compiled.intToTextDC.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.intToTextDC.bound 1000 x) :=
  Verified.call_on (fun x => x.Canonical)
    (Verified.ImplementsTables.call (.ofA (compiled.intToTextDC.trapFree.mono
      (fun x _ _ h => ⟨intToTextDC_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, h1⟩⟩ hx => by
      have s1 : x.mag.size < 536870912 := h1.values.size_lt_memory32
      rw [BigInt.eq_ofInt hx] at s1
      have h := intToTextDC_eq (z := x.toInt) (by omega)
      rw [← BigInt.eq_ofInt hx] at h
      exact h

/-! ## The entries with parameters -/

/-- Function 64, `natDivModCheckedBZWith`, called with any thresholds and two canonical naturals,
returns `natDivModCheckedSpec` of them. -/
theorem natDivModCheckedBZWith_call :
    Verified.Call compiled.module compiled.tables 64
      (fun x : UInt64 × UInt64 × UInt64 × Array UInt64 × Array UInt64 =>
        natDivModCheckedSpec (value x.2.2.2.1) (value x.2.2.2.2))
      (fun x heap store => (Canonical x.2.2.2.1 ∧ Canonical x.2.2.2.2) ∧
        heap.Within store compiled.module (compiled.natDivModCheckedBZWith.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natDivModCheckedBZWith.bound 1000 x) :=
  Verified.call_on (fun x => Canonical x.2.2.2.1 ∧ Canonical x.2.2.2.2)
    (Verified.ImplementsTables.call (.ofA (compiled.natDivModCheckedBZWith.trapFree.mono
      (fun x _ _ h => ⟨natDivModCheckedBZWith_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, _, _, ⟨_, _, _, _, ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩⟩⟩⟩
        ⟨hu, hv⟩ =>
      natDivModCheckedBZWith_eq _ _ _ hu hv
        (by have := h1.values.size_lt_memory32; omega)
        (by have := h2.values.size_lt_memory32; omega)

/-- Function 71, `natToTextDCWith`, called with any thresholds, any level of the leaves, and a
canonical natural, returns `printSpec` of the natural as an integer. -/
theorem natToTextDCWith_call :
    Verified.Call compiled.module compiled.tables 71
      (fun x : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 => printSpec (value x.2.2.2.2 : ℤ))
      (fun x heap store => Canonical x.2.2.2.2 ∧
        heap.Within store compiled.module (compiled.natToTextDCWith.bound 1000 x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.natToTextDCWith.bound 1000 x) :=
  Verified.call_on (fun x => Canonical x.2.2.2.2)
    (Verified.ImplementsTables.call (.ofA (compiled.natToTextDCWith.trapFree.mono
      (fun x _ _ h => ⟨natToTextDCWith_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun)
    (fun _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, _, _, ⟨_, _, _, _, ⟨_, _, _, _, ⟨_, _, h1⟩⟩⟩⟩⟩ hu =>
      natToTextDCWith_eq _ _ _ _ hu (by have := h1.values.size_lt_memory32; omega)

/-! ## The closed forms at 1,000 frames -/

theorem natDivModCheckedBZ_room (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.natDivModCheckedBZ.bound 1000 (u, v) ≤ 128 * u.size + 144 * v.size + 824 :=
  natDivModCheckedBZ_bound_le 998 u v hu hv

theorem intTDivModCheckedBZ_room (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intTDivModCheckedBZ.bound 1000 (x, y) ≤ 128 * x.mag.size + 144 * y.mag.size + 824 :=
  intTDivModCheckedBZ_bound_le 997 x y hx hy

theorem intEDivModCheckedBZ_room (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intEDivModCheckedBZ.bound 1000 (x, y) ≤
      248 * x.mag.size + 248 * y.mag.size + 1472 :=
  intEDivModCheckedBZ_bound_le 997 x y hx hy

theorem natToTextDC_room (u : Array UInt64) (hs : u.size < 2 ^ 32) :
    compiled.natToTextDC.bound 1000 u ≤ 438 * u.size + 1968 :=
  natToTextDC_bound_le 997 u hs

theorem intToTextDC_room (x : BigInt) (hs : x.mag.size < 2 ^ 32) :
    compiled.intToTextDC.bound 1000 x ≤ 438 * x.mag.size + 1968 :=
  intToTextDC_bound_le 998 x hs

theorem natDivModCheckedBZWith_room (t T D : UInt64) (u v : Array UInt64)
    (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natDivModCheckedBZWith.bound 1000 (t, T, D, u, v) ≤
      128 * u.size + 144 * v.size + 824 :=
  natDivModCheckedBZWith_bound_le 999 t T D u v hu hv

theorem natToTextDCWith_room (t T L P : UInt64) (u : Array UInt64) (hs : u.size < 2 ^ 32) :
    compiled.natToTextDCWith.bound 1000 (t, T, L, P, u) ≤ 438 * u.size + 1968 :=
  natToTextDCWith_bound_le 998 t T L P u hs

/-! ## The helpers

Each helper's theorem states that the module computes the Lean function without a trap.  The
helpers that update the workspace in place take it moved, as the second iteration's `kara` does,
and they allocate nothing: they need no room and leave `top` where it was.  The helpers that call
a recursion need no premise on the depth.  `toChunks` has no theorem of its own: its level is an
argument, and its frames are those of `chunksDC`, which starts it below level 40. -/

/-- Function 28, `trialAt`, the trial digit of step D3 at offsets of the workspace, returns the
Lean function's value. -/
theorem trialAt_call :
    Verified.CallSpec compiled.module compiled.tables 28
      (fun x : Array UInt64 × UInt64 × UInt64 × UInt64 => trialAt x.1 x.2.1 x.2.2.1 x.2.2.2)
      compiled.trialAt.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.trialAt.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

theorem trialAt_bound (x : Array UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.trialAt.bound x = 0 := by
  obtain ⟨W, a, b, c⟩ := x; exact compiled.trialAt.bound_eq W a b c

/-- Function 29, `mulSubSeg`, step D4 in place, computes the Lean function, allocating nothing. -/
theorem mulSubSeg_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 29
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 =>
      mulSubSeg x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.mulSubSeg.trapFree.mono
    (fun x _ _ h => by obtain ⟨⟨W⟩, a, b, c, d⟩ := x; rw [compiled.mulSubSeg.bound_eq]; exact h)
    fun x _ _ _ _ _ h => by
      obtain ⟨⟨W⟩, a, b, c, d⟩ := x; rw [compiled.mulSubSeg.bound_eq] at h; exact h

/-- Function 30, `baseDiv`, the base case of the recursion in place, computes the Lean function,
allocating nothing. -/
theorem baseDiv_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 30
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 =>
      baseDiv x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.baseDiv.trapFree.mono
    (fun x _ _ h => by obtain ⟨⟨W⟩, a, b, c, d, e⟩ := x; rw [compiled.baseDiv.bound_eq]; exact h)
    fun x _ _ _ _ _ h => by
      obtain ⟨⟨W⟩, a, b, c, d, e⟩ := x; rw [compiled.baseDiv.bound_eq] at h; exact h

/-- Function 33, `subFix`, the subtraction and the corrections of a half of Algorithm 1.8 in
place, computes the Lean function, allocating nothing. -/
theorem subFix_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 33
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 =>
      subFix x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.subFix.trapFree.mono
    (fun x _ _ h => by
      obtain ⟨⟨W⟩, a, b, c, d, e, f, g, i⟩ := x; rw [compiled.subFix.bound_eq]; exact h)
    fun x _ _ _ _ _ h => by
      obtain ⟨⟨W⟩, a, b, c, d, e, f, g, i⟩ := x; rw [compiled.subFix.bound_eq] at h; exact h

/-- Function 39, `divSmallSeg`, the short division of a segment in place, computes the Lean
function, allocating nothing. -/
theorem divSmallSeg_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 39
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 =>
      divSmallSeg x.1.val x.2.1 x.2.2.1 x.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.divSmallSeg.trapFree.mono
    (fun x _ _ h => by obtain ⟨⟨W⟩, a, b, c⟩ := x; rw [compiled.divSmallSeg.bound_eq]; exact h)
    fun x _ _ _ _ _ h => by
      obtain ⟨⟨W⟩, a, b, c⟩ := x; rw [compiled.divSmallSeg.bound_eq] at h; exact h

/-- Function 47, `leafChunks`, the repeated division by `10^9` of a leaf in place, computes the
Lean function, allocating nothing. -/
theorem leafChunks_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 47
    (fun x : LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 =>
      leafChunks x.1.val x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.leafChunks.trapFree.mono
    (fun x _ _ h => by obtain ⟨⟨W⟩, a, b, c, d⟩ := x; rw [compiled.leafChunks.bound_eq]; exact h)
    fun x _ _ _ _ _ h => by
      obtain ⟨⟨W⟩, a, b, c, d⟩ := x; rw [compiled.leafChunks.bound_eq] at h; exact h

/-- Function 43, `signTDiv`, the signs of the truncated division, computes the Lean function,
allocating nothing. -/
theorem signTDiv_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 43
    (fun x : Bool × Bool × LeanExe.Pipeline.Moved (Array UInt64) ×
        LeanExe.Pipeline.Moved (Array UInt64) => signTDiv x.1 x.2.1 x.2.2.1.val x.2.2.2.val)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.signTDiv.trapFree.mono
    (fun x _ _ h => by obtain ⟨a, b, ⟨q⟩, ⟨r⟩⟩ := x; rw [compiled.signTDiv.bound_eq]; exact h)
    fun x _ _ _ _ _ h => by
      obtain ⟨a, b, ⟨q⟩, ⟨r⟩⟩ := x; rw [compiled.signTDiv.bound_eq] at h; exact h

/-- Function 44, `signEDiv`, the signs and the correction of the Euclidean division, returns the
Lean function's value from a ready store with room for its bound. -/
theorem signEDiv_call :
    Verified.CallSpec compiled.module compiled.tables 44
      (fun x : Bool × Bool × Array UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
          LeanExe.Pipeline.Moved (Array UInt64) =>
        signEDiv x.1 x.2.1 x.2.2.1 x.2.2.2.1.val x.2.2.2.2.val)
      compiled.signEDiv.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.signEDiv.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 50, `textOfChunks`, returns the Lean function's value, the text of the chunks
(`textOfChunks_eq`), from a ready store with room for its bound, at most `80 K + 280` bytes
(`textOfChunks_bound_le`). -/
theorem textOfChunks_call :
    Verified.CallSpec compiled.module compiled.tables 50
      (fun x : Bool × Array UInt64 × UInt64 × UInt64 => textOfChunks x.1 x.2.1 x.2.2.1 x.2.2.2)
      compiled.textOfChunks.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.textOfChunks.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- Function 55, `kara`, computes the Lean function in place for every argument, allocating
nothing, with no premise on the depth. -/
theorem kara_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 55
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 =>
      kara x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.kara.trapFree.mono
    (fun x _ _ h => ⟨kara_fits_all 1000 (by omega) x, by rw [kara_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [kara_bound] at h; exact h

/-- Function 56, `mulChunk`, computes the Lean function in place for every argument, allocating
nothing, with no premise on the depth. -/
theorem mulChunk_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 56
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 =>
      mulChunk x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.mulChunk.trapFree.mono
    (fun x _ _ h => ⟨mulChunk_fits 1000 (by omega) x, by rw [mulChunk_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [mulChunk_bound] at h; exact h

/-- Function 57, `mulAcc`, computes the Lean function in place for every argument, allocating
nothing, with no premise on the depth. -/
theorem mulAcc_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 57
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 =>
      mulAcc x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.mulAcc.trapFree.mono
    (fun x _ _ h => ⟨mulAcc_fits 1000 (by omega) x, by rw [mulAcc_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [mulAcc_bound] at h; exact h

/-- Function 58, `halfStep`, computes the Lean function in place for every argument, allocating
nothing, with no premise on the depth. -/
theorem halfStep_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 58
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 × UInt64 =>
      halfStep x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.halfStep.trapFree.mono
    (fun x _ _ h => ⟨halfStep_fits 1000 (by omega) x, by rw [halfStep_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [halfStep_bound] at h; exact h

/-- Function 59, `lowHalf`, computes the Lean function in place for every argument, allocating
nothing, with no premise on the depth. -/
theorem lowHalf_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 59
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 × UInt64 =>
      lowHalf x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.lowHalf.trapFree.mono
    (fun x _ _ h => ⟨lowHalf_fits 1000 (by omega) x, by rw [lowHalf_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [lowHalf_bound] at h; exact h

/-- Function 60, `rdiv`, Algorithm 1.8, computes the Lean function in place for every argument,
allocating nothing, with no premise on the depth. -/
theorem rdiv_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 60
    (fun x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 =>
      rdiv x.1 x.2.1 x.2.2.1.val x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.rdiv.trapFree.mono
    (fun x _ _ h => ⟨rdiv_fits_all 1000 (by omega) x, by rw [rdiv_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [rdiv_bound] at h; exact h

/-- Function 61, `tdiv`, the truncated division of the last block, computes the Lean function in
place for every argument, allocating nothing, with no premise on the depth. -/
theorem tdiv_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 61
    (fun x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 =>
      tdiv x.1 x.2.1 x.2.2.1.val x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.tdiv.trapFree.mono
    (fun x _ _ h => ⟨tdiv_fits 1000 (by omega) x, by rw [tdiv_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [tdiv_bound] at h; exact h

/-- Function 62, `udiv`, Algorithm 1.9, computes the Lean function in place for every argument,
allocating nothing, with no premise on the depth. -/
theorem udiv_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 62
    (fun x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 =>
      udiv x.1 x.2.1 x.2.2.1.val x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.udiv.trapFree.mono
    (fun x _ _ h => ⟨udiv_fits 1000 (by omega) x, by rw [udiv_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [udiv_bound] at h; exact h

/-- Function 63, `divSeg`, the division of segments with the normalization, computes the Lean
function in place for every argument, allocating nothing, with no premise on the depth. -/
theorem divSeg_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 63
    (fun x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 ×
        UInt64 × UInt64 × UInt64 =>
      divSeg x.1 x.2.1 x.2.2.1.val x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.divSeg.trapFree.mono
    (fun x _ _ h => ⟨divSeg_fits 1000 (by omega) x, by rw [divSeg_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [divSeg_bound] at h; exact h

/-- Function 68, `powInit`, the powers `10^(9 · 2^i)` by squaring, computes the Lean function in
place for every argument, allocating nothing, with no premise on the depth. -/
theorem powInit_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 68
    (fun x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 =>
      powInit x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun _ heap store => heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.powInit.trapFree.mono
    (fun x _ _ h => ⟨powInit_fits 1000 (by omega) x, by rw [powInit_bound]; exact h⟩)
    fun x _ _ _ _ _ h => by rw [powInit_bound] at h; exact h

/-- Function 70, `chunksDC`, returns the Lean function's value, the chunks of nine digits of its
natural (`chunksDC_spec`), from a ready store with room for its bound at 1,000 frames, which
`chunksDC_bound_le` bounds, with no premise on the depth. -/
theorem chunksDC_call :
    Verified.CallSpec compiled.module compiled.tables 70
      (fun x : UInt64 × UInt64 × UInt64 × Array UInt64 => chunksDC x.1 x.2.1 x.2.2.1 x.2.2.2)
      (fun x => compiled.chunksDC.bound 1000 x) :=
  (Verified.ImplementsTables.call (.ofA (compiled.chunksDC.trapFree.mono
      (fun x _ _ h => ⟨chunksDC_fits 1000 (by omega) x, h⟩) fun _ _ _ _ _ _ h => h))
      compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

end Library.Numerics.Bignum.Third

#print axioms Library.Numerics.Bignum.natDivModCheckedBZ_eq
#print axioms Library.Numerics.Bignum.natDivModCheckedBZWith_eq
#print axioms Library.Numerics.Bignum.natDivModCheckedBZ_eq_natDivModChecked
#print axioms Library.Numerics.Bignum.natDivModBZ_eq_natDivMod
#print axioms Library.Numerics.Bignum.intTDivModCheckedBZ_eq
#print axioms Library.Numerics.Bignum.intEDivModCheckedBZ_eq
#print axioms Library.Numerics.Bignum.intTDivModCheckedBZ_eq_intTDivModChecked
#print axioms Library.Numerics.Bignum.intEDivModCheckedBZ_eq_intEDivModChecked
#print axioms Library.Numerics.Bignum.natDivModBZ_canonical
#print axioms Library.Numerics.Bignum.intDivModCheckedBZ_canonical
#print axioms Library.Numerics.Bignum.rdiv_spec
#print axioms Library.Numerics.Bignum.udiv_spec
#print axioms Library.Numerics.Bignum.divSeg_spec
#print axioms Library.Numerics.Bignum.natToTextDC_eq
#print axioms Library.Numerics.Bignum.natToTextDCWith_eq
#print axioms Library.Numerics.Bignum.natToTextDC_eq_intToText
#print axioms Library.Numerics.Bignum.intToTextDC_eq
#print axioms Library.Numerics.Bignum.intToTextDC_eq_intToText
#print axioms Library.Numerics.Bignum.intToTextDC_toString
#print axioms Library.Numerics.Bignum.readSpec_intToTextDC
#print axioms Library.Numerics.Bignum.intOfText_intToTextDC
#print axioms Library.Numerics.Bignum.chunksDC_spec
#print axioms Library.Numerics.Bignum.Third.natDivModCheckedBZ_call
#print axioms Library.Numerics.Bignum.Third.intTDivModCheckedBZ_call
#print axioms Library.Numerics.Bignum.Third.intEDivModCheckedBZ_call
#print axioms Library.Numerics.Bignum.Third.natToTextDC_call
#print axioms Library.Numerics.Bignum.Third.intToTextDC_call
#print axioms Library.Numerics.Bignum.Third.natDivModCheckedBZWith_call
#print axioms Library.Numerics.Bignum.Third.natToTextDCWith_call
#print axioms Library.Numerics.Bignum.Third.natDivModCheckedBZ_room
#print axioms Library.Numerics.Bignum.Third.intTDivModCheckedBZ_room
#print axioms Library.Numerics.Bignum.Third.intEDivModCheckedBZ_room
#print axioms Library.Numerics.Bignum.Third.natToTextDC_room
#print axioms Library.Numerics.Bignum.Third.intToTextDC_room
#print axioms Library.Numerics.Bignum.Third.natDivModCheckedBZWith_room
#print axioms Library.Numerics.Bignum.Third.natToTextDCWith_room
#print axioms Library.Numerics.Bignum.Third.rdiv_trapFree
#print axioms Library.Numerics.Bignum.Third.divSeg_trapFree
#print axioms Library.Numerics.Bignum.Third.chunksDC_call
#print axioms Library.Numerics.Bignum.Third.rdiv_fits_all
