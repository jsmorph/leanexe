/-
Derived from CompCert 3.18, the files `x86_64/Archi.v`, `aarch64/Archi.v`, and `arm/Archi.v`.
CompCert is Copyright Institut National de Recherche en Informatique et en Automatique (INRIA) and
AbsInt Angewandte Informatik GmbH, and its source files state INRIA's copyright.

This file is distributed under the GNU Lesser General Public License, version 2.1 or (at your
option) any later version, one of the two licenses CompCert offers for its source files.  The
text of version 2.1 is in `LICENSE-LGPL-2.1` in this directory.

Changed from CompCert on 2026-10-26 and 2026-11-04: transcribed from Coq into Lean, with the
changes that `LeanExe/Native/NOTICE` and the documentation comment below describe.
-/

/-!
The parameters of CompCert 3.18's `Archi.v` that the copy depends on: the width of pointers and
the NaN choices of the floating-point operations.

`ptr64` is true on x86-64 and AArch64 and false on ARM.  A NaN is described, as in Flocq, by its
sign and its payload, the fraction field read as a positive number.  The fields `default_nan_64`
and `default_nan_32` record `Archi.v`'s default NaNs, which the operations use only through the
choice functions.  The three targets set `float_conversion_default_nan` and
`float_of_single_preserves_sNaN` to false, and the copy fixes those values.  All three are
little-endian: `arm/Archi.v` leaves `big_endian` a parameter, and the configuration `armv7m-eabihf`
sets it to false.  `x86_64`, `aarch64`, and `arm` are the instances, so a theorem stated for every
`Archi` holds on each.
-/

namespace LClight

structure Archi where
  ptr64 : Bool
  default_nan_64 : Bool × Nat
  default_nan_32 : Bool × Nat
  choose_nan_64 : List (Bool × Nat) → Bool × Nat
  choose_nan_32 : List (Bool × Nat) → Bool × Nat

namespace Archi

/-- `x86_64/Archi.v`: the default NaN is negative, and the result takes the first NaN
argument. -/
def x86_64 : Archi where
  ptr64 := true
  default_nan_64 := (true, 2 ^ 51)
  default_nan_32 := (true, 2 ^ 22)
  choose_nan_64 := fun l => match l with
    | [] => (true, 2 ^ 51)
    | n :: _ => n
  choose_nan_32 := fun l => match l with
    | [] => (true, 2 ^ 22)
    | n :: _ => n

/-- `Archi.choose_nan` of `aarch64/Archi.v` and `arm/Archi.v`: the first signaling NaN, else the
first NaN, else the default. -/
def choose_nan (is_signaling : Nat → Bool) (default : Bool × Nat) (l0 : List (Bool × Nat)) :
    Bool × Nat :=
  match l0.find? (fun n => is_signaling n.2) with
  | some n => n
  | none =>
      match l0 with
      | [] => default
      | n :: _ => n

/-- `aarch64/Archi.v`: the default NaN is positive.  A payload is signaling when its top bit,
bit 51 or bit 22, is clear. -/
def aarch64 : Archi where
  ptr64 := true
  default_nan_64 := (false, 2 ^ 51)
  default_nan_32 := (false, 2 ^ 22)
  choose_nan_64 := choose_nan (fun p => !p.testBit 51) (false, 2 ^ 51)
  choose_nan_32 := choose_nan (fun p => !p.testBit 22) (false, 2 ^ 22)

/-- `arm/Archi.v`: 32-bit pointers, and the NaN choices of `aarch64/Archi.v`. -/
def arm : Archi where
  ptr64 := false
  default_nan_64 := (false, 2 ^ 51)
  default_nan_32 := (false, 2 ^ 22)
  choose_nan_64 := choose_nan (fun p => !p.testBit 51) (false, 2 ^ 51)
  choose_nan_32 := choose_nan (fun p => !p.testBit 22) (false, 2 ^ 22)

end Archi

end LClight
