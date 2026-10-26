import Interpreter.Wasm.IEEE64
import LeanExe.Native.Clight.Integers

/-!
The floating-point numbers of CompCert 3.18's `lib/Floats.v` and the parameters of
`x86_64/Archi.v` and `aarch64/Archi.v` that they depend on.

A `float` or `float32` is its IEEE 754 bit pattern, which is in bijection with Flocq's
`binary64` or `binary32` value, NaN payloads included.  Where Flocq's operation returns a number
or an infinity, the copy returns Talos's `Wasm.IEEE64` or `Wasm.IEEE32` result, which LeanExe's
`F64*` and `F32*` lemmas relate to Lean's `Float.Model`.  Where Flocq's operation returns a NaN,
which happens exactly when the Talos operation returns its canonical NaN, the copy computes the
NaN as `Floats.v` does, from the architecture's choice function `Archi.choose_nan_64` or
`choose_nan_32`.  `Archi` holds these functions, so a theorem stated for every `Archi` holds on
both targets; `x86_64` and `aarch64` are the two instances.  `of_single` and `to_single`, which
Talos computes with Lean's native floats, are defined here from Talos's exact rounding helpers.

Both targets set `float_conversion_default_nan` and `float_of_single_preserves_sNaN` to false,
and the copy fixes those values.  Only the operations that `Cop.lean` and `Events.lean` use are
copied.
-/

namespace LClight

/-- `Floats.float`, a binary64 bit pattern. -/
abbrev float := UInt64
/-- `Floats.float32`, a binary32 bit pattern. -/
abbrev float32 := UInt32

/-- The NaN parameters of `Archi.v`.  A NaN is described, as in Flocq, by its sign and its
payload, the fraction field read as a positive number. -/
structure Archi where
  default_nan_64 : Bool × Nat
  default_nan_32 : Bool × Nat
  choose_nan_64 : List (Bool × Nat) → Bool × Nat
  choose_nan_32 : List (Bool × Nat) → Bool × Nat

namespace Archi

/-- `x86_64/Archi.v`: the default NaN is negative, and the result takes the first NaN
argument. -/
def x86_64 : Archi where
  default_nan_64 := (true, 2 ^ 51)
  default_nan_32 := (true, 2 ^ 22)
  choose_nan_64 := fun l => match l with
    | [] => (true, 2 ^ 51)
    | n :: _ => n
  choose_nan_32 := fun l => match l with
    | [] => (true, 2 ^ 22)
    | n :: _ => n

/-- `Archi.choose_nan` of `aarch64/Archi.v`: the first signaling NaN, else the first NaN, else
the default. -/
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
  default_nan_64 := (false, 2 ^ 51)
  default_nan_32 := (false, 2 ^ 22)
  choose_nan_64 := choose_nan (fun p => !p.testBit 51) (false, 2 ^ 51)
  choose_nan_32 := choose_nan (fun p => !p.testBit 22) (false, 2 ^ 22)

end Archi

/-- `quiet_nan_64_payload`: the payload with its quiet bit set, reduced to 52 bits. -/
def quiet_nan_64_payload (p : Nat) : Nat := (p ||| 2 ^ 51) % 2 ^ 52

/-- `quiet_nan_64`: the NaN of sign `s` and the quiet payload of `p`. -/
def quiet_nan_64 (sp : Bool × Nat) : float :=
  UInt64.ofNat ((if sp.1 then 2 ^ 63 else 0) + 0x7FF * 2 ^ 52 + quiet_nan_64_payload sp.2)

def quiet_nan_32_payload (p : Nat) : Nat := (p ||| 2 ^ 22) % 2 ^ 23

def quiet_nan_32 (sp : Bool × Nat) : float32 :=
  UInt32.ofNat ((if sp.1 then 2 ^ 31 else 0) + 0xFF * 2 ^ 23 + quiet_nan_32_payload sp.2)

/-- `cmp_of_comparison`. -/
def cmp_of_comparison (c : comparison) (x : Option Ordering) : Bool :=
  match c, x with
  | .Ceq, some .eq => true
  | .Ceq, _ => false
  | .Cne, some .eq => false
  | .Cne, _ => true
  | .Clt, some .lt => true
  | .Clt, _ => false
  | .Cle, some .lt => true
  | .Cle, some .eq => true
  | .Cle, _ => false
  | .Cgt, some .gt => true
  | .Cgt, _ => false
  | .Cge, some .gt => true
  | .Cge, some .eq => true
  | .Cge, _ => false

namespace Float

open Wasm

/-- `Float.cons_pl`: the sign and payload of `x` before `l` when `x` is a NaN. -/
def cons_pl (x : float) (l : List (Bool × Nat)) : List (Bool × Nat) :=
  if IEEE64.isNaN x then (IEEE64.sign x, IEEE64.fraction x) :: l else l

def unop_nan (A : Archi) (x : float) : float :=
  quiet_nan_64 (A.choose_nan_64 (cons_pl x []))

def binop_nan (A : Archi) (x y : float) : float :=
  quiet_nan_64 (A.choose_nan_64 (cons_pl x (cons_pl y [])))

/-- A Talos result `r` of an operation on `x` and `y`, with its NaN replaced by Flocq's. -/
def binop (A : Archi) (r x y : float) : float :=
  if IEEE64.isNaN r then binop_nan A x y else r

def zero : float := 0

def add (A : Archi) (x y : float) : float := binop A (IEEE64.add x y) x y
def sub (A : Archi) (x y : float) : float := binop A (IEEE64.sub x y) x y
def mul (A : Archi) (x y : float) : float := binop A (IEEE64.mul x y) x y
def div (A : Archi) (x y : float) : float := binop A (IEEE64.div x y) x y

def sqrt (A : Archi) (x : float) : float :=
  let r := IEEE64.sqrt x
  if IEEE64.isNaN r then unop_nan A x else r

/-- `Bopp` with `neg_nan`, which keeps a NaN's payload: the sign bit flipped. -/
def neg (x : float) : float := IEEE64.negate x

/-- `Babs` with `abs_nan`, which keeps a NaN's payload: the sign bit cleared. -/
def abs (x : float) : float := IEEE64.abs x

/-- `Bcompare`: `none` when either operand is a NaN, and `+0` equals `-0`. -/
def compare (f1 f2 : float) : Option Ordering :=
  if IEEE64.isNaN f1 || IEEE64.isNaN f2 then none
  else if IEEE64.eq f1 f2 then some .eq
  else if IEEE64.lt f1 f2 then some .lt
  else some .gt

def cmp (c : comparison) (f1 f2 : float) : Bool := cmp_of_comparison c (compare f1 f2)

/-- `expand_nan_payload`. -/
def expand_nan_payload (p : Nat) : Nat := p * 2 ^ 29

/-- `reduce_nan_payload`. -/
def reduce_nan_payload (p : Nat) : Nat := quiet_nan_64_payload p / 2 ^ 29

/-- `Float.of_single`, exact for numbers; a NaN keeps its sign and its payload shifted into the
binary64 fraction, then quieted (`of_single_nan` with both architecture flags false). -/
def of_single (f : float32) : float :=
  if IEEE32.isNaN f then quiet_nan_64 (IEEE32.sign f, expand_nan_payload (IEEE32.fraction f))
  else if IEEE32.isInfinite f then IEEE64.infinity (IEEE32.sign f)
  else IEEE64.roundScaledMagnitude (IEEE32.sign f) (IEEE32.scaledMagnitude f * 2 ^ 925)

/-- `Float.to_single`, rounding to nearest, ties to even; a NaN keeps its sign and the top of its
quieted payload (`to_single_nan`). -/
def to_single (f : float) : float32 :=
  if IEEE64.isNaN f then quiet_nan_32 (IEEE64.sign f, reduce_nan_payload (IEEE64.fraction f))
  else if IEEE64.isInfinite f then IEEE32.infinity (IEEE64.sign f)
  else IEEE32.roundDyadicMagnitude (IEEE64.sign f) (IEEE64.scaledMagnitude f) 925

/-- `ZofB_range`: the value truncated toward zero, when it is finite and the truncation lies in
`[zmin, zmax]`. -/
def ZofB_range (f : float) (zmin zmax : _root_.Int) : Option _root_.Int :=
  match IEEE64.truncatedInt f with
  | some z => if zmin ≤ z ∧ z ≤ zmax then some z else none
  | none => none

def to_int (f : float) : Option int :=
  (ZofB_range f Int.min_signed Int.max_signed).map Int.repr
def to_intu (f : float) : Option int :=
  (ZofB_range f 0 Int.max_unsigned).map Int.repr
def to_long (f : float) : Option int64 :=
  (ZofB_range f Int64.min_signed Int64.max_signed).map Int64.repr
def to_longu (f : float) : Option int64 :=
  (ZofB_range f 0 Int64.max_unsigned).map Int64.repr

/-- `BofZ`: the integer rounded to nearest, ties to even. -/
def of_int (n : int) : float := IEEE64.fromInt (Int.signed n)
def of_intu (n : int) : float := IEEE64.fromInt (Int.unsigned n)
def of_long (n : int64) : float := IEEE64.fromInt (Int64.signed n)
def of_longu (n : int64) : float := IEEE64.fromInt (Int64.unsigned n)

def to_bits (f : float) : int64 := f
def of_bits (b : int64) : float := b

end Float

namespace Float32

open Wasm

def cons_pl (x : float32) (l : List (Bool × Nat)) : List (Bool × Nat) :=
  if IEEE32.isNaN x then (IEEE32.sign x, IEEE32.fraction x) :: l else l

def binop_nan (A : Archi) (x y : float32) : float32 :=
  quiet_nan_32 (A.choose_nan_32 (cons_pl x (cons_pl y [])))

def binop (A : Archi) (r x y : float32) : float32 :=
  if IEEE32.isNaN r then binop_nan A x y else r

def zero : float32 := 0

def add (A : Archi) (x y : float32) : float32 := binop A (IEEE32.add x y) x y
def sub (A : Archi) (x y : float32) : float32 := binop A (IEEE32.sub x y) x y
def mul (A : Archi) (x y : float32) : float32 := binop A (IEEE32.mul x y) x y
def div (A : Archi) (x y : float32) : float32 := binop A (IEEE32.div x y) x y

def neg (x : float32) : float32 := IEEE32.negate x
def abs (x : float32) : float32 := IEEE32.abs x

def compare (f1 f2 : float32) : Option Ordering :=
  if IEEE32.isNaN f1 || IEEE32.isNaN f2 then none
  else if IEEE32.eq f1 f2 then some .eq
  else if IEEE32.lt f1 f2 then some .lt
  else some .gt

def cmp (c : comparison) (f1 f2 : float32) : Bool := cmp_of_comparison c (compare f1 f2)

def ZofB_range (f : float32) (zmin zmax : _root_.Int) : Option _root_.Int :=
  match IEEE32.truncatedInt f with
  | some z => if zmin ≤ z ∧ z ≤ zmax then some z else none
  | none => none

def to_int (f : float32) : Option int :=
  (ZofB_range f Int.min_signed Int.max_signed).map Int.repr
def to_intu (f : float32) : Option int :=
  (ZofB_range f 0 Int.max_unsigned).map Int.repr
def to_long (f : float32) : Option int64 :=
  (ZofB_range f Int64.min_signed Int64.max_signed).map Int64.repr
def to_longu (f : float32) : Option int64 :=
  (ZofB_range f 0 Int64.max_unsigned).map Int64.repr

def of_int (n : int) : float32 := IEEE32.fromInt (Int.signed n)
def of_intu (n : int) : float32 := IEEE32.fromInt (Int.unsigned n)
def of_long (n : int64) : float32 := IEEE32.fromInt (Int64.signed n)
def of_longu (n : int64) : float32 := IEEE32.fromInt (Int64.unsigned n)

def to_bits (f : float32) : int := f
def of_bits (b : int) : float32 := b

end Float32

end LClight
