/-!
The machine integers of CompCert 3.18's `lib/Integers.v`: `Int` (32 bits), `Int64`, `Ptrofs`
(64 bits on both targets), and `Byte`.  A value is a Lean fixed-width word, and each operation is
defined as `Integers.v` defines it, through `unsigned`, `signed`, and `repr` on Lean's `Int`,
which plays the part of Coq's `Z`: `Z.quot` and `Z.rem` are `Int.tdiv` and `Int.tmod`, and `Z.div`
and `Z.modulo` with a positive divisor are `/` and `%`.  The shifts state the result for an
amount of at least the word size outright, which agrees with `Z.shiftl` and `Z.shiftr` followed
by `repr` and avoids computing a power of two that large.  Only the operations that the
semantics in this directory use are copied.
-/

namespace LClight

/-- `Int.int`. -/
abbrev int := UInt32
/-- `Int64.int`. -/
abbrev int64 := UInt64
/-- `Ptrofs.int`; `Archi.ptr64` is true on x86-64 and AArch64. -/
abbrev ptrofs := UInt64
/-- `Byte.int`. -/
abbrev byte := UInt8

/-- `comparison` of `lib/Integers.v`. -/
inductive comparison where
  | Ceq | Cne | Clt | Cle | Cgt | Cge
  deriving Repr, DecidableEq

namespace Int

def modulus : _root_.Int := 2 ^ 32
def max_unsigned : _root_.Int := modulus - 1
def half_modulus : _root_.Int := modulus / 2
def max_signed : _root_.Int := half_modulus - 1
def min_signed : _root_.Int := -half_modulus

def unsigned (n : int) : _root_.Int := n.toNat

def signed (n : int) : _root_.Int :=
  if unsigned n < half_modulus then unsigned n else unsigned n - modulus

def repr (x : _root_.Int) : int := UInt32.ofNat (x % modulus).toNat

def zero : int := repr 0
def one : int := repr 1
def mone : int := repr (-1)
def iwordsize : int := repr 32

def eq (x y : int) : Bool := decide (unsigned x = unsigned y)
def lt (x y : int) : Bool := decide (signed x < signed y)
def ltu (x y : int) : Bool := decide (unsigned x < unsigned y)

def neg (x : int) : int := repr (- unsigned x)
def add (x y : int) : int := repr (unsigned x + unsigned y)
def sub (x y : int) : int := repr (unsigned x - unsigned y)
def mul (x y : int) : int := repr (unsigned x * unsigned y)
def divs (x y : int) : int := repr ((signed x).tdiv (signed y))
def mods (x y : int) : int := repr ((signed x).tmod (signed y))
def divu (x y : int) : int := repr (unsigned x / unsigned y)
def modu (x y : int) : int := repr (unsigned x % unsigned y)

def and (x y : int) : int := UInt32.ofNat ((unsigned x).toNat &&& (unsigned y).toNat)
def or (x y : int) : int := UInt32.ofNat ((unsigned x).toNat ||| (unsigned y).toNat)
def xor (x y : int) : int := UInt32.ofNat ((unsigned x).toNat ^^^ (unsigned y).toNat)
def not (x : int) : int := xor x mone

def shl (x y : int) : int :=
  if unsigned y < 32 then repr (unsigned x * 2 ^ (unsigned y).toNat) else zero
def shru (x y : int) : int :=
  if unsigned y < 32 then repr (unsigned x / 2 ^ (unsigned y).toNat) else zero
def shr (x y : int) : int :=
  if unsigned y < 32 then repr (signed x / 2 ^ (unsigned y).toNat)
  else if signed x < 0 then mone else zero

/-- `Zzero_ext n x` is `x mod 2^n` for `n > 0` and `0` otherwise. -/
def zero_ext (n : _root_.Int) (x : int) : int :=
  repr (if n ≤ 0 then 0 else unsigned x % 2 ^ n.toNat)

/-- `Zsign_ext n x` is the low `n` bits of `x` read in two's complement for `n > 0`, and `0`
otherwise. -/
def sign_ext (n : _root_.Int) (x : int) : int :=
  repr (if n ≤ 0 then 0
    else
      let y := unsigned x % 2 ^ n.toNat
      if 2 ^ (n.toNat - 1) ≤ y then y - 2 ^ n.toNat else y)

def cmp (c : comparison) (x y : int) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !eq x y
  | .Clt => lt x y
  | .Cle => !lt y x
  | .Cgt => lt y x
  | .Cge => !lt x y

def cmpu (c : comparison) (x y : int) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !eq x y
  | .Clt => ltu x y
  | .Cle => !ltu y x
  | .Cgt => ltu y x
  | .Cge => !ltu x y

end Int

namespace Int64

def modulus : _root_.Int := 2 ^ 64
def max_unsigned : _root_.Int := modulus - 1
def half_modulus : _root_.Int := modulus / 2
def max_signed : _root_.Int := half_modulus - 1
def min_signed : _root_.Int := -half_modulus

def unsigned (n : int64) : _root_.Int := n.toNat

def signed (n : int64) : _root_.Int :=
  if unsigned n < half_modulus then unsigned n else unsigned n - modulus

def repr (x : _root_.Int) : int64 := UInt64.ofNat (x % modulus).toNat

def zero : int64 := repr 0
def one : int64 := repr 1
def mone : int64 := repr (-1)
def iwordsize : int64 := repr 64
/-- `Int64.iwordsize'`, the word size as a 32-bit integer. -/
def iwordsize' : int := Int.repr 64

def eq (x y : int64) : Bool := decide (unsigned x = unsigned y)
def lt (x y : int64) : Bool := decide (signed x < signed y)
def ltu (x y : int64) : Bool := decide (unsigned x < unsigned y)

def neg (x : int64) : int64 := repr (- unsigned x)
def add (x y : int64) : int64 := repr (unsigned x + unsigned y)
def sub (x y : int64) : int64 := repr (unsigned x - unsigned y)
def mul (x y : int64) : int64 := repr (unsigned x * unsigned y)
def divs (x y : int64) : int64 := repr ((signed x).tdiv (signed y))
def mods (x y : int64) : int64 := repr ((signed x).tmod (signed y))
def divu (x y : int64) : int64 := repr (unsigned x / unsigned y)
def modu (x y : int64) : int64 := repr (unsigned x % unsigned y)

def and (x y : int64) : int64 := UInt64.ofNat ((unsigned x).toNat &&& (unsigned y).toNat)
def or (x y : int64) : int64 := UInt64.ofNat ((unsigned x).toNat ||| (unsigned y).toNat)
def xor (x y : int64) : int64 := UInt64.ofNat ((unsigned x).toNat ^^^ (unsigned y).toNat)
def not (x : int64) : int64 := xor x mone

def shl (x y : int64) : int64 :=
  if unsigned y < 64 then repr (unsigned x * 2 ^ (unsigned y).toNat) else zero
def shru (x y : int64) : int64 :=
  if unsigned y < 64 then repr (unsigned x / 2 ^ (unsigned y).toNat) else zero
def shr (x y : int64) : int64 :=
  if unsigned y < 64 then repr (signed x / 2 ^ (unsigned y).toNat)
  else if signed x < 0 then mone else zero

/-- The low 32 bits. -/
def loword (n : int64) : int := Int.repr (unsigned n)

def cmp (c : comparison) (x y : int64) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !eq x y
  | .Clt => lt x y
  | .Cle => !lt y x
  | .Cgt => lt y x
  | .Cge => !lt x y

def cmpu (c : comparison) (x y : int64) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !eq x y
  | .Clt => ltu x y
  | .Cle => !ltu y x
  | .Cgt => ltu y x
  | .Cge => !ltu x y

end Int64

namespace Ptrofs

def modulus : _root_.Int := 2 ^ 64
def max_unsigned : _root_.Int := modulus - 1
def half_modulus : _root_.Int := modulus / 2
def max_signed : _root_.Int := half_modulus - 1

def unsigned (n : ptrofs) : _root_.Int := n.toNat

def signed (n : ptrofs) : _root_.Int :=
  if unsigned n < half_modulus then unsigned n else unsigned n - modulus

def repr (x : _root_.Int) : ptrofs := UInt64.ofNat (x % modulus).toNat

def zero : ptrofs := repr 0

def add (x y : ptrofs) : ptrofs := repr (unsigned x + unsigned y)
def sub (x y : ptrofs) : ptrofs := repr (unsigned x - unsigned y)
def mul (x y : ptrofs) : ptrofs := repr (unsigned x * unsigned y)
def divs (x y : ptrofs) : ptrofs := repr ((signed x).tdiv (signed y))

def to_int64 (x : ptrofs) : int64 := Int64.repr (unsigned x)
def of_int64 (x : int64) : ptrofs := repr (Int64.unsigned x)
def of_intu (x : int) : ptrofs := repr (Int.unsigned x)
def of_ints (x : int) : ptrofs := repr (Int.signed x)

end Ptrofs

namespace Byte

def modulus : _root_.Int := 2 ^ 8
def unsigned (n : byte) : _root_.Int := n.toNat
def repr (x : _root_.Int) : byte := UInt8.ofNat (x % modulus).toNat

end Byte

end LClight
