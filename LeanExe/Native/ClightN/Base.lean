import LeanExe.Native.Clight.Bigstep

/-!
The Lean meaning of the symbols of the neutral specification `clightn/N.nsx`, the twin of
`clightn/rocq/NBase.v`.  The base symbols are word and pointer-offset conversions, which the Lean
copy's `unsigned`, `repr`, and `signed` give, Euclid's division by a positive divisor, powers of
two, bitwise operations on numbers that are not negative, the concatenation of traces, and the
conversions between floating-point numbers and their bits; the laws that `Laws.lean` proves fix
their meaning where the specification uses them.  The interpreted symbols
name the definitions of the Lean copy of Clight under test, at `Archi.aarch64`, and take a `Unit`
in place of CompCert's composite environment, which the copy's programs leave empty.
-/

namespace ClightN.Base

def u32 (x : UInt32) : Int := LClight.Int.unsigned x
def r32 (z : Int) : UInt32 := LClight.Int.repr z
def u64 (x : UInt64) : Int := LClight.Int64.unsigned x
def r64 (z : Int) : UInt64 := LClight.Int64.repr z
def s64 (x : UInt64) : Int := LClight.Int64.signed x
def zdiv (a b : Int) : Int := a / b
def zmod (a b : Int) : Int := a % b
def pow2 (k : Int) : Int := 2 ^ k.toNat
def land (a b : Int) : Int := (a.toNat &&& b.toNat : Nat)
def lor (a b : Int) : Int := (a.toNat ||| b.toNat : Nat)
def lxor (a b : Int) : Int := (a.toNat ^^^ b.toNat : Nat)
def uptr (x : LClight.ptrofs) : Int := LClight.Ptrofs.unsigned x
def rptr (z : Int) : LClight.ptrofs := LClight.Ptrofs.repr LClight.Archi.aarch64 z
def app (t1 t2 : List LClight.event) : List LClight.event := t1 ++ t2
def f64_of_bits (x : UInt64) : LClight.float := LClight.Float.of_bits x
def f64_bits (f : LClight.float) : UInt64 := LClight.Float.to_bits f
def f32_of_bits (x : UInt32) : LClight.float32 := LClight.Float32.of_bits x
def f32_bits (f : LClight.float32) : UInt32 := LClight.Float32.to_bits f

abbrev sem_binop (_ : Unit) : LClight.binary_operation → LClight.val → LClight.type →
    LClight.val → LClight.type → LClight.mem → Option LClight.val :=
  LClight.sem_binary_operation LClight.Archi.aarch64
abbrev sem_cast : LClight.val → LClight.type → LClight.type → LClight.mem → Option LClight.val :=
  LClight.sem_cast LClight.Archi.aarch64
abbrev bool_val : LClight.val → LClight.type → LClight.mem → Option Bool :=
  LClight.bool_val LClight.Archi.aarch64
abbrev eval_expr : LClight.genv → LClight.env → LClight.temp_env → LClight.mem → LClight.expr →
    LClight.val → Prop :=
  LClight.eval_expr LClight.Archi.aarch64

end ClightN.Base
