module

public import LeanExe.Dialect.RepeatWhile
public import LeanExe.Dialect.Build
public import LeanExe.Dialect.Bytes

@[expose] public section

/-! The state of the executable interpreter in the verified compiler's dialect: value words, the
slots of the arena, and the machine record, with the helpers that read and allocate slots.

A value is a 64-bit word whose low three bits are its tag.  A fixnum `n` is the word of `8 n`, so
the profile's 61-bit range is the range of the remaining bits.  A reference to slot `i` is
`8 i + 1`.  The constants `#f`, `#t`, `()`, the unspecified value, and the private markers of an
undefined or unbound location have tag 2, a character has tag 3 and its ASCII code above the tag,
a standard procedure has tag 4 and its code, and a temporary of a rewrite rule, which only the
expander's scopes hold, has tag 5.

The arena is an array of slots of five words: a kind word and four fields.  The kind word holds
the object's kind in its low byte, the mutability flag in bit 8, a subkind or a keyword code in
bits 16 to 23, and a small count in bits 32 to 63.  The kinds and the fields that hold references
are these.

| Kind | Fields | Reference fields |
|---|---|---|
| pair | car, cdr | a, b |
| symbol | spelling (a string), top-level value, next interned symbol | a, b, c |
| string | length, first chunk | b |
| vector | length, first chunk | b |
| chunk | next chunk, three payload words: values of a vector, or bytes of a string, eight to a word | a; b, c, d for a vector's chunk |
| bignum | reserved: no field is fixed, and the fixnum profile creates none | |
| cell | value, next cell of the environment | a, b |
| closure | lambda node, environment | a, b |
| escape | frame chain | a |
| code | by subkind, as `Demos.Scheme.Machine.Code` lists | by subkind |
| frame | next frame, then three fields by subkind | a and by subkind |

Slot 0 is no object, and the reference to it ends chains.  The machine allocates slots from `top`
upward and reports the outcome *out of space* when `top` reaches `cap`. -/

namespace Demos.Scheme.Machine

/-- A slot of the arena. -/
structure Slot where
  kind : UInt64
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64
  deriving Inhabited

/-- The machine.  `heap` is the arena of `cap` slots, `out` the output buffer of `outCap` bytes
with `outLen` written, `mode` the phase, `status` the outcome once it is decided, with `detail` its
irritant, `pos` the reader's offset, `x`, `env`, `val`, `args`, `nargs`, and `k` the registers of
the reader, the expander, and the evaluator, `forms` the program's remaining data, `syms` the list
of interned symbols, `aux` a further register, and `runMode` the export's mode: 0 to read and
write the data, 1 to expand and write the code, 2 to evaluate. -/
structure Machine where
  heap : Array Slot
  out : Array UInt64
  top : UInt64
  cap : UInt64
  outLen : UInt64
  outCap : UInt64
  mode : UInt64
  status : UInt64
  detail : UInt64
  pos : UInt64
  x : UInt64
  env : UInt64
  val : UInt64
  args : UInt64
  nargs : UInt64
  k : UInt64
  forms : UInt64
  syms : UInt64
  aux : UInt64
  runMode : UInt64
  deriving Inhabited

/-! ## Tags and constants -/

@[inline] def tagOf (v : UInt64) : UInt64 := v &&& 7
@[inline] def isRef (v : UInt64) : Bool := v &&& 7 == 1
@[inline] def isFix (v : UInt64) : Bool := v &&& 7 == 0
@[inline] def isChar (v : UInt64) : Bool := v &&& 7 == 3
@[inline] def isPrim (v : UInt64) : Bool := v &&& 7 == 4
@[inline] def refIdx (v : UInt64) : UInt64 := v >>> 3
@[inline] def mkRef (i : UInt64) : UInt64 := (i <<< 3) ||| 1
@[inline] def mkChar (c : UInt64) : UInt64 := (c <<< 3) ||| 3
@[inline] def charCode (v : UInt64) : UInt64 := v >>> 3
@[inline] def mkPrim (p : UInt64) : UInt64 := (p <<< 3) ||| 4
@[inline] def primCode (v : UInt64) : UInt64 := v >>> 3
@[inline] def mkTemp (n : UInt64) : UInt64 := (n <<< 3) ||| 5
@[inline] def mkFix (n : Int64) : UInt64 := (n <<< 3).toUInt64
@[inline] def fixVal (v : UInt64) : Int64 := v.toInt64 >>> 3

/-- The reference that ends a chain: slot 0. -/
def NONE : UInt64 := 1
def FALSE : UInt64 := 2
def TRUE : UInt64 := 10
def NILV : UInt64 := 18
def UNSPEC : UInt64 := 26
def UNDEF : UInt64 := 34
def UNBOUND : UInt64 := 42

@[inline] def boolV (b : Bool) : UInt64 := if b then TRUE else FALSE

/-! ## Kinds -/

def K_PAIR : UInt64 := 1
def K_SYMBOL : UInt64 := 2
def K_STRING : UInt64 := 3
def K_VECTOR : UInt64 := 4
def K_CHUNK : UInt64 := 5
def K_BIGNUM : UInt64 := 6
def K_CELL : UInt64 := 7
def K_CLOSURE : UInt64 := 8
def K_ESCAPE : UInt64 := 9
def K_CODE : UInt64 := 10
def K_FRAME : UInt64 := 11

/-- The mutability flag of a kind word. -/
def MUTABLE : UInt64 := 256

@[inline] def kindByte (w : UInt64) : UInt64 := w &&& 255
@[inline] def subOf (w : UInt64) : UInt64 := (w >>> 16) &&& 255
@[inline] def countOf (w : UInt64) : UInt64 := w >>> 32
@[inline] def mkKind (kind sub count : UInt64) : UInt64 := kind ||| (sub <<< 16) ||| (count <<< 32)

/-! ## Reading the arena -/

@[inline] def slotAt (heap : Array Slot) (v : UInt64) : Slot := heap[(v >>> 3).toNat]!

@[inline] def kindAt (heap : Array Slot) (v : UInt64) : UInt64 :=
  if isRef v then kindByte (slotAt heap v).kind else 0

@[inline] def isKind (heap : Array Slot) (v k : UInt64) : Bool := kindAt heap v == k

@[inline] def fa (heap : Array Slot) (v : UInt64) : UInt64 := (slotAt heap v).a
@[inline] def fb (heap : Array Slot) (v : UInt64) : UInt64 := (slotAt heap v).b
@[inline] def fc (heap : Array Slot) (v : UInt64) : UInt64 := (slotAt heap v).c
@[inline] def fd (heap : Array Slot) (v : UInt64) : UInt64 := (slotAt heap v).d
@[inline] def subAt (heap : Array Slot) (v : UInt64) : UInt64 := subOf (slotAt heap v).kind

@[inline] def isPair (heap : Array Slot) (v : UInt64) : Bool := isKind heap v K_PAIR

@[inline] def isMutable (heap : Array Slot) (v : UInt64) : Bool :=
  (slotAt heap v).kind &&& MUTABLE != 0

/-! ## Outcomes -/

/-- The phases.  `READ` reads the program, `TOP` starts the next top-level form, `EXPAND` and
`EXPANDED` expand a datum and return its code, `EVAL`, `APPLY`, and `RETURN` evaluate, `PRINT`
writes the value, `PRINTK` continues with the printer's frames, `LINE` writes a line feed
between the data or the forms of the modes 0 and 1, and `DONE` ends the run. -/
def READ : UInt64 := 0
def TOP : UInt64 := 1
def EXPAND : UInt64 := 2
def EXPANDED : UInt64 := 3
def EVAL : UInt64 := 4
def APPLY : UInt64 := 5
def RETURN : UInt64 := 6
def PRINT : UInt64 := 7
def DONE : UInt64 := 8
def PRINTK : UInt64 := 9
def LINE : UInt64 := 10

/-- The classes of an outcome, which are the status bytes of the profile, times 256, plus the
kind within the class. -/
def S_READ : UInt64 := 256
def S_SYNTAX : UInt64 := 512
def S_ERROR : UInt64 := 768
def S_RESTRICTION : UInt64 := 1024
def S_SPACE : UInt64 := 1280
def S_OUTPUT : UInt64 := 1792

/-- The machine with the outcome `status` and its irritant, unless an earlier outcome stands. -/
def fail (m : Machine) (status detail : UInt64) : Machine :=
  if m.status == 0 then { m with status := status, detail := detail, mode := DONE } else m

/-- A fresh slot holding `s`, whose reference becomes `val`, or the outcome *out of space*. -/
def alloc (m : Machine) (kind a b c d : UInt64) : Machine :=
  if m.top < m.cap then
    let s : Slot := ⟨kind, a, b, c, d⟩
    { m with heap := m.heap.set! m.top.toNat s, val := mkRef m.top, top := m.top + 1 }
  else fail m S_SPACE 0

/-- A new frame of subkind `sub` with the fields `b`, `c`, and `d` above the frame chain `k`. -/
def pushFrame (m : Machine) (sub b c d : UInt64) : Machine :=
  let m := alloc m (mkKind K_FRAME sub 0) m.k b c d
  { m with k := m.val }

/-- The machine with field `a` of the object `v` replaced. -/
def setA (m : Machine) (v w : UInt64) : Machine :=
  let s := slotAt m.heap v
  let s' : Slot := ⟨s.kind, w, s.b, s.c, s.d⟩
  { m with heap := m.heap.set! (v >>> 3).toNat s' }

def setB (m : Machine) (v w : UInt64) : Machine :=
  let s := slotAt m.heap v
  let s' : Slot := ⟨s.kind, s.a, w, s.c, s.d⟩
  { m with heap := m.heap.set! (v >>> 3).toNat s' }

def setC (m : Machine) (v w : UInt64) : Machine :=
  let s := slotAt m.heap v
  let s' : Slot := ⟨s.kind, s.a, s.b, w, s.d⟩
  { m with heap := m.heap.set! (v >>> 3).toNat s' }

def setD (m : Machine) (v w : UInt64) : Machine :=
  let s := slotAt m.heap v
  let s' : Slot := ⟨s.kind, s.a, s.b, s.c, w⟩
  { m with heap := m.heap.set! (v >>> 3).toNat s' }

end Demos.Scheme.Machine
