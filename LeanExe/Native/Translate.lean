import LeanExe.Native.Subset
import LeanExe.Native.Clight.Clight

/-!
The translator from a Talos module to a Clight program, in the form that `clightgen` produces
from the printed C text: function parameters and locals are temporaries, a call stores its
result in a temporary of its own and then copies it, and a `for (;;)` loop is
`Sloop (Ssequence Sskip body) Sskip`.

A function's locals and operand-stack slots are temporaries, named by a static analysis of the
stack's types: local `i` is `l<i>`, and the slot at height `h` of type `t` is `s<h>_<t>`.  Every
`block`, `loop`, and `iff`, and the function body, is a loop that its body leaves with `break`,
and a branch to an enclosing construct `n ≥ 1` levels out sets `brk` to `n` and breaks; the code
after each construct decrements `brk` and continues the branch.  A trap stores its code in
`lx_status` and returns, and the code after each call returns at once when `lx_status` is not 0.
The Wasm globals are the C globals `lx_g<i>`.

The linear memory is the array `lx_mem` of `cap` pages, where `cap` is a parameter of
`translate`, and `lx_pages` holds the current number of pages.  Each function keeps
`lx_pages × 65536` in the temporary `lim`, which it sets at entry and again after each call of a
function of the module and after each `memory.grow` that succeeds, the only statements that
change `lx_pages`.  A `load64` or `store64` computes its address in 64-bit arithmetic in the
`i64` slot at the height of its address, traps when the eight bytes do not lie below `lim`, and
then reads or writes one word of `lx_mem`
when the address is a multiple of 8, and eight bytes in little-endian order otherwise.  A
`load8U` or `store8` computes its address and traps in the same way for its one byte, which it
reads or writes as an `unsigned char` of `lx_mem`: `load8U` converts the byte to
`unsigned int`, and `store8` stores `(unsigned char) v`, the low byte of its `i32` value.
`memory.grow` succeeds when the new number of pages is at most `cap`.  The function `lx_init`
writes the module's data segments into `lx_mem`, with a word store for each aligned word that a
segment covers and a byte store for each other byte.

This version handles the forms of milestones M2 to M6 and the byte forms: locals, globals, the
`i64` and `i32` operations of the subset, `block`, `loop`, `iff`, `br`, `br_if`, `ret`, `call`,
`unreachable`, `load64`, `store64`, `load8U`, `store8`, `memory.size`, `memory.grow`, and the
binary64 and binary32 forms, in functions with one result or several, which return several
results in the globals `lx_r<i>_<t>`.  An operation
that rounds replaces a NaN result by Talos's canonical NaN, and a value changes type through the
cell `lx_pun`.  A function that uses another form, or that calls a function the translator omits,
is omitted, and `translate` returns the program of the remaining functions.  A function of the
program is `lxf_<name>` when the module exports it under a name that is a C identifier, and
`lxf_<k>` for its index `k` otherwise.
-/

namespace LeanExe.Native

open Wasm LClight

/-- The four numeric value types. -/
inductive VT where
  | i32 | i64 | f32 | f64
  deriving DecidableEq, Repr, Inhabited

namespace VT

def ofValueType : ValueType → Option VT
  | .i32 => some .i32
  | .i64 => some .i64
  | .f32 => some .f32
  | .f64 => some .f64
  | _ => none

/-- The C type: `unsigned int`, `unsigned long long`, `float`, or `double`. -/
def ty : VT → type
  | .i32 => .Tint .I32 .Unsigned noattr
  | .i64 => .Tlong .Unsigned noattr
  | .f32 => .Tfloat .F32 noattr
  | .f64 => .Tfloat .F64 noattr

def code : VT → Nat
  | .i32 => 1
  | .i64 => 2
  | .f32 => 3
  | .f64 => 4

def letter : VT → String
  | .i32 => "i"
  | .i64 => "l"
  | .f32 => "f"
  | .f64 => "d"

/-- The constant 0 of the type, the initial value of a declared local. -/
def zero : VT → expr
  | .i32 => .Econst_int 0 (ty .i32)
  | .i64 => .Econst_long 0 (ty .i64)
  | .f32 => .Econst_single 0 (ty .f32)
  | .f64 => .Econst_float 0 (ty .f64)

end VT

def tuint : type := VT.ty .i32
def tulong : type := VT.ty .i64
def tint : type := .Tint .I32 .Signed noattr
def tuchar : type := .Tint .I8 .Unsigned noattr

/-! ## Identifiers

A temporary is `8 n + r`: local `n - 1` for `r = 0` and `n ≥ 1`, the stack slot at height `n` of
the type with code `r` for `r` from 1 to 4, `brk` for `n = 0` and `r = 5`, the result of call
site `n` for `r = 6`, and `lim` for `n = 0` and `r = 7`.  A global is `lx_status`, 1, the Wasm
global `i`, `4 i + 2`, or the function `k`, `4 k + 3`, `lx_pages`, 8, `lx_mem`, 12, `lx_init`,
16, `lx_pun`, 20, the built-in `__builtin_fsqrt`, 24, or the result global of position `i` and
type code `r`, `32 (i + 1) + 4 r`, and the program's `main` is 4.
Every identifier is at least 1, as CompCert's identifiers, which are positive, are. -/

def localId (i : Nat) : ident := 8 * i + 8
def slotId (h : Nat) (t : VT) : ident := 8 * h + t.code
def brkId : ident := 5
def callId (k : Nat) : ident := 8 * k + 6
def limId : ident := 7

def statusId : ident := 1
def globalId (i : Nat) : ident := 4 * i + 2
def funId (k : Nat) : ident := 4 * k + 3
def mainId : ident := 4
def pagesId : ident := 8
def memId : ident := 12
def initId : ident := 16
def punId : ident := 20
def sqrtId : ident := 24

/-- The C name of a temporary. -/
def tempName (id : ident) : String :=
  let n := id / 8
  match id % 8 with
  | 0 => s!"l{n - 1}"
  | 1 => s!"s{n}_i"
  | 2 => s!"s{n}_l"
  | 3 => s!"s{n}_f"
  | 4 => s!"s{n}_d"
  | 5 => "brk"
  | 6 => s!"c{n}"
  | 7 => if n = 0 then "lim" else s!"t{id}"
  | _ => s!"t{id}"

/-! ## Statements -/

/-- An enclosing construct: a loop, whose branch target is its start, or a `block`, `iff`, or
function body, whose branch target is its end and which keeps `result`.  `base` is the height of
the stack at its entry, where its result goes.  A branch may not target a `final` construct: the
body of a function with several results, which a branch would have to leave with all of
them. -/
structure Label where
  isLoop : Bool
  base : Nat
  result : Option VT
  final : Bool := false
  deriving Repr, DecidableEq

/-- The C result of a function whose results have the types `rs`: the one result, if there is
exactly one. -/
def retOf : List VT → Option VT
  | [t] => some t
  | _ => none

/-- What the translation of a function body needs: the types of the parameters and declared
locals, the function's results, the number of globals, the parameter and result types of each
function, `none` for one the translator does not call, and the number of pages of `lx_mem`. -/
structure FCtx where
  locals : List VT
  results : List VT
  nglobals : Nat
  sigs : List (Option (List VT × List VT))
  cap : Nat

/-- The C result of the function. -/
def FCtx.result (c : FCtx) : Option VT := retOf c.results

def tmp (h : Nat) (t : VT) : expr := .Etempvar (slotId h t) t.ty

def cint (n : Nat) : expr := .Econst_int (UInt32.ofNat n) tuint

/-- `return` with the constant 0 of the result type, after a trap. -/
def retZero : Option VT → statement
  | some t => .Sreturn (some t.zero)
  | none => .Sreturn none

/-- The trap codes in `lx_status`. -/
def trapUnreachable : Nat := 1
def trapOutOfBounds : Nat := 2
def trapDivZero : Nat := 3

/-- The code of a Talos trap message. -/
def trapCode (msg : String) : Nat :=
  if msg = "unreachable" then trapUnreachable
  else if msg = "out of bounds memory access" then trapOutOfBounds
  else if msg = "integer divide by zero" then trapDivZero
  else 0

def trapStmt (code : Nat) (r : Option VT) : statement :=
  .Ssequence (.Sassign (.Evar statusId tuint) (cint code)) (retZero r)

/-- After a call: return at once when the callee trapped. -/
def statusCheck (r : Option VT) : statement :=
  .Sifthenelse (.Ebinop .One (.Evar statusId tuint) (cint 0) tint) (retZero r) .Sskip

/-- The C jump that ends a branch to a construct from its own body. -/
def jump (isLoop : Bool) : statement := if isLoop then .Scontinue else .Sbreak

/-- The code after a construct inside the body of `parent`: a branch that left the construct
with `brk ≥ 1` goes on to `parent` when `brk - 1 = 0`, and further out otherwise. -/
def dispatch (parent : Label) : statement :=
  .Sifthenelse (.Ebinop .One (.Etempvar brkId tuint) (cint 0) tint)
    (.Ssequence (.Sset brkId (.Ebinop .Osub (.Etempvar brkId tuint) (cint 1) tuint))
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar brkId tuint) (cint 0) tint)
        (jump parent.isLoop) .Sbreak))
    .Sskip

/-- `Ssequence a b`, or `b` when `a` is `Sskip`, as `clightgen` leaves it. -/
def seq (a b : statement) : statement :=
  match a with
  | .Sskip => b
  | _ => .Ssequence a b

/-- `for (;;) { body; break; }`. -/
def wrapLoop (body : statement) : statement :=
  .Sloop (.Ssequence .Sskip (seq body .Sbreak)) .Sskip

/-- The height below which the current body may not pop. -/
def curBase (L : List Label) : Nat :=
  match L with
  | l :: _ => l.base
  | [] => 0

/-- `σ` without its top `n` types, when they lie above the current base. -/
def pops (L : List Label) (σ : List VT) (n : Nat) : Option (List VT) :=
  if curBase L + n ≤ σ.length then some (σ.drop n) else none

/-- A branch `n` levels out from the stack `σ`: copy the kept value to the target's result slot,
then `break` or `continue` for `n = 0`, or set `brk` to `n` and `break`. -/
def brStmt (L : List Label) (σ : List VT) (n : Nat) : Option statement := do
  let target ← L[n]?
  if n < 2 ^ 31 ∧ target.final = false then
    let copy ← match target.isLoop, target.result with
      | false, some t =>
          match σ with
          | t' :: _ =>
              if t' = t ∧ curBase L + 1 ≤ σ.length then
                some (.Sset (slotId target.base t) (tmp (σ.length - 1) t))
              else none
          | [] => none
      | _, _ => some .Sskip
    let go := if n = 0 then jump target.isLoop else .Ssequence (.Sset brkId (cint n)) .Sbreak
    pure (seq copy go)
  else none

/-! ## Memory -/

def clong (n : Nat) : expr := .Econst_long (UInt64.ofNat n) tulong

/-- The type of `lx_mem`, an array of `8192 cap` words. -/
def memType (cap : Nat) : type := .Tarray tulong (8192 * cap : Nat) noattr

def memVar (cap : Nat) : expr := .Evar memId (memType cap)

def pagesVar : expr := .Evar pagesId tuint

/-- `(unsigned long long) lx_pages * 65536`, the number of bytes of memory. -/
def limExpr : expr := .Ebinop .Omul (.Ecast pagesVar tulong) (clong 65536) tulong

/-- `lim = (unsigned long long) lx_pages * 65536`. -/
def limSet : statement := .Sset limId limExpr

/-- After a call of a function of the module: return at once when the callee trapped, and
otherwise set `lim` again, since the callee may have grown the memory. -/
def callCheck (r : Option VT) : statement := .Ssequence (statusCheck r) limSet

/-- The address in the temporary `t` plus `k`: `t + k`, or `t` for `k = 0`. -/
def addrPlus (t : ident) (k : Nat) : expr :=
  if k = 0 then .Etempvar t tulong else .Ebinop .Oadd (.Etempvar t tulong) (clong k) tulong

/-- The word of `lx_mem` at the byte address in `t`, a multiple of 8: `lx_mem[t >> 3]`. -/
def wordAt (cap : Nat) (t : ident) : expr :=
  .Ederef (.Ebinop .Oadd (memVar cap) (.Ebinop .Oshr (.Etempvar t tulong) (clong 3) tulong)
    (.Tpointer tulong noattr)) tulong

/-- The byte of `lx_mem` at the address `a`: `((unsigned char *) lx_mem)[a]`. -/
def byteAt (cap : Nat) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Ecast (memVar cap) (.Tpointer tuchar noattr)) a
    (.Tpointer tuchar noattr)) tuchar

/-- Bytes 0 to `k` from the address in `t`, combined little-endian as `Mem.read64` combines
them. -/
def loadBytes (cap : Nat) (t : ident) : Nat → expr
  | 0 => .Ecast (byteAt cap (addrPlus t 0)) tulong
  | k + 1 => .Ebinop .Oor (loadBytes cap t k)
      (.Ebinop .Oshl (.Ecast (byteAt cap (addrPlus t (k + 1))) tulong) (clong (8 * (k + 1)))
        tulong) tulong

/-- Byte `k` of the value `v`: `(unsigned char) (v >> 8 k)`. -/
def byteOfVal (v : expr) (k : Nat) : expr :=
  .Ecast (if k = 0 then v else .Ebinop .Oshr v (clong (8 * k)) tulong) tuchar

/-- The stores of bytes `k` to `k + n` of `v` from the address in `t`, in increasing order. -/
def storeBytes (cap : Nat) (t : ident) (v : expr) : Nat → Nat → statement
  | k, 0 => .Sassign (byteAt cap (addrPlus t k)) (byteOfVal v k)
  | k, n + 1 => .Ssequence (.Sassign (byteAt cap (addrPlus t k)) (byteOfVal v k))
      (storeBytes cap t v (k + 1) n)

/-- `t = (unsigned long long) a + off`: the address of an access, without wrapping. -/
def addrStmt (t : ident) (a : expr) (off : UInt32) : statement :=
  .Sset t (.Ebinop .Oadd (.Ecast a tulong) (.Econst_long off.toUInt64 tulong) tulong)

/-- The trap of an access whose `w` bytes from the address in `t` do not lie below `lim`. -/
def boundsCheck (w : Nat) (r : Option VT) (t : ident) : statement :=
  .Sifthenelse (.Ebinop .Ogt (.Ebinop .Oadd (.Etempvar t tulong) (clong w) tulong)
      (.Etempvar limId tulong) tint)
    (trapStmt trapOutOfBounds r) .Sskip

/-- The address in `t` is a multiple of 8. -/
def aligned (t : ident) : expr :=
  .Ebinop .Oeq (.Ebinop .Oand (.Etempvar t tulong) (clong 7) tulong) (clong 0) tint

/-- The binary `i64` operations other than division and shifts. -/
def i64Op : Instruction → Option binary_operation
  | .addI64 => some .Oadd
  | .subI64 => some .Osub
  | .mulI64 => some .Omul
  | .andI64 => some .Oand
  | .orI64 => some .Oor
  | .xorI64 => some .Oxor
  | _ => none

/-- The `i64` comparisons. -/
def i64Cmp : Instruction → Option binary_operation
  | .eqI64 => some .Oeq
  | .neI64 => some .One
  | .ltUI64 => some .Olt
  | .leUI64 => some .Ole
  | .geUI64 => some .Oge
  | _ => none

/-- The C function type of a callee with parameters `ps` and results `rs`. -/
def funType (ps : List VT) (rs : List VT) : type :=
  .Tfunction (ps.map VT.ty) (((retOf rs).map VT.ty).getD .Tvoid) cc_default

/-! ## Several results

A function with several results returns `void` and leaves result `i`, of type `t`, in the global
`lx_r<i>_<t>`, which the caller copies into its stack slot.  The translator declares the
globals of `unsigned int`, `unsigned long long`, `double`, and `float` for each position up to
the most results of a function. -/

/-- `lx_r<i>_<t>`. -/
def resId (i : Nat) (t : VT) : ident := 32 * (i + 1) + 4 * t.code

def resVar (i : Nat) (t : VT) : expr := .Evar (resId i t) t.ty

/-- The types of the result globals: all four. -/
def VT.isRes : VT → Bool
  | _ => true

/-- The types of the result globals of a position, in the order of the program's definitions. -/
def resTypes : List VT := [.i32, .i64, .f64, .f32]

/-- `Ssequence` of the statements in order. -/
def seqList : List statement → statement
  | [] => .Sskip
  | [s] => s
  | s :: rest => .Ssequence s (seqList rest)

/-- The stores of the slots from height `h` up, of the types `rs`, to the result globals from
position `i` up. -/
def resStores : List VT → Nat → Nat → List statement
  | [], _, _ => []
  | t :: rs, i, h => .Sassign (resVar i t) (tmp h t) :: resStores rs (i + 1) (h + 1)

/-- The copies of the result globals of the types `rs` from position `i` up to the slots from
height `h` up. -/
def resLoads : List VT → Nat → Nat → List statement
  | [], _, _ => []
  | t :: rs, i, h => .Sset (slotId h t) (resVar i t) :: resLoads rs (i + 1) (h + 1)

/-- `lx_pun`, an array of one `unsigned long long`, the cell through which a value changes
type. -/
def punType : type := .Tarray tulong 1 noattr

def punDef : globvar type :=
  { gvar_info := punType, gvar_init := [.Init_space 8], gvar_readonly := false
    gvar_volatile := false }

def tdouble : type := VT.ty .f64

/-- The signature of `__builtin_fsqrt`, as CompCert's table of built-ins gives it. -/
def sqrtSig : signature := { sig_args := [.Xfloat], sig_res := .Xfloat, sig_cc := cc_default }

/-- The declaration of `__builtin_fsqrt`, an external built-in function, as `clightgen` writes
it. -/
def sqrtFun : fundef function :=
  .External (.EF_builtin "__builtin_fsqrt" sqrtSig) [tdouble] tdouble cc_default

def sqrtDef : globdef (fundef function) type := .Gfun sqrtFun

/-! ## Binary64

A binary64 operation that Talos rounds computes its C result, and a NaN result becomes Talos's
positive canonical quiet NaN, which C cannot write as a literal: `if (t != t)` stores its bits
in `lx_pun` as a word and loads them back as a double.  A value changes type through `lx_pun`
as well, and so does a constant that is a NaN or an infinity; a finite constant is an exact
literal, negated when it is negative, as `clightgen` reads a negative literal. -/

/-- `*(ty *) lx_pun`. -/
def punAt (ty : type) : expr := .Ederef (.Ecast (.Evar punId punType) (.Tpointer ty noattr)) ty

/-- The double in `lx_pun` after a store of the word `w`. -/
def punStore (w : expr) (h : Nat) : statement :=
  .Ssequence (.Sassign (punAt tulong) w) (.Sset (slotId h .f64) (punAt tdouble))

/-- `if (t != t) t = <the canonical NaN>;` for the double slot at height `h`. -/
def canonStmt (h : Nat) : statement :=
  .Sifthenelse (.Ebinop .One (tmp h .f64) (tmp h .f64) tint)
    (punStore (.Econst_long IEEE64.canonicalNaN tulong) h) .Sskip

/-- The binary64 operations that round. -/
def f64Op : Instruction → Option binary_operation
  | .f64Add => some .Oadd
  | .f64Sub => some .Osub
  | .f64Mul => some .Omul
  | .f64Div => some .Odiv
  | _ => none

/-- The binary64 comparisons. -/
def f64Cmp : Instruction → Option binary_operation
  | .f64Eq => some .Oeq
  | .f64Lt => some .Olt
  | .f64Le => some .Ole
  | _ => none

/-- The binary64 constant `v` in the slot at height `h`. -/
def f64ConstStmt (h : Nat) (v : UInt64) : statement :=
  if IEEE64.isFinite v then
    if IEEE64.sign v then
      .Sset (slotId h .f64) (.Eunop .Oneg (.Econst_float (IEEE64.negate v) tdouble) tdouble)
    else .Sset (slotId h .f64) (.Econst_float v tdouble)
  else punStore (.Econst_long v tulong) h

def sqrtVar : expr := .Evar sqrtId (.Tfunction [tdouble] tdouble cc_default)

/-- -1.0. -/
def minusOne : expr := .Eunop .Oneg (.Econst_float 0x3FF0000000000000 tdouble) tdouble

/-- 2^64. -/
def twoTo64 : expr := .Econst_float 0x43F0000000000000 tdouble

/-- `i64.trunc_sat_f64_u` of the double slot at height `h` into the word slot: 0 for a NaN and
below -1, the largest word at 2^64 and above, and the C conversion between. -/
def truncSatStmt (h : Nat) : statement :=
  .Sifthenelse (.Ebinop .One (tmp h .f64) (tmp h .f64) tint) (.Sset (slotId h .i64) (clong 0))
    (.Sifthenelse (.Ebinop .Ole (tmp h .f64) minusOne tint) (.Sset (slotId h .i64) (clong 0))
      (.Sifthenelse (.Ebinop .Oge (tmp h .f64) twoTo64 tint)
        (.Sset (slotId h .i64) (.Econst_long 0xFFFFFFFFFFFFFFFF tulong))
        (.Sset (slotId h .i64) (.Ecast (tmp h .f64) tulong))))

/-! ## Binary32

The binary32 forms follow the binary64 ones, with the first four bytes of `lx_pun` as the cell:
a NaN result of a rounding operation becomes Talos's canonical NaN, and a value changes type
through the cell.  `abs` clears the sign bit of the word, since `__builtin_fabs` of a `float`
converts it to `double` first, which quiets a signaling NaN.  `sqrt` takes the square root of the
`double` conversion and converts the result back, which rounds twice but gives the correctly
rounded result, and `nearest` computes the integer from the word with shifts and masks. -/

def tfloat : type := VT.ty .f32

/-- The float in `lx_pun` after a store of the word `w`, into the float slot at height `h`. -/
def punStore32 (w : expr) (h : Nat) : statement :=
  .Ssequence (.Sassign (punAt tuint) w) (.Sset (slotId h .f32) (punAt tfloat))

/-- The word of the float slot at height `h`, through `lx_pun`, into the word slot at height
`k`. -/
def punBits32 (h k : Nat) : statement :=
  .Ssequence (.Sassign (punAt tfloat) (tmp h .f32)) (.Sset (slotId k .i32) (punAt tuint))

/-- `if (t != t) t = <the canonical NaN>;` for the float slot at height `h`. -/
def canonStmt32 (h : Nat) : statement :=
  .Sifthenelse (.Ebinop .One (tmp h .f32) (tmp h .f32) tint)
    (punStore32 (.Econst_int IEEE32.canonicalNaN tuint) h) .Sskip

/-- The binary32 operations that round. -/
def f32Op : Instruction → Option binary_operation
  | .f32Add => some .Oadd
  | .f32Sub => some .Osub
  | .f32Mul => some .Omul
  | .f32Div => some .Odiv
  | _ => none

/-- The binary32 comparisons. -/
def f32Cmp : Instruction → Option binary_operation
  | .f32Eq => some .Oeq
  | .f32Lt => some .Olt
  | .f32Le => some .Ole
  | _ => none

/-- The binary32 constant `v` in the slot at height `h`. -/
def f32ConstStmt (h : Nat) (v : UInt32) : statement :=
  if IEEE32.isFinite v then
    if IEEE32.sign v then
      .Sset (slotId h .f32) (.Eunop .Oneg (.Econst_single (IEEE32.negate v) tfloat) tfloat)
    else .Sset (slotId h .f32) (.Econst_single v tfloat)
  else punStore32 (.Econst_int v tuint) h

/-- `abs` of the float slot at height `h`: its word with the sign bit cleared. -/
def abs32Stmt (h : Nat) : statement :=
  .Ssequence (punBits32 h h)
    (punStore32 (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFFFF) tuint) h)

/-- `sqrt` of the float slot at height `h`: the square root of its `double` conversion, which
the call `n` takes, converted back. -/
def sqrt32Stmt (h n : Nat) : statement :=
  .Ssequence
    (.Ssequence (.Scall (some (callId n)) sqrtVar [.Ecast (tmp h .f32) tdouble])
      (.Sset (slotId h .f32) (.Ecast (.Etempvar (callId n) tdouble) tfloat)))
    (canonStmt32 h)

/-- `nearest` of the float slot at height `h`.  The word `u` goes to the word slot at height
`h` and its biased exponent `e` to the one above.  For `e ≥ 150` the value is integral, infinite,
or a NaN, and stays; for `e < 126` its magnitude is below one half, and the result is a zero of
its sign.  Otherwise, with the significand `m` and `s = 150 - e`, the quotient `q = m >> s` rises
by one when the remainder `m & ((1 << s) - 1)` exceeds the half `1 << (s - 1)`, or equals it and
`q` is odd, and the result is `(float) q`, negated when the sign bit is set.  The slots at
heights `h + 2` to `h + 5` hold `s`, `q`, the remainder, and the half. -/
def nearest32Stmt (h : Nat) : statement :=
  let w (k : Nat) : expr := tmp k .i32
  let set (k : Nat) (e : expr) : statement := .Sset (slotId k .i32) e
  let mant : expr := .Ebinop .Oadd (.Ebinop .Oand (w h) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint
  let negative : expr := .Ebinop .Oshr (w h) (cint 31) tuint
  seqList [
    punBits32 h h,
    set (h + 1) (.Ebinop .Oand (.Ebinop .Oshr (w h) (cint 23) tuint) (cint 255) tuint),
    .Sifthenelse (.Ebinop .Oge (w (h + 1)) (cint 150) tint) .Sskip
      (.Sifthenelse (.Ebinop .Olt (w (h + 1)) (cint 126) tint)
        (.Sifthenelse negative
          (.Sset (slotId h .f32) (.Eunop .Oneg (.Econst_single 0 tfloat) tfloat))
          (.Sset (slotId h .f32) (.Econst_single 0 tfloat)))
        (seqList [
          set (h + 2) (.Ebinop .Osub (cint 150) (w (h + 1)) tuint),
          set (h + 3) (.Ebinop .Oshr mant (w (h + 2)) tuint),
          set (h + 4) (.Ebinop .Oand mant
            (.Ebinop .Osub (.Ebinop .Oshl (cint 1) (w (h + 2)) tuint) (cint 1) tuint) tuint),
          set (h + 5) (.Ebinop .Oshl (cint 1) (.Ebinop .Osub (w (h + 2)) (cint 1) tuint) tuint),
          .Sifthenelse (.Ebinop .Ogt (w (h + 4)) (w (h + 5)) tint)
            (set (h + 3) (.Ebinop .Oadd (w (h + 3)) (cint 1) tuint))
            (.Sifthenelse (.Ebinop .Oeq (w (h + 4)) (w (h + 5)) tint)
              (.Sifthenelse (.Ebinop .Oand (w (h + 3)) (cint 1) tuint)
                (set (h + 3) (.Ebinop .Oadd (w (h + 3)) (cint 1) tuint)) .Sskip)
              .Sskip),
          .Sset (slotId h .f32) (.Ecast (w (h + 3)) tfloat),
          .Sifthenelse negative
            (.Sset (slotId h .f32) (.Eunop .Oneg (tmp h .f32) tfloat)) .Sskip])),
    canonStmt32 h]

/-- -1.0f, 2^31, -2^31, and 2^64 as `float`s. -/
def minusOne32 : expr := .Eunop .Oneg (.Econst_single 0x3F800000 tfloat) tfloat
def two31f : expr := .Econst_single 0x4F000000 tfloat
def minusTwo31f : expr := .Eunop .Oneg two31f tfloat
def two64f : expr := .Econst_single 0x5F800000 tfloat

/-- `i64.trunc_sat_f32_u` of the float slot at height `h` into the word slot of `i64`: 0 for a
NaN and below -1, the largest word at 2^64 and above, and the C conversion between. -/
def truncSat32UStmt (h : Nat) : statement :=
  .Sifthenelse (.Ebinop .One (tmp h .f32) (tmp h .f32) tint) (.Sset (slotId h .i64) (clong 0))
    (.Sifthenelse (.Ebinop .Ole (tmp h .f32) minusOne32 tint) (.Sset (slotId h .i64) (clong 0))
      (.Sifthenelse (.Ebinop .Oge (tmp h .f32) two64f tint)
        (.Sset (slotId h .i64) (.Econst_long 0xFFFFFFFFFFFFFFFF tulong))
        (.Sset (slotId h .i64) (.Ecast (tmp h .f32) tulong))))

/-- `i32.trunc_sat_f32_s` of the float slot at height `h` into the word slot of `i32`: 0 for a
NaN, `0x80000000` at -2^31 and below, `0x7FFFFFFF` at 2^31 and above, and the C conversion to
`int` between. -/
def truncSat32SStmt (h : Nat) : statement :=
  .Sifthenelse (.Ebinop .One (tmp h .f32) (tmp h .f32) tint) (.Sset (slotId h .i32) (cint 0))
    (.Sifthenelse (.Ebinop .Ole (tmp h .f32) minusTwo31f tint)
      (.Sset (slotId h .i32) (cint 0x80000000))
      (.Sifthenelse (.Ebinop .Oge (tmp h .f32) two31f tint)
        (.Sset (slotId h .i32) (cint 0x7FFFFFFF))
        (.Sset (slotId h .i32) (.Ecast (.Ecast (tmp h .f32) tint) tuint))))

/-- The arguments of a call with parameters `ps`: the slots from height `base` up, deepest
first. -/
def callArgs (base : Nat) : List VT → List expr
  | [] => []
  | t :: ts => tmp base t :: callArgs (base + 1) ts

mutual

/-- The statement of `inst` from the stack `σ` with `n` call sites so far, the stack after it
(`none` when control does not continue past it), and the new number of call sites. -/
def trInstr (c : FCtx) (L : List Label) (σ : List VT) (n : Nat) (inst : Instruction) :
    Option (statement × Option (List VT) × Nat) :=
  let h := σ.length
  match inst with
  | .localGet i => do
      let t ← c.locals[i]?
      pure (.Sset (slotId h t) (.Etempvar (localId i) t.ty), some (t :: σ), n)
  | .localSet i => do
      let t ← c.locals[i]?
      let σ' ← pops L σ 1
      if σ.head? = some t then
        pure (.Sset (localId i) (tmp (h - 1) t), some σ', n)
      else none
  | .localTee i => do
      let t ← c.locals[i]?
      let _ ← pops L σ 1
      if σ.head? = some t then
        pure (.Sset (localId i) (tmp (h - 1) t), some σ, n)
      else none
  | .globalGet i =>
      if i < c.nglobals then
        some (.Sset (slotId h .i64) (.Evar (globalId i) tulong), some (.i64 :: σ), n)
      else none
  | .globalSet i => do
      let σ' ← pops L σ 1
      if i < c.nglobals ∧ σ.head? = some .i64 then
        pure (.Sassign (.Evar (globalId i) tulong) (tmp (h - 1) .i64), some σ', n)
      else none
  | .const k => some (.Sset (slotId h .i32) (.Econst_int k tuint), some (.i32 :: σ), n)
  | .constI64 k => some (.Sset (slotId h .i64) (.Econst_long k tulong), some (.i64 :: σ), n)
  | .addI64 | .subI64 | .mulI64 | .andI64 | .orI64 | .xorI64 => do
      let op ← i64Op inst
      let σ' ← pops L σ 2
      if σ.take 2 = [.i64, .i64] then
        pure (.Sset (slotId (h - 2) .i64) (.Ebinop op (tmp (h - 2) .i64) (tmp (h - 1) .i64) tulong),
          some (.i64 :: σ'), n)
      else none
  | .shlI64 | .shrUI64 => do
      let σ' ← pops L σ 2
      let op : binary_operation := if inst matches .shlI64 then .Oshl else .Oshr
      if σ.take 2 = [.i64, .i64] then
        pure (.Sset (slotId (h - 2) .i64)
            (.Ebinop op (tmp (h - 2) .i64)
              (.Ebinop .Oand (tmp (h - 1) .i64) (.Econst_long 63 tulong) tulong) tulong),
          some (.i64 :: σ'), n)
      else none
  | .divUI64 | .remUI64 => do
      let σ' ← pops L σ 2
      let op : binary_operation := if inst matches .divUI64 then .Odiv else .Omod
      if σ.take 2 = [.i64, .i64] then
        pure (.Ssequence
            (.Sifthenelse (.Ebinop .Oeq (tmp (h - 1) .i64) (.Econst_long 0 tulong) tint)
              (trapStmt trapDivZero c.result) .Sskip)
            (.Sset (slotId (h - 2) .i64)
              (.Ebinop op (tmp (h - 2) .i64) (tmp (h - 1) .i64) tulong)),
          some (.i64 :: σ'), n)
      else none
  | .eqI64 | .neI64 | .ltUI64 | .leUI64 | .geUI64 => do
      let op ← i64Cmp inst
      let σ' ← pops L σ 2
      if σ.take 2 = [.i64, .i64] then
        pure (.Sset (slotId (h - 2) .i32)
            (.Ecast (.Ebinop op (tmp (h - 2) .i64) (tmp (h - 1) .i64) tint) tuint),
          some (.i32 :: σ'), n)
      else none
  | .eqzI64 => do
      let σ' ← pops L σ 1
      if σ.head? = some .i64 then
        pure (.Sset (slotId (h - 1) .i32)
            (.Ecast (.Ebinop .Oeq (tmp (h - 1) .i64) (.Econst_long 0 tulong) tint) tuint),
          some (.i32 :: σ'), n)
      else none
  | .eq => do
      let σ' ← pops L σ 2
      if σ.take 2 = [.i32, .i32] then
        pure (.Sset (slotId (h - 2) .i32)
            (.Ecast (.Ebinop .Oeq (tmp (h - 2) .i32) (tmp (h - 1) .i32) tint) tuint),
          some (.i32 :: σ'), n)
      else none
  | .eqz => do
      let σ' ← pops L σ 1
      if σ.head? = some .i32 then
        pure (.Sset (slotId (h - 1) .i32)
            (.Ecast (.Ebinop .Oeq (tmp (h - 1) .i32) (cint 0) tint) tuint),
          some (.i32 :: σ'), n)
      else none
  | .and => do
      let σ' ← pops L σ 2
      if σ.take 2 = [.i32, .i32] then
        pure (.Sset (slotId (h - 2) .i32)
            (.Ebinop .Oand (tmp (h - 2) .i32) (tmp (h - 1) .i32) tuint),
          some (.i32 :: σ'), n)
      else none
  | .wrapI64 => do
      let σ' ← pops L σ 1
      if σ.head? = some .i64 then
        pure (.Sset (slotId (h - 1) .i32) (.Ecast (tmp (h - 1) .i64) tuint), some (.i32 :: σ'), n)
      else none
  | .extendUI32 => do
      let σ' ← pops L σ 1
      if σ.head? = some .i32 then
        pure (.Sset (slotId (h - 1) .i64) (.Ecast (tmp (h - 1) .i32) tulong), some (.i64 :: σ'), n)
      else none
  | .load64 off => do
      let σ' ← pops L σ 1
      if σ.head? = some .i32 then
        let t := slotId (h - 1) .i64
        pure (.Ssequence (addrStmt t (tmp (h - 1) .i32) off)
            (.Ssequence (boundsCheck 8 c.result t)
              (.Sifthenelse (aligned t) (.Sset t (wordAt c.cap t)) (.Sset t (loadBytes c.cap t 7)))),
          some (.i64 :: σ'), n)
      else none
  | .store64 off => do
      let σ' ← pops L σ 2
      if σ.take 2 = [.i64, .i32] then
        let t := slotId (h - 2) .i64
        let v := tmp (h - 1) .i64
        pure (.Ssequence (addrStmt t (tmp (h - 2) .i32) off)
            (.Ssequence (boundsCheck 8 c.result t)
              (.Sifthenelse (aligned t) (.Sassign (wordAt c.cap t) v) (storeBytes c.cap t v 0 7))),
          some σ', n)
      else none
  | .load8U off => do
      let σ' ← pops L σ 1
      if σ.head? = some .i32 then
        let t := slotId (h - 1) .i64
        pure (.Ssequence (addrStmt t (tmp (h - 1) .i32) off)
            (.Ssequence (boundsCheck 1 c.result t)
              (.Sset (slotId (h - 1) .i32) (.Ecast (byteAt c.cap (addrPlus t 0)) tuint))),
          some (.i32 :: σ'), n)
      else none
  | .store8 off => do
      let σ' ← pops L σ 2
      if σ.take 2 = [.i32, .i32] then
        let t := slotId (h - 2) .i64
        pure (.Ssequence (addrStmt t (tmp (h - 2) .i32) off)
            (.Ssequence (boundsCheck 1 c.result t)
              (.Sassign (byteAt c.cap (addrPlus t 0)) (.Ecast (tmp (h - 1) .i32) tuchar))),
          some σ', n)
      else none
  | .memorySize => some (.Sset (slotId h .i32) pagesVar, some (.i32 :: σ), n)
  | .memoryGrow => do
      let σ' ← pops L σ 1
      if σ.head? = some .i32 then
        let t := slotId (h - 1) .i64
        let r := slotId (h - 1) .i32
        pure (.Ssequence
            (.Sset t (.Ebinop .Oadd (.Ecast pagesVar tulong) (.Ecast (tmp (h - 1) .i32) tulong)
              tulong))
            (.Sifthenelse (.Ebinop .Ole (.Etempvar t tulong) (clong c.cap) tint)
              (.Ssequence (.Sset r pagesVar)
                (.Ssequence (.Sassign pagesVar (.Ecast (.Etempvar t tulong) tuint)) limSet))
              (.Sset r (.Econst_int 0xFFFFFFFF tuint))),
          some (.i32 :: σ'), n)
      else none
  | .f64Const v => some (f64ConstStmt h v, some (.f64 :: σ), n)
  | .f64Add | .f64Sub | .f64Mul | .f64Div => do
      let op ← f64Op inst
      let σ' ← pops L σ 2
      if σ.take 2 = [.f64, .f64] then
        pure (.Ssequence
            (.Sset (slotId (h - 2) .f64) (.Ebinop op (tmp (h - 2) .f64) (tmp (h - 1) .f64) tdouble))
            (canonStmt (h - 2)),
          some (.f64 :: σ'), n)
      else none
  | .f64Sqrt => do
      let σ' ← pops L σ 1
      if σ.head? = some .f64 then
        pure (.Ssequence
            (.Ssequence (.Scall (some (callId n)) sqrtVar [tmp (h - 1) .f64])
              (.Sset (slotId (h - 1) .f64) (.Etempvar (callId n) tdouble)))
            (canonStmt (h - 1)),
          some (.f64 :: σ'), n + 1)
      else none
  | .f64Eq | .f64Lt | .f64Le => do
      let op ← f64Cmp inst
      let σ' ← pops L σ 2
      if σ.take 2 = [.f64, .f64] then
        pure (.Sset (slotId (h - 2) .i32)
            (.Ecast (.Ebinop op (tmp (h - 2) .f64) (tmp (h - 1) .f64) tint) tuint),
          some (.i32 :: σ'), n)
      else none
  | .f64Abs => do
      let σ' ← pops L σ 1
      if σ.head? = some .f64 then
        pure (.Sset (slotId (h - 1) .f64) (.Eunop .Oabsfloat (tmp (h - 1) .f64) tdouble),
          some (.f64 :: σ'), n)
      else none
  | .f64ConvertI64U => do
      let σ' ← pops L σ 1
      if σ.head? = some .i64 then
        pure (.Sset (slotId (h - 1) .f64) (.Ecast (tmp (h - 1) .i64) tdouble), some (.f64 :: σ'), n)
      else none
  | .f64ReinterpretI64 => do
      let σ' ← pops L σ 1
      if σ.head? = some .i64 then
        pure (punStore (tmp (h - 1) .i64) (h - 1), some (.f64 :: σ'), n)
      else none
  | .i64ReinterpretF64 => do
      let σ' ← pops L σ 1
      if σ.head? = some .f64 then
        pure (.Ssequence (.Sassign (punAt tdouble) (tmp (h - 1) .f64))
            (.Sset (slotId (h - 1) .i64) (punAt tulong)),
          some (.i64 :: σ'), n)
      else none
  | .i64TruncSatF64U => do
      let σ' ← pops L σ 1
      if σ.head? = some .f64 then
        pure (truncSatStmt (h - 1), some (.i64 :: σ'), n)
      else none
  | .f32Const v => some (f32ConstStmt h v, some (.f32 :: σ), n)
  | .f32Add | .f32Sub | .f32Mul | .f32Div => do
      let op ← f32Op inst
      let σ' ← pops L σ 2
      if σ.take 2 = [.f32, .f32] then
        pure (.Ssequence
            (.Sset (slotId (h - 2) .f32) (.Ebinop op (tmp (h - 2) .f32) (tmp (h - 1) .f32) tfloat))
            (canonStmt32 (h - 2)),
          some (.f32 :: σ'), n)
      else none
  | .f32Sqrt => do
      let σ' ← pops L σ 1
      if σ.head? = some .f32 then pure (sqrt32Stmt (h - 1) n, some (.f32 :: σ'), n + 1)
      else none
  | .f32Nearest => do
      let σ' ← pops L σ 1
      if σ.head? = some .f32 then pure (nearest32Stmt (h - 1), some (.f32 :: σ'), n)
      else none
  | .f32Eq | .f32Lt | .f32Le => do
      let op ← f32Cmp inst
      let σ' ← pops L σ 2
      if σ.take 2 = [.f32, .f32] then
        pure (.Sset (slotId (h - 2) .i32)
            (.Ecast (.Ebinop op (tmp (h - 2) .f32) (tmp (h - 1) .f32) tint) tuint),
          some (.i32 :: σ'), n)
      else none
  | .f32Abs => do
      let σ' ← pops L σ 1
      if σ.head? = some .f32 then pure (abs32Stmt (h - 1), some (.f32 :: σ'), n)
      else none
  | .f32ConvertI64U => do
      let σ' ← pops L σ 1
      if σ.head? = some .i64 then
        pure (.Sset (slotId (h - 1) .f32) (.Ecast (tmp (h - 1) .i64) tfloat), some (.f32 :: σ'), n)
      else none
  | .f32ConvertI32S => do
      let σ' ← pops L σ 1
      if σ.head? = some .i32 then
        pure (.Sset (slotId (h - 1) .f32) (.Ecast (.Ecast (tmp (h - 1) .i32) tint) tfloat),
          some (.f32 :: σ'), n)
      else none
  | .f32ReinterpretI32 => do
      let σ' ← pops L σ 1
      if σ.head? = some .i32 then pure (punStore32 (tmp (h - 1) .i32) (h - 1), some (.f32 :: σ'), n)
      else none
  | .i32ReinterpretF32 => do
      let σ' ← pops L σ 1
      if σ.head? = some .f32 then pure (punBits32 (h - 1) (h - 1), some (.i32 :: σ'), n)
      else none
  | .i64TruncSatF32U => do
      let σ' ← pops L σ 1
      if σ.head? = some .f32 then pure (truncSat32UStmt (h - 1), some (.i64 :: σ'), n)
      else none
  | .i32TruncSatF32S => do
      let σ' ← pops L σ 1
      if σ.head? = some .f32 then pure (truncSat32SStmt (h - 1), some (.i32 :: σ'), n)
      else none
  | .unreachable => some (trapStmt trapUnreachable c.result, none, n)
  | .br k => do
      let s ← brStmt L σ k
      pure (s, none, n)
  | .br_if k => do
      let σ' ← pops L σ 1
      if σ.head? = some .i32 then
        let s ← brStmt L σ' k
        pure (.Sifthenelse (tmp (h - 1) .i32) s .Sskip, some σ', n)
      else none
  | .ret =>
      match c.results with
      | [] => some (.Sreturn none, none, n)
      | [t] =>
          if σ.head? = some t ∧ curBase L + 1 ≤ h then
            some (.Sreturn (some (tmp (h - 1) t)), none, n)
          else none
      | rs =>
          if σ.take rs.length = rs.reverse ∧ curBase L + rs.length ≤ h then
            some (seqList (resStores rs 0 (h - rs.length) ++ [.Sreturn none]), none, n)
          else none
  | .call k => do
      let (ps, rs) ← (c.sigs[k]?).join
      let σ' ← pops L σ ps.length
      if σ.take ps.length = ps.reverse then
        let callee : expr := .Evar (funId k) (funType ps rs)
        let args := callArgs (h - ps.length) ps
        match rs with
        | [] => pure (.Ssequence (.Scall none callee args) (callCheck c.result), some σ', n)
        | [t] =>
            pure (.Ssequence
                (.Ssequence (.Scall (some (callId n)) callee args)
                  (.Sset (slotId (h - ps.length) t) (.Etempvar (callId n) t.ty)))
                (callCheck c.result),
              some (t :: σ'), n + 1)
        | rs =>
            pure (.Ssequence
                (.Ssequence (.Scall none callee args) (seqList (resLoads rs 0 (h - ps.length))))
                (callCheck c.result),
              some (rs.reverse ++ σ'), n)
      else none
  | .block pa ra body pts rts => do
      if blockTypeOk pa ra pts rts then
        let r ← (rts.head?).mapM VT.ofValueType
        let parent ← L.head?
        let L' := { isLoop := false, base := h, result := r : Label } :: L
        let (s, n') ← trProg c L' σ (r.toList ++ σ) n body
        pure (.Ssequence (wrapLoop s) (dispatch parent), some (r.toList ++ σ), n')
      else none
  | .loop pa ra body pts rts => do
      if blockTypeOk pa ra pts rts then
        let r ← (rts.head?).mapM VT.ofValueType
        let parent ← L.head?
        let L' := { isLoop := true, base := h, result := none : Label } :: L
        let (s, n') ← trProg c L' σ (r.toList ++ σ) n body
        pure (.Ssequence (wrapLoop s) (dispatch parent), some (r.toList ++ σ), n')
      else none
  | .iff pa ra thn els pts rts => do
      if blockTypeOk pa ra pts rts then
        let r ← (rts.head?).mapM VT.ofValueType
        let parent ← L.head?
        let σ' ← pops L σ 1
        if σ.head? = some .i32 then
          let L' := { isLoop := false, base := h - 1, result := r : Label } :: L
          let (s1, n1) ← trProg c L' σ' (r.toList ++ σ') n thn
          let (s2, n2) ← trProg c L' σ' (r.toList ++ σ') n1 els
          pure (.Ssequence (wrapLoop (.Sifthenelse (tmp (h - 1) .i32) s1 s2)) (dispatch parent),
            some (r.toList ++ σ'), n2)
        else none
      else none
  | _ => none

/-- The statement of the body `p` from the stack `σ`, which must end with the stack `σend`
unless control does not reach the end. -/
def trProg (c : FCtx) (L : List Label) (σ σend : List VT) (n : Nat) (p : Program) :
    Option (statement × Nat) :=
  match p with
  | [] => if σ = σend then some (.Sskip, n) else none
  | inst :: rest => do
      let (s, σ', n') ← trInstr c L σ n inst
      match rest, σ' with
      | [], none => pure (s, n')
      | [], some σ'' => if σ'' = σend then pure (s, n') else none
      | _ :: _, none => none
      | _ :: _, some σ'' => do
          let (s2, n'') ← trProg c L σ'' σend n' rest
          pure (.Ssequence s s2, n'')

end

/-! ## Functions and modules -/

/-- The temporaries that `s` assigns, with their types, in order of first assignment. -/
def assigned : statement → List (ident × type)
  | .Sset id a => [(id, typeof a)]
  | .Scall (some id) (.Evar _ (.Tfunction _ r _)) _ => [(id, r)]
  | .Ssequence s1 s2 => assigned s1 ++ assigned s2
  | .Sifthenelse _ s1 s2 => assigned s1 ++ assigned s2
  | .Sloop s1 s2 => assigned s1 ++ assigned s2
  | _ => []

/-- The functions that `s` calls. -/
def callees : statement → List ident
  | .Scall _ (.Evar f _) _ => [f]
  | .Ssequence s1 s2 => callees s1 ++ callees s2
  | .Sifthenelse _ s1 s2 => callees s1 ++ callees s2
  | .Sloop s1 s2 => callees s1 ++ callees s2
  | _ => []

def insertSorted (x : ident × type) : List (ident × type) → List (ident × type)
  | [] => [x]
  | y :: ys => if x.1 < y.1 then x :: y :: ys else if x.1 = y.1 then y :: ys else y :: insertSorted x ys

/-- The declared temporaries of a body: the stack slots in increasing order, then `brk` and
`lim`, then the call results in decreasing order of call site, the order in which `clightgen`
lists the temporaries that it creates. -/
def bodyTemps (s : statement) : List (ident × type) :=
  let all := (assigned s).foldl (fun acc x => insertSorted x acc) []
  let slots := all.filter fun (id, _) => 1 ≤ id % 8 ∧ id % 8 ≤ 4
  let calls := all.filter fun (id, _) => id % 8 = 6
  slots ++ [(brkId, tuint), (limId, tulong)] ++ calls.reverse

/-- The `return` at the end of a function with results `rs`: of the result's slot for one
result, and after the stores of the slots to the result globals for several. -/
def retStmt : List VT → statement
  | [] => .Sreturn none
  | [t] => .Sreturn (some (tmp 0 t))
  | rs => seqList (resStores rs 0 0 ++ [.Sreturn none])

/-- The results that the translator handles: at most one, or several whose types have result
globals. -/
def resultsOk (rs : List VT) : Bool := rs.length ≤ 1 || rs.all VT.isRes

/-- The C function of a Talos function, with `lx_mem` of `cap` pages. -/
def trFunction (cap : Nat) (sigs : List (Option (List VT × List VT))) (nglobals : Nat)
    (f : Function) : Option function := do
  let ps ← f.params.mapM VT.ofValueType
  let ls ← f.locals.mapM VT.ofValueType
  let rs ← f.results.mapM VT.ofValueType
  guard (resultsOk rs)
  let c : FCtx := { locals := ps ++ ls, results := rs, nglobals := nglobals, sigs := sigs, cap := cap }
  let funLabel : Label := { isLoop := false, base := 0, result := retOf rs, final := 2 ≤ rs.length }
  let (body, _) ← trProg c [funLabel] [] rs.reverse 0 f.body
  let inits := ls.zipIdx.map fun (t, j) => statement.Sset (localId (ps.length + j)) t.zero
  let fbody := seqList (inits ++ [.Sset brkId (cint 0), limSet, wrapLoop body, retStmt rs])
  pure { fn_return := ((retOf rs).map VT.ty).getD .Tvoid
         fn_callconv := cc_default
         fn_params := ps.zipIdx.map fun (t, i) => (localId i, t.ty)
         fn_vars := []
         fn_temps := ls.zipIdx.map (fun (t, j) => (localId (ps.length + j), t.ty)) ++
           bodyTemps body
         fn_body := fbody }

/-- The parameter and result types of a function whose results the translator handles. -/
def signatureOf (f : Function) : Option (List VT × List VT) := do
  let ps ← f.params.mapM VT.ofValueType
  let rs ← f.results.mapM VT.ofValueType
  if resultsOk rs then some (ps, rs) else none

/-- The indices `k` in `candidates` whose callees all lie in the result, by removing a function
whose callee is missing until none is: at most one pass per function. -/
def closeUnderCalls (calls : Nat → List Nat) : Nat → List Nat → List Nat
  | 0, ks => ks
  | fuel + 1, ks =>
      let ks' := ks.filter fun k => (calls k).all (ks.contains ·)
      if ks'.length = ks.length then ks else closeUnderCalls calls fuel ks'

def isIdentStart (ch : Char) : Bool := ch.isAlpha || ch == '_'
def isIdentChar (ch : Char) : Bool := ch.isAlphanum || ch == '_'

/-- The C name of function `k`. -/
def functionName (m : Module) (k : Nat) : String :=
  match m.exports.find? (·.funcIdx == k) with
  | some e =>
      match e.name.toList with
      | ch :: rest =>
          if isIdentStart ch && rest.all isIdentChar then s!"lxf_{e.name}" else s!"lxf_{k}"
      | [] => s!"lxf_{k}"
  | none => s!"lxf_{k}"

/-- The translated program, the names of its globals and functions, the indices of the functions
it contains, and the number of positions of its result globals. -/
structure Translation where
  cprogram : program function
  names : List (ident × String)
  funcs : List Nat
  nres : Nat

/-- The global `lx_g<i>` of a Talos global, whose initial value is an `i64`. -/
def globalDef (g : GlobalDecl) : Option (globvar type) :=
  match g.init with
  | .i64 n =>
      some { gvar_info := tulong, gvar_init := [.Init_int64 n], gvar_readonly := false
             gvar_volatile := false }
  | _ => none

/-- The C function of each function of `m`, `none` for one the translator does not handle. -/
def fdefsOf (cap : Nat) (m : Module) : List (Option function) :=
  m.funcs.map (trFunction cap (m.funcs.map signatureOf) m.globals.length)

/-- The functions that the C function of `k` calls. -/
def callsOf (cap : Nat) (m : Module) (k : Nat) : List Nat :=
  match (fdefsOf cap m)[k]?.join with
  | some f => (callees f.fn_body).filterMap fun id => if id % 4 = 3 then some (id / 4) else none
  | none => []

/-- The functions that the program contains: those that translate and call only such
functions. -/
def includedOf (cap : Nat) (m : Module) : List Nat :=
  closeUnderCalls (callsOf cap m) (m.funcs.length + 1)
    ((List.range m.funcs.length).filter fun k => ((fdefsOf cap m)[k]?.join).isSome)

/-- The definition of function `k` in the program. -/
def funDef (cap : Nat) (m : Module) (k : Nat) : Option (ident × globdef (fundef function) type) := do
  let f ← (fdefsOf cap m)[k]?.join
  pure (funId k, .Gfun (.Internal f))

/-- `lx_status`, initially 0. -/
def statusVar : globvar type :=
  { gvar_info := tuint, gvar_init := [.Init_int32 0], gvar_readonly := false
    gvar_volatile := false }

/-- `lx_pages`, initially `pages`. -/
def pagesDef (pages : Nat) : globvar type :=
  { gvar_info := tuint, gvar_init := [.Init_int32 (UInt32.ofNat pages)], gvar_readonly := false
    gvar_volatile := false }

/-- `lx_mem`, of `cap` pages, initially zero. -/
def memDef (cap : Nat) : globvar type :=
  { gvar_info := memType cap, gvar_init := [.Init_space (65536 * cap : Nat)], gvar_readonly := false
    gvar_volatile := false }

/-- The value of eight bytes read little-endian, as `decode_val` reads them. -/
def wordOfBytes (bs : List UInt8) : UInt64 := Int64.repr (int_of_bytes bs)

/-- The store of the word of the bytes `bs` at the address `a`, a multiple of 8. -/
def wordStore (cap : Nat) (a : Nat) (bs : List UInt8) : statement :=
  .Sassign (.Ederef (.Ebinop .Oadd (memVar cap) (clong (a / 8)) (.Tpointer tulong noattr)) tulong)
    (.Econst_long (wordOfBytes bs) tulong)

/-- The store of the byte `b` at the address `a`. -/
def byteStore (cap : Nat) (a : Nat) (b : UInt8) : statement :=
  .Sassign (byteAt cap (clong a)) (.Ecast (.Econst_int b.toUInt32 tuint) tuchar)

/-- The stores that write the bytes `bs` from the address `a`: a word store where `a` is a
multiple of 8 and eight bytes remain, and a byte store otherwise. -/
def initStores (cap : Nat) : Nat → List UInt8 → List statement
  | a, b0 :: rest@(b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest') =>
      if a % 8 = 0 then
        wordStore cap a [b0, b1, b2, b3, b4, b5, b6, b7] :: initStores cap (a + 8) rest'
      else byteStore cap a b0 :: initStores cap (a + 1) rest
  | a, b0 :: rest => byteStore cap a b0 :: initStores cap (a + 1) rest
  | _, [] => []

/-- The stores of a data segment, which the subset check requires to be active at a literal
offset. -/
def segmentStores (cap : Nat) (seg : DataSegment) : List statement :=
  match seg.offset with
  | some off => initStores cap off.toNat seg.bytes
  | none => []

/-- `lx_init`, which writes the data segments into `lx_mem` in order. -/
def initFunction (cap : Nat) (segs : List DataSegment) : function :=
  { fn_return := .Tvoid, fn_callconv := cc_default, fn_params := [], fn_vars := [], fn_temps := []
    fn_body := seqList (segs.flatMap (segmentStores cap)) }

/-- A result global of the type `t`: an integer one initially 0, a `double` one without an
initializer. -/
def resDef (t : VT) : globvar type :=
  { gvar_info := t.ty
    gvar_init := [match t with
      | .i32 => .Init_int32 0
      | .i64 => .Init_int64 0
      | .f64 => .Init_space 8
      | .f32 => .Init_space 4]
    gvar_readonly := false
    gvar_volatile := false }

/-- The result globals of the positions below `nres`, of the types `resTypes` for each. -/
def resDefs (nres : Nat) : List (ident × globdef (fundef function) type) :=
  (List.range nres).flatMap fun i => resTypes.map fun t => (resId i t, .Gvar (resDef t))

def resNames (nres : Nat) : List (ident × String) :=
  (List.range nres).flatMap fun i => resTypes.map fun t => (resId i t, s!"lx_r{i}_{t.letter}")



/-- `acc`, raised to the results of function `k` when it has several. -/
def maxStep (m : Module) (acc k : Nat) : Nat :=
  match m.funcs[k]? with
  | some f => if 2 ≤ f.results.length then max acc f.results.length else acc
  | none => acc

/-- The most results of a function among `ks` with several. -/
def maxResults (m : Module) (ks : List Nat) : Nat := ks.foldl (maxStep m) 0

/-- The pages of `lx_mem` in the translations that `verified_compile` adds: 4,096 pages, or
256 MiB. -/
def nativeCap : Nat := 4096

/-- The translation of `m` with `lx_mem` of `cap` pages.  The module's initial pages must not
exceed `cap`, and `cap` must not exceed 65,535, the most pages that the compiled modules
declare. -/
def translate (cap : Nat) (m : Module) : Option Translation := do
  guard (violation m = none)
  let decl ← m.memory
  guard (decl.pagesMin.toNat ≤ cap ∧ cap ≤ 65535)
  let gdefs ← m.globals.mapM globalDef
  let included := includedOf cap m
  guard (included.all fun k => (callsOf cap m k).all (included.contains ·))
  let funs ← included.mapM (funDef cap m)
  let nres := maxResults m included
  let defs := (statusId, globdef.Gvar statusVar) ::
    (gdefs.zipIdx.map fun (g, i) => (globalId i, globdef.Gvar g)) ++
    [(pagesId, globdef.Gvar (pagesDef decl.pagesMin.toNat)), (memId, globdef.Gvar (memDef cap)),
      (punId, globdef.Gvar punDef), (sqrtId, sqrtDef)] ++
    resDefs nres ++ funs ++ [(initId, globdef.Gfun (.Internal (initFunction cap decl.data)))]
  let names := (statusId, "lx_status") ::
    ((List.range m.globals.length).map fun i => (globalId i, s!"lx_g{i}")) ++
    [(pagesId, "lx_pages"), (memId, "lx_mem"), (punId, "lx_pun"), (sqrtId, "__builtin_fsqrt")] ++
    resNames nres ++
    included.map (fun k => (funId k, functionName m k)) ++ [(initId, "lx_init")]
  pure { cprogram := { prog_defs := defs, prog_public := defs.map (·.1), prog_main := mainId }
         names := names
         funcs := included
         nres := nres }

end LeanExe.Native
