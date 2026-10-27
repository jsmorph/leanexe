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
`translate`, and `lx_pages` holds the current number of pages.  A `load64` or `store64` computes
its address in 64-bit arithmetic in the `i64` slot at the height of its address, traps when the
eight bytes do not lie below `lx_pages × 65536`, and then reads or writes one word of `lx_mem`
when the address is a multiple of 8, and eight bytes in little-endian order otherwise.
`memory.grow` succeeds when the new number of pages is at most `cap`.  The function `lx_init`
writes the module's data segments into `lx_mem`, with a word store for each aligned word that a
segment covers and a byte store for each other byte.

This version handles the integer forms of milestones M2 and M3: locals, globals, the `i64` and
`i32` operations of the subset, `block`, `loop`, `iff`, `br`, `br_if`, `ret`, `call`,
`unreachable`, `load64`, `store64`, `memory.size`, and `memory.grow`, in functions with at most
one result.  A function that uses another form, or that calls a function the translator omits,
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
the type with code `r` for `r` from 1 to 4, `brk` for `n = 0` and `r = 5`, and the result of call
site `n` for `r = 6`.  A global is `lx_status`, 1, the Wasm global `i`, `4 i + 2`, or the function
`k`, `4 k + 3`, `lx_pages`, 8, `lx_mem`, 12, or `lx_init`, 16, and the program's `main` is 4.
Every identifier is at least 1, as CompCert's identifiers, which are positive, are. -/

def localId (i : Nat) : ident := 8 * i + 8
def slotId (h : Nat) (t : VT) : ident := 8 * h + t.code
def brkId : ident := 5
def callId (k : Nat) : ident := 8 * k + 6

def statusId : ident := 1
def globalId (i : Nat) : ident := 4 * i + 2
def funId (k : Nat) : ident := 4 * k + 3
def mainId : ident := 4
def pagesId : ident := 8
def memId : ident := 12
def initId : ident := 16

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
  | _ => s!"t{id}"

/-! ## Statements -/

/-- An enclosing construct: a loop, whose branch target is its start, or a `block`, `iff`, or
function body, whose branch target is its end and which keeps `result`.  `base` is the height of
the stack at its entry, where its result goes. -/
structure Label where
  isLoop : Bool
  base : Nat
  result : Option VT
  deriving Repr, DecidableEq

/-- What the translation of a function body needs: the types of the parameters and declared
locals, the function's result, the number of globals, the parameter and result types of each
function, `none` for one the translator does not call, and the number of pages of `lx_mem`. -/
structure FCtx where
  locals : List VT
  result : Option VT
  nglobals : Nat
  sigs : List (Option (List VT × Option VT))
  cap : Nat

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
  if n < 2 ^ 31 then
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

/-- The trap of an access whose eight bytes from the address in `t` do not lie in memory. -/
def boundsCheck (r : Option VT) (t : ident) : statement :=
  .Sifthenelse (.Ebinop .Ogt (.Ebinop .Oadd (.Etempvar t tulong) (clong 8) tulong)
      (.Ebinop .Omul (.Ecast pagesVar tulong) (clong 65536) tulong) tint)
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

/-- The C function type of a callee with parameters `ps` and result `r`. -/
def funType (ps : List VT) (r : Option VT) : type :=
  .Tfunction (ps.map VT.ty) ((r.map VT.ty).getD .Tvoid) cc_default

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
            (.Ssequence (boundsCheck c.result t)
              (.Sifthenelse (aligned t) (.Sset t (wordAt c.cap t)) (.Sset t (loadBytes c.cap t 7)))),
          some (.i64 :: σ'), n)
      else none
  | .store64 off => do
      let σ' ← pops L σ 2
      if σ.take 2 = [.i64, .i32] then
        let t := slotId (h - 2) .i64
        let v := tmp (h - 1) .i64
        pure (.Ssequence (addrStmt t (tmp (h - 2) .i32) off)
            (.Ssequence (boundsCheck c.result t)
              (.Sifthenelse (aligned t) (.Sassign (wordAt c.cap t) v) (storeBytes c.cap t v 0 7))),
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
              (.Ssequence (.Sset r pagesVar) (.Sassign pagesVar (.Ecast (.Etempvar t tulong) tuint)))
              (.Sset r (.Econst_int 0xFFFFFFFF tuint))),
          some (.i32 :: σ'), n)
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
      match c.result with
      | none => some (.Sreturn none, none, n)
      | some t =>
          if σ.head? = some t ∧ curBase L + 1 ≤ h then
            some (.Sreturn (some (tmp (h - 1) t)), none, n)
          else none
  | .call k => do
      let (ps, r) ← (c.sigs[k]?).join
      let σ' ← pops L σ ps.length
      if σ.take ps.length = ps.reverse then
        let callee : expr := .Evar (funId k) (funType ps r)
        let args := callArgs (h - ps.length) ps
        match r with
        | none => pure (.Ssequence (.Scall none callee args) (statusCheck c.result), some σ', n)
        | some t =>
            pure (.Ssequence
                (.Ssequence (.Scall (some (callId n)) callee args)
                  (.Sset (slotId (h - ps.length) t) (.Etempvar (callId n) t.ty)))
                (statusCheck c.result),
              some (t :: σ'), n + 1)
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

/-- `Ssequence` of the statements in order. -/
def seqList : List statement → statement
  | [] => .Sskip
  | [s] => s
  | s :: rest => .Ssequence s (seqList rest)

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

/-- The declared temporaries of a body: the stack slots in increasing order, then `brk`, then
the call results in decreasing order of call site, the order in which `clightgen` lists the
temporaries that it creates. -/
def bodyTemps (s : statement) : List (ident × type) :=
  let all := (assigned s).foldl (fun acc x => insertSorted x acc) []
  let slots := all.filter fun (id, _) => 1 ≤ id % 8 ∧ id % 8 ≤ 4
  let calls := all.filter fun (id, _) => id % 8 = 6
  slots ++ [(brkId, tuint)] ++ calls.reverse

/-- The `return` at the end of a function with result `r`, of the result's slot. -/
def retStmt : Option VT → statement
  | some t => .Sreturn (some (tmp 0 t))
  | none => .Sreturn none

/-- The C function of a Talos function, with `lx_mem` of `cap` pages. -/
def trFunction (cap : Nat) (sigs : List (Option (List VT × Option VT))) (nglobals : Nat)
    (f : Function) : Option function := do
  let ps ← f.params.mapM VT.ofValueType
  let ls ← f.locals.mapM VT.ofValueType
  let rs ← f.results.mapM VT.ofValueType
  let r ← match rs with
    | [] => some none
    | [t] => some (some t)
    | _ => none
  let c : FCtx := { locals := ps ++ ls, result := r, nglobals := nglobals, sigs := sigs, cap := cap }
  let funLabel : Label := { isLoop := false, base := 0, result := r }
  let (body, _) ← trProg c [funLabel] [] r.toList 0 f.body
  let inits := ls.zipIdx.map fun (t, j) => statement.Sset (localId (ps.length + j)) t.zero
  let fbody := seqList (inits ++ [.Sset brkId (cint 0), wrapLoop body, retStmt r])
  pure { fn_return := (r.map VT.ty).getD .Tvoid
         fn_callconv := cc_default
         fn_params := ps.zipIdx.map fun (t, i) => (localId i, t.ty)
         fn_vars := []
         fn_temps := ls.zipIdx.map (fun (t, j) => (localId (ps.length + j), t.ty)) ++
           bodyTemps body
         fn_body := fbody }

/-- The parameter and result types of a function with at most one result. -/
def signatureOf (f : Function) : Option (List VT × Option VT) := do
  let ps ← f.params.mapM VT.ofValueType
  let rs ← f.results.mapM VT.ofValueType
  match rs with
  | [] => some (ps, none)
  | [t] => some (ps, some t)
  | _ => none

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

/-- The translated program, the names of its globals and functions, and the indices of the
functions it contains. -/
structure Translation where
  cprogram : program function
  names : List (ident × String)
  funcs : List Nat

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
  | some f => (callees f.fn_body).map (· / 4)
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
  let defs := (statusId, globdef.Gvar statusVar) ::
    (gdefs.zipIdx.map fun (g, i) => (globalId i, globdef.Gvar g)) ++
    [(pagesId, globdef.Gvar (pagesDef decl.pagesMin.toNat)), (memId, globdef.Gvar (memDef cap))] ++
    funs ++ [(initId, globdef.Gfun (.Internal (initFunction cap decl.data)))]
  let names := (statusId, "lx_status") ::
    ((List.range m.globals.length).map fun i => (globalId i, s!"lx_g{i}")) ++
    [(pagesId, "lx_pages"), (memId, "lx_mem")] ++
    included.map (fun k => (funId k, functionName m k)) ++ [(initId, "lx_init")]
  pure { cprogram := { prog_defs := defs, prog_public := defs.map (·.1), prog_main := mainId }
         names := names
         funcs := included }

end LeanExe.Native
