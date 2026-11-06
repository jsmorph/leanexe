import Lean
import LeanExe.A64.Machine

/-!
The traces that Isla computes from the Sail model of the Arm architecture, as a relation between
states of the model of `LeanExe/A64/Machine.lean`.  The syntax covers the part of Isla's trace
language (the grammar `isla_lang.ott` of the repository isla-lang) that the traces of `tests/isla`
and of the Isla probes use: the header `(segments ...)` that names the symbolic fields of an
opcode, atoms, register values that are atoms, structs of atoms, or vectors of atoms, the SMT-LIB
expressions of `define-const`, `assert`, and `assume`, the events, and trees of `cases`.  A bit
vector is a width `w` and a natural number below `2 ^ w`, and every operator is arithmetic on
natural numbers modulo a power of 2, as SMT-LIB defines it.

`isla_trace% "PATH"` reads the footprint, the header and the trace, in the file at PATH, relative
to the directory in which Lean runs, when the term elaborates.  The reader `parse` is trusted: a
theorem about the term holds of the file only as far as `parse` reads the file correctly.  It folds
the operators of many arguments to the left, drops the access kind of a memory read and the kind
and the result of a memory write, which the semantics does not use, reads a name of the header in
an expression as the field's variable, reads a vector primitive only over the references `R0` to
`R30` in order, and reads the events `cycle`, `call`, `return`, `define-enum`, and `branch-address`
as `skip`.

`Trace.Run P t ρ s σ o` follows the operational semantics of Islaris (Sammler et al., PLDI 2022,
section 3, and `theories/opsem.v` of its repository): `declare-const` picks any value of its type,
a read of a register or of memory whose value differs from the state's ends the path without an
outcome, as does a false `assert`, while a false `assume` or `assume-reg` and every ill-formed
event end it in `fail`, `cases` takes any branch, a write to memory stores its bytes least
significant first, and `branch-address` and the result of a write have no effect.  The model's
`State` holds the registers `R0` to `R30`, `SP_EL1`, `_PC`, and the fields `N`, `Z`, `C`, and `V`
of `PSTATE`, the bytes of memory, and the UART's output.  `σ` holds every other register by name,
and `PSTATE`'s other fields in a struct.  The outcome of a path that ends holds the model's state
and `σ`, so that a theorem can state an instruction's whole effect.  An `ite` evaluates both
branches, which differs from Islaris only where a branch cannot be evaluated.

The rules below read Isla or the Sail model instead of Islaris, which binds no field, steps over
an `abstract-primop` without effect (`opsem.v` 427-429), and leaves the program counter to the
trace.  Citations of Isla give lines of its tree at e9b5d945, and those of `armv9p4.ir` lines of
the IR of isla-snapshots d8b31014.

1. `Footprint.Run` binds the variable of each field of the header to the field's value, and
   `declare-const` of a bound variable checks its width and range instead of choosing a value.
   Isla declares one variable per field and prints the header (`isla/src/footprint.rs` 100-135).
2. `read_register_from_vector` lists the values of `R0` to `R30`, which must be the state's, as
   for `read-reg`, and its result must be register `i` for `i` below 31 and `R0` for 31, where
   `i` is the index modulo 32.  Isla truncates the index to 5 bits (`isla-lib/src/executor.rs`
   175-184) and builds the chain `ite (= i j) Rj ...` over `R30` to `R1` on the base `R0`
   (244-264).
3. `write_register_from_vector` lists the values of `R0` to `R30`, which must be the state's, and
   sets register `i` for `i` below 31 and no register for 31.  Isla assigns `ite (= i j) v Rj` to
   each `Rj` and records no `write-reg` (`executor.rs` 329-351).
4. `__BranchTaken` is false before the trace, and at the end of a path `_PC` advances by 4 while
   `__BranchTaken` is false, as in `__InstructionExecute` (`armv9p4.ir` 3768698 and
   3768806-3768831, Sail lines 299 and 333-334), which the entry point `isla_footprint_no_init`
   does not run.  The other effects of `__InstructionExecute` after the instruction, on
   `InGuardedPage`, `PSTATE.BTYPE`, and the IT and single-step state, concern registers outside
   the model, and the rule leaves them out.
5. A write of one byte at `P.uart` appends the byte to the output instead of writing memory, as
   the model's `Platform.uart` states.
6. A write of a whole register outside the model sets it even when `σ` holds no value for it,
   where Islaris requires one (`opsem.v` 497-503), since `σ` holds the registers of a
   configuration that the theorems leave open.
7. The reader takes `(|f| nil)` in an expression, where `f` names a field of the header, as the
   field's variable.  Isla records a constraint on the fields as an `assume` over their names
   (`isla/src/footprint.rs` 136-146).
-/

namespace LeanExe.A64.Isla

/-- An atom of a trace: the variable `v<x>`, a bit vector of width `w` and value `n`, a Boolean,
or a member of an enumeration. -/
inductive Base where
  | var (x : Nat)
  | bits (w n : Nat)
  | bool (b : Bool)
  | enum (name : String)
  deriving Lean.ToExpr

/-- The value of a register event: an atom, a struct of atoms, or a vector of atoms. -/
inductive RVal where
  | base (b : Base)
  | struct (fields : List (String × Base))
  | vec (elems : List Base)
  deriving Lean.ToExpr

/-- An operator of one argument: `not`, `bvnot`, `(_ extract hi lo)`, `(_ zero_extend k)`, and
`(_ sign_extend k)`. -/
inductive Unop where
  | not
  | bvnot
  | extract (hi lo : Nat)
  | zeroExtend (k : Nat)
  | signExtend (k : Nat)
  deriving Lean.ToExpr

/-- An operator of two arguments: `=`, `and`, `or`, `concat`, and the operators on bit vectors
of SMT-LIB's theory of fixed-size bit vectors that the traces use. -/
inductive Binop where
  | eq
  | and
  | or
  | concat
  | bvadd
  | bvsub
  | bvmul
  | bvand
  | bvor
  | bvshl
  | bvlshr
  | bvashr
  | bvsdiv
  | bvsrem
  | bvule
  | bvuge
  | bvslt
  | bvsle
  | bvsgt
  | bvsge
  deriving Lean.ToExpr

/-- An SMT-LIB expression, where `reg r al` is the value of register `r` at the accessor path
`al`, which only an `assume` uses. -/
inductive Exp where
  | base (b : Base)
  | reg (r : String) (al : List String)
  | un (o : Unop) (e : Exp)
  | bin (o : Binop) (a b : Exp)
  | ite (c a b : Exp)
  deriving Lean.ToExpr

/-- The type of a declared variable: a bit vector of width `w`, or a Boolean. -/
inductive Ty where
  | bv (w : Nat)
  | bool
  deriving Lean.ToExpr

/-- An event of a trace.  `readMem d a k` reads the `k` bytes from the address `a` as `d`, and
`writeMem a d k` writes `d` as `k` bytes from `a`.  `readGprs v i xs` is the primitive
`read_register_from_vector`, which reads `v` at the index `i` from `R0` to `R30`, whose values are
`xs`, and `writeGprs i v xs` is `write_register_from_vector`, which writes `v` at `i`. -/
inductive Event where
  | declare (x : Nat) (ty : Ty)
  | define (x : Nat) (e : Exp)
  | assert (e : Exp)
  | assume (e : Exp)
  | assumeReg (r : String) (al : List String) (v : RVal)
  | readReg (r : String) (al : List String) (v : RVal)
  | writeReg (r : String) (al : List String) (v : RVal)
  | readMem (d a : Base) (k : Nat)
  | writeMem (a d : Base) (k : Nat)
  | readGprs (v i : Base) (xs : List Base)
  | writeGprs (i v : Base) (xs : List Base)
  | skip
  deriving Lean.ToExpr

/-- A trace: events, each followed by the rest, ending either with nothing or with `cases`. -/
inductive Trace where
  | done
  | event (e : Event) (t : Trace)
  | cases (ts : List Trace)
  deriving Lean.ToExpr

/-- A field of the header: its name, its width, and the variable that holds it. -/
structure Segment where
  name : String
  width : Nat
  var : Nat
  deriving Lean.ToExpr

/-- What `isla-footprint` prints for an opcode: the fields of the header, empty for an opcode
without symbolic fields, and the trace. -/
structure Footprint where
  segments : List Segment
  trace : Trace
  deriving Lean.ToExpr

/-- A value: a bit vector of width `w` whose value `n` is below `2 ^ w`, a Boolean, a member of
an enumeration, a struct, or a vector. -/
inductive Val where
  | bits (w n : Nat)
  | bool (b : Bool)
  | enum (name : String)
  | struct (fields : List (String × Val))
  | vec (elems : List Val)

/-- The values of the variables. -/
abbrev Vars := Nat → Option Val

/-- `ρ` with the variable `x` set to `v`. -/
def Vars.set (ρ : Vars) (x : Nat) (v : Val) : Vars := fun y => if y = x then some v else ρ y

/-- The registers outside the model, by name. -/
abbrev Sys := String → Option Val

/-- `σ` with the register `r` set to `v`. -/
def Sys.set (σ : Sys) (r : String) (v : Val) : Sys := fun q => if q = r then some v else σ q

/-- The value of an atom, `none` for an undeclared variable. -/
def Base.eval (ρ : Vars) : Base → Option Val
  | .var x => ρ x
  | .bits w n => some (.bits w n)
  | .bool b => some (.bool b)
  | .enum e => some (.enum e)

def Base.evalAll (ρ : Vars) : List Base → Option (List Val)
  | [] => some []
  | b :: bs =>
    match b.eval ρ, Base.evalAll ρ bs with
    | some v, some vs => some (v :: vs)
    | _, _ => none

def Base.evalFields (ρ : Vars) : List (String × Base) → Option (List (String × Val))
  | [] => some []
  | (f, b) :: fs =>
    match b.eval ρ, Base.evalFields ρ fs with
    | some v, some vs => some ((f, v) :: vs)
    | _, _ => none

/-- The value of a register event's value. -/
def RVal.eval (ρ : Vars) : RVal → Option Val
  | .base b => b.eval ρ
  | .struct fs => (Base.evalFields ρ fs).map .struct
  | .vec bs => (Base.evalAll ρ bs).map .vec

/-- The part of `v` at the accessor path `al`, a list of field names. -/
def acc : List String → Val → Option Val
  | [], v => some v
  | f :: al, .struct fs => (fs.lookup f).bind (acc al)
  | _ :: _, _ => none

/-- `v` with its part at the accessor path `al` replaced by `x`. -/
def upd : List String → Val → Val → Option Val
  | [], _, x => some x
  | f :: al, .struct fs, x =>
    (fs.lookup f).bind fun w => (upd al w x).map fun w' =>
      .struct (fs.map fun p => if p.1 = f then (f, w') else p)
  | _ :: _, _, _ => none

/-- The part of register `r` of `σ` at the accessor path `al`. -/
def Sys.get (σ : Sys) (r : String) (al : List String) : Option Val := (σ r).bind (acc al)

/-- A part of the model's state that a register access names. -/
inductive Part where
  | x (i : Fin 31)
  | sp
  | pc
  | n
  | z
  | c
  | v

/-- The registers `R0` to `R30` of the Sail model, the general registers X0 to X30. -/
def gprs : List (String × Fin 31) :=
  [("R0", 0), ("R1", 1), ("R2", 2), ("R3", 3), ("R4", 4), ("R5", 5), ("R6", 6), ("R7", 7),
    ("R8", 8), ("R9", 9), ("R10", 10), ("R11", 11), ("R12", 12), ("R13", 13), ("R14", 14),
    ("R15", 15), ("R16", 16), ("R17", 17), ("R18", 18), ("R19", 19), ("R20", 20), ("R21", 21),
    ("R22", 22), ("R23", 23), ("R24", 24), ("R25", 25), ("R26", 26), ("R27", 27), ("R28", 28),
    ("R29", 29), ("R30", 30)]

/-- The index of the general register named `r`. -/
def gpr (r : String) : Option (Fin 31) := gprs.lookup r

/-- The part of the model's state that the register `r` at the accessor path `al` names: the
general registers, `SP_EL1`, the program counter `_PC`, and the fields `N`, `Z`, `C`, and `V` of
`PSTATE`. -/
def part (r : String) : List String → Option Part
  | [] => if r = "SP_EL1" then some .sp else if r = "_PC" then some .pc else (gpr r).map .x
  | [f] =>
    if r = "PSTATE" then
      if f = "N" then some .n else if f = "Z" then some .z else if f = "C" then some .c
      else if f = "V" then some .v else none
    else none
  | _ :: _ :: _ => none

/-- A flag as a bit vector of width 1. -/
def bit (b : Bool) : Val := .bits 1 (if b then 1 else 0)

/-- The value of a part of the model's state: a register as a bit vector of width 64, a flag as
one of width 1. -/
def partGet (s : State) : Part → Val
  | .x i => .bits 64 (s.regs i).toNat
  | .sp => .bits 64 s.sp.toNat
  | .pc => .bits 64 s.pc.toNat
  | .n => bit s.nFlag
  | .z => bit s.zFlag
  | .c => bit s.cFlag
  | .v => bit s.vFlag

/-- The state with a part set to `v`, `none` when `v` has the wrong width. -/
def partPut (s : State) : Part → Val → Option State
  | .x i, .bits 64 n => some { s with regs := fun j => if j = i then .ofNat n else s.regs j }
  | .sp, .bits 64 n => some { s with sp := .ofNat n }
  | .pc, .bits 64 n => some { s with pc := .ofNat n }
  | .n, .bits 1 n => some { s with nFlag := n = 1 }
  | .z, .bits 1 n => some { s with zFlag := n = 1 }
  | .c, .bits 1 n => some { s with cFlag := n = 1 }
  | .v, .bits 1 n => some { s with vFlag := n = 1 }
  | _, _ => none

/-- The value of the register `r` at the accessor path `al`: the model's part that they name, or
else the part at `al` of the register outside the model.  `PSTATE` as a whole has no value, since
the model holds four of its fields. -/
def regGet (s : State) (σ : Sys) (r : String) (al : List String) : Option Val :=
  match part r al with
  | some p => some (partGet s p)
  | none => if r = "PSTATE" ∧ al = [] then none else σ.get r al

/-- The state and registers after writing `x` to the register `r` at the accessor path `al`.  A
whole register outside the model takes `x` whether or not `σ` holds it. -/
def regSet (s : State) (σ : Sys) (r : String) (al : List String) (x : Val) :
    Option (State × Sys) :=
  match part r al with
  | some p => (partPut s p x).map (·, σ)
  | none =>
    if r = "PSTATE" ∧ al = [] then none
    else match al with
      | [] => some (s, σ.set r x)
      | _ :: _ => (σ r).bind fun w => (upd al w x).map fun w' => (s, σ.set r w')

/-- The values of `R0` to `R30` in the state `s`, as the vector primitives list them. -/
def gprVals (s : State) : List Val := gprs.map fun p => .bits 64 (s.regs p.2).toNat

/-- The register that `read_register_from_vector` reads at the index `i` below 32: register `i`
below 31, and `R0`, the base of Isla's chain, at 31. -/
def regAt (s : State) (i : Nat) : UInt64 := if h : i < 31 then s.regs ⟨i, h⟩ else s.regs 0

/-- The state after `write_register_from_vector` writes `v` at the index `i` below 32: register
`i` set to `v` below 31, and no change at 31. -/
def setRegAt (s : State) (i : Nat) (v : UInt64) : State :=
  if i < 31 then { s with regs := fun j => if j.val = i then v else s.regs j } else s

/-- The bit vector `n` of width `w` as a two's complement integer: `n` less `2 ^ w` times its top
bit, `n / 2 ^ (w - 1)`. -/
def sint (w n : Nat) : Int := (n : Int) - (n / 2 ^ (w - 1) * 2 ^ w : Nat)

/-- SMT-LIB's `bvudiv`, all ones for a divisor of zero. -/
def udiv (w a b : Nat) : Nat := if b = 0 then 2 ^ w - 1 else a / b

/-- SMT-LIB's `bvurem`, the dividend for a divisor of zero. -/
def urem (a b : Nat) : Nat := if b = 0 then a else a % b

/-- SMT-LIB's `bvneg`. -/
def neg (w a : Nat) : Nat := (2 ^ w - a) % 2 ^ w

/-- SMT-LIB's `bvsdiv`, defined from `bvudiv` and `bvneg` by the signs of `a` and `b`. -/
def sdiv (w a b : Nat) : Nat :=
  if 2 ^ w ≤ 2 * a then
    if 2 ^ w ≤ 2 * b then udiv w (neg w a) (neg w b) else neg w (udiv w (neg w a) b)
  else if 2 ^ w ≤ 2 * b then neg w (udiv w a (neg w b)) else udiv w a b

/-- SMT-LIB's `bvsrem`, defined from `bvurem` and `bvneg` by the signs of `a` and `b`. -/
def srem (w a b : Nat) : Nat :=
  if 2 ^ w ≤ 2 * a then
    if 2 ^ w ≤ 2 * b then neg w (urem (neg w a) (neg w b)) else neg w (urem (neg w a) b)
  else if 2 ^ w ≤ 2 * b then urem a (neg w b) else urem a b

/-- SMT-LIB's `bvlshr`: `a` shifted right by `b` places, zero once `b` reaches `w`. -/
def lshr (w a b : Nat) : Nat := if b < w then a / 2 ^ b else 0

/-- SMT-LIB's `bvashr`: `bvlshr` for a clear top bit, else the complement of `bvlshr` of the
complement. -/
def ashr (w a b : Nat) : Nat :=
  if a / 2 ^ (w - 1) % 2 = 0 then lshr w a b else 2 ^ w - 1 - lshr w (2 ^ w - 1 - a) b

/-- The operator `o` on `v`.  `(_ sign_extend k)` adds the top bit, `n / 2 ^ (w - 1)`, times the
`k` bits above the `w` bits of `n`. -/
def Unop.apply : Unop → Val → Option Val
  | .not, .bool b => some (.bool !b)
  | .bvnot, .bits w n => some (.bits w (2 ^ w - 1 - n))
  | .extract hi lo, .bits w n =>
    if lo ≤ hi ∧ hi < w then some (.bits (hi + 1 - lo) (n / 2 ^ lo % 2 ^ (hi + 1 - lo)))
    else none
  | .zeroExtend k, .bits w n => some (.bits (w + k) n)
  | .signExtend k, .bits w n =>
    some (.bits (w + k) (n + n / 2 ^ (w - 1) * (2 ^ (w + k) - 2 ^ w)))
  | _, _ => none

/-- The operator `o` on two bit vectors `a` and `b` of width `w`. -/
def Binop.arith : Binop → Nat → Nat → Nat → Option Val
  | .eq, _, a, b => some (.bool (decide (a = b)))
  | .bvadd, w, a, b => some (.bits w ((a + b) % 2 ^ w))
  | .bvsub, w, a, b => some (.bits w ((a + (2 ^ w - b)) % 2 ^ w))
  | .bvmul, w, a, b => some (.bits w (a * b % 2 ^ w))
  | .bvand, w, a, b => some (.bits w (a &&& b))
  | .bvor, w, a, b => some (.bits w (a ||| b))
  | .bvshl, w, a, b => some (.bits w (if b < w then a * 2 ^ b % 2 ^ w else 0))
  | .bvlshr, w, a, b => some (.bits w (lshr w a b))
  | .bvashr, w, a, b => some (.bits w (ashr w a b))
  | .bvsdiv, w, a, b => some (.bits w (sdiv w a b))
  | .bvsrem, w, a, b => some (.bits w (srem w a b))
  | .bvule, _, a, b => some (.bool (decide (a ≤ b)))
  | .bvuge, _, a, b => some (.bool (decide (b ≤ a)))
  | .bvslt, w, a, b => some (.bool (decide (sint w a < sint w b)))
  | .bvsle, w, a, b => some (.bool (decide (sint w a ≤ sint w b)))
  | .bvsgt, w, a, b => some (.bool (decide (sint w b < sint w a)))
  | .bvsge, w, a, b => some (.bool (decide (sint w b ≤ sint w a)))
  | .and, _, _, _ | .or, _, _, _ | .concat, _, _, _ => none

/-- The operator `o` on two values: `=` on Booleans, on members of enumerations, or on bit vectors
of one width, `and` and `or` on Booleans, `concat` on two bit vectors, and arithmetic on bit
vectors of one width. -/
def Binop.apply : Binop → Val → Val → Option Val
  | .eq, .bool a, .bool b => some (.bool (decide (a = b)))
  | .eq, .enum a, .enum b => some (.bool (decide (a = b)))
  | .and, .bool a, .bool b => some (.bool (a && b))
  | .or, .bool a, .bool b => some (.bool (a || b))
  | .concat, .bits w a, .bits w' b => some (.bits (w + w') (a * 2 ^ w' + b))
  | o, .bits w a, .bits w' b => if w = w' then o.arith w a b else none
  | _, _, _ => none

/-- The value of an expression, `none` when an operator does not apply to its arguments. -/
def Exp.eval (s : State) (σ : Sys) (ρ : Vars) : Exp → Option Val
  | .base b => b.eval ρ
  | .reg r al => regGet s σ r al
  | .un o e => (e.eval s σ ρ).bind o.apply
  | .bin o a b =>
    match a.eval s σ ρ, b.eval s σ ρ with
    | some x, some y => o.apply x y
    | _, _ => none
  | .ite c a b =>
    match c.eval s σ ρ, a.eval s σ ρ, b.eval s σ ρ with
    | some (.bool k), some (.bits w x), some (.bits w' y) =>
      if w = w' then some (.bits w (cond k x y)) else none
    | some (.bool k), some (.bool x), some (.bool y) => some (.bool (cond k x y))
    | some (.bool k), some (.enum x), some (.enum y) => some (.enum (cond k x y))
    | _, _, _ => none

/-- The number whose base-256 digits, the lowest first, are the `k` bytes of `m` from `a`. -/
def bytes (m : UInt64 → UInt8) (a : UInt64) : Nat → Nat
  | 0 => 0
  | k + 1 => (m a).toNat + 256 * bytes m (a + 1) k

/-- The memory `m` with the `k` bytes from `a` set to the base-256 digits of `x`, the lowest
first. -/
def writeBytes (m : UInt64 → UInt8) (a : UInt64) (x : Nat) : Nat → UInt64 → UInt8
  | 0 => m
  | k + 1 => writeBytes (fun b => if b = a then .ofNat (x % 256) else m b) (a + 1) (x / 256) k

/-- The state after a write of `x` as `k` bytes from `a`: a byte at the UART goes to the output,
and every other write to memory. -/
def store (P : Platform) (s : State) (a : UInt64) (x k : Nat) : State :=
  if a = P.uart ∧ k = 1 then { s with out := s.out ++ [.ofNat x] }
  else { s with mem := writeBytes s.mem a x k }

/-- How a path of a trace ends: in a state of the model and the registers outside it, or in
failure. -/
inductive Outcome where
  | done (s : State) (σ : Sys)
  | fail

/-- The outcome at the end of a path from the state `s` and the registers `σ`: `_PC` advances by
4 while `__BranchTaken` is false. -/
def finish (s : State) (σ : Sys) : Outcome :=
  match σ "__BranchTaken" with
  | some (.bool false) => .done { s with pc := s.pc + 4 } σ
  | some (.bool true) => .done s σ
  | _ => .fail

mutual

/-- Some path of the trace from the state `s`, the registers `σ`, and the variables `ρ` ends in
the outcome `o`. -/
def Trace.Run (P : Platform) : Trace → Vars → State → Sys → Outcome → Prop
  | .done, _, s, σ, o => o = finish s σ
  | .cases ts, ρ, s, σ, o => Trace.RunSome P ts ρ s σ o
  | .event (.declare x (.bv w)) t, ρ, s, σ, o =>
    match ρ x with
    | none => ∃ n, n < 2 ^ w ∧ t.Run P (ρ.set x (.bits w n)) s σ o
    | some (.bits w' n) => if w' = w ∧ n < 2 ^ w then t.Run P ρ s σ o else o = .fail
    | some _ => o = .fail
  | .event (.declare x .bool) t, ρ, s, σ, o =>
    match ρ x with
    | none => ∃ b, t.Run P (ρ.set x (.bool b)) s σ o
    | some (.bool _) => t.Run P ρ s σ o
    | some _ => o = .fail
  | .event (.define x e) t, ρ, s, σ, o =>
    match e.eval s σ ρ with
    | some v => t.Run P (ρ.set x v) s σ o
    | none => o = .fail
  | .event (.assert e) t, ρ, s, σ, o =>
    match e.eval s σ ρ with
    | some (.bool b) => b = true ∧ t.Run P ρ s σ o
    | _ => o = .fail
  | .event (.assume e) t, ρ, s, σ, o =>
    match e.eval s σ ρ with
    | some (.bool b) => if b then t.Run P ρ s σ o else o = .fail
    | _ => o = .fail
  | .event (.assumeReg r al v) t, ρ, s, σ, o =>
    match regGet s σ r al, v.eval ρ with
    | some w, some w' => w = w' ∧ t.Run P ρ s σ o ∨ w ≠ w' ∧ o = .fail
    | _, _ => o = .fail
  | .event (.readReg r al v) t, ρ, s, σ, o =>
    match regGet s σ r al, (v.eval ρ).bind (acc al) with
    | some w, some w' => w = w' ∧ t.Run P ρ s σ o
    | _, _ => o = .fail
  | .event (.writeReg r al v) t, ρ, s, σ, o =>
    match ((v.eval ρ).bind (acc al)).bind (regSet s σ r al) with
    | some (s', σ') => t.Run P ρ s' σ' o
    | none => o = .fail
  | .event (.readMem d a k) t, ρ, s, σ, o =>
    match d.eval ρ, a.eval ρ with
    | some (.bits w x), some (.bits 64 y) =>
      if w = 8 * k then x = bytes s.mem (.ofNat y) k ∧ t.Run P ρ s σ o else o = .fail
    | _, _ => o = .fail
  | .event (.writeMem a d k) t, ρ, s, σ, o =>
    match a.eval ρ, d.eval ρ with
    | some (.bits 64 y), some (.bits w x) =>
      if w = 8 * k then t.Run P ρ (store P s (.ofNat y) x k) σ o else o = .fail
    | _, _ => o = .fail
  | .event (.readGprs v i xs) t, ρ, s, σ, o =>
    match v.eval ρ, i.eval ρ, Base.evalAll ρ xs with
    | some (.bits 64 y), some (.bits _ k), some ws =>
      ws = gprVals s ∧ y = (regAt s (k % 32)).toNat ∧ t.Run P ρ s σ o
    | _, _, _ => o = .fail
  | .event (.writeGprs i v xs) t, ρ, s, σ, o =>
    match i.eval ρ, v.eval ρ, Base.evalAll ρ xs with
    | some (.bits _ k), some (.bits 64 y), some ws =>
      ws = gprVals s ∧ t.Run P ρ (setRegAt s (k % 32) (.ofNat y)) σ o
    | _, _, _ => o = .fail
  | .event .skip t, ρ, s, σ, o => t.Run P ρ s σ o

/-- Some path of some trace of `ts` ends in the outcome `o`. -/
def Trace.RunSome (P : Platform) : List Trace → Vars → State → Sys → Outcome → Prop
  | [], _, _, _, _ => False
  | t :: ts, ρ, s, σ, o => t.Run P ρ s σ o ∨ Trace.RunSome P ts ρ s σ o

end

/-- The values of the fields of an opcode, by name. -/
abbrev Fields := List (String × Nat)

/-- The variables of the header bound to the values of the fields `f`. -/
def Footprint.vars (F : Footprint) (f : Fields) : Vars :=
  F.segments.foldl (fun ρ g => ρ.set g.var (.bits g.width ((f.lookup g.name).getD 0)))
    fun _ => none

/-- Some path of the footprint `F` for the fields `f` ends in the outcome `o`: its trace runs
with the header's variables bound and `__BranchTaken` false. -/
def Footprint.Run (P : Platform) (F : Footprint) (f : Fields) (s : State) (σ : Sys)
    (o : Outcome) : Prop :=
  F.trace.Run P (F.vars f) s (σ.set "__BranchTaken" (.bool false)) o

/-- The registers that an expression reads, with their accessor paths. -/
def Exp.regs : Exp → List (String × List String)
  | .base _ => []
  | .reg r al => [(r, al)]
  | .un _ e => e.regs
  | .bin _ a b => a.regs ++ b.regs
  | .ite c a b => c.regs ++ a.regs ++ b.regs

/-- The registers outside the model that an event reads, with their accessor paths. -/
def Event.reads : Event → List (String × List String)
  | .define _ e | .assert e | .assume e => e.regs.filter fun q => (part q.1 q.2).isNone
  | .assumeReg r al _ | .readReg r al _ => if (part r al).isNone then [(r, al)] else []
  | _ => []

mutual

/-- The registers outside the model that a trace reads, with their accessor paths. -/
def Trace.reads : Trace → List (String × List String)
  | .done => []
  | .event e t => e.reads ++ t.reads
  | .cases ts => Trace.readsAll ts

def Trace.readsAll : List Trace → List (String × List String)
  | [] => []
  | t :: ts => t.reads ++ Trace.readsAll ts

end

/-! The reader of trace files. -/

/-- An s-expression: a bare token, a name written between bars, a string, or a list. -/
inductive Sx where
  | atom (s : String)
  | name (s : String)
  | str (s : String)
  | list (l : List Sx)
  deriving Inhabited

/-- `cs` without its leading white space and comments, which run from `;` to the end of a line. -/
partial def skipSpace : List Char → List Char
  | ';' :: cs => skipSpace (cs.dropWhile (· ≠ '\n'))
  | c :: cs => if c.isWhitespace then skipSpace cs else c :: cs
  | [] => []

/-- The characters of `cs` up to the closing character `e`, and the characters after it. -/
def closed (e : Char) (cs : List Char) : Except String (String × List Char) :=
  match cs.span (· ≠ e) with
  | (a, _ :: r) => .ok (String.ofList a, r)
  | _ => .error s!"no closing {e}"

mutual

/-- The s-expression at the front of `cs`, and the characters after it. -/
partial def readSx (cs : List Char) : Except String (Sx × List Char) :=
  match skipSpace cs with
  | '(' :: r => readList r #[]
  | '|' :: r => (fun (a, r) => (.name a, r)) <$> closed '|' r
  | '"' :: r => (fun (a, r) => (.str a, r)) <$> closed '"' r
  | ')' :: _ => .error "unexpected )"
  | [] => .error "unexpected end of file"
  | r =>
    let (a, r) := r.span fun c => !(c.isWhitespace || c == '(' || c == ')')
    .ok (.atom (String.ofList a), r)

/-- The elements of a list up to its closing parenthesis, after the elements `acc`. -/
partial def readList (cs : List Char) (acc : Array Sx) : Except String (Sx × List Char) :=
  match skipSpace cs with
  | ')' :: r => .ok (.list acc.toList, r)
  | r => do
    let (x, r) ← readSx r
    readList r (acc.push x)

end

/-- The value of the digit `c` in base 16, or `none`. -/
def digit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The natural number written in base `b` with the digits `cs`, one or more. -/
def readNat (b : Nat) (cs : List Char) : Except String Nat :=
  if cs = [] then .error "empty number"
  else cs.foldlM (init := 0) fun n c =>
    match digit c with
    | some d => if d < b then .ok (n * b + d) else .error s!"bad digit {c}"
    | none => .error s!"bad digit {c}"

/-- An atom: `true`, `false`, `v<n>`, `#x...`, `#b...`, `|name|`, or `(_ bv<n> <w>)`, whose
negative `n` stands for `2 ^ w + n`. -/
def toBase : Sx → Except String Base
  | .atom "true" => .ok (.bool true)
  | .atom "false" => .ok (.bool false)
  | .atom a =>
    match a.toList with
    | 'v' :: ds => .var <$> readNat 10 ds
    | '#' :: 'x' :: ds => .bits (4 * ds.length) <$> readNat 16 ds
    | '#' :: 'b' :: ds => .bits ds.length <$> readNat 2 ds
    | _ => .error s!"unknown atom {a}"
  | .name e => .ok (.enum e)
  | .list [.atom "_", .atom v, .atom w] => do
    let w ← readNat 10 w.toList
    match v.toList with
    | 'b' :: 'v' :: '-' :: ds => do
      let n ← readNat 10 ds
      .ok (.bits w ((2 ^ w - n % 2 ^ w) % 2 ^ w))
    | 'b' :: 'v' :: ds => do
      let n ← readNat 10 ds
      .ok (.bits w (n % 2 ^ w))
    | _ => .error s!"unknown literal {v}"
  | _ => .error "bad atom"

/-- A register value: an atom, `(_ struct (|f| atom) ...)`, or `(_ vec atom ...)`. -/
def toRVal : Sx → Except String RVal
  | .list (.atom "_" :: .atom "struct" :: fs) =>
    .struct <$> fs.mapM fun
      | .list [.name f, b] => (f, ·) <$> toBase b
      | _ => .error "bad struct field"
  | .list (.atom "_" :: .atom "vec" :: bs) => .vec <$> bs.mapM toBase
  | x => .base <$> toBase x

/-- An accessor path: `nil`, or a list of `(_ field |f|)`. -/
def toPath : Sx → Except String (List String)
  | .atom "nil" => .ok []
  | .list l => l.mapM fun
    | .list [.atom "_", .atom "field", .name f] => .ok f
    | _ => .error "bad accessor"
  | _ => .error "bad accessor list"

/-- The operator of two or more arguments named `f`, and whether it takes more than two. -/
def binop : String → Except String (Binop × Bool)
  | "=" => .ok (.eq, false)
  | "and" => .ok (.and, true)
  | "or" => .ok (.or, true)
  | "concat" => .ok (.concat, true)
  | "bvadd" => .ok (.bvadd, true)
  | "bvsub" => .ok (.bvsub, false)
  | "bvmul" => .ok (.bvmul, true)
  | "bvand" => .ok (.bvand, true)
  | "bvor" => .ok (.bvor, true)
  | "bvshl" => .ok (.bvshl, false)
  | "bvlshr" => .ok (.bvlshr, false)
  | "bvashr" => .ok (.bvashr, false)
  | "bvsdiv" => .ok (.bvsdiv, false)
  | "bvsrem" => .ok (.bvsrem, false)
  | "bvule" => .ok (.bvule, false)
  | "bvuge" => .ok (.bvuge, false)
  | "bvslt" => .ok (.bvslt, false)
  | "bvsle" => .ok (.bvsle, false)
  | "bvsgt" => .ok (.bvsgt, false)
  | "bvsge" => .ok (.bvsge, false)
  | f => .error s!"unknown operator {f}"

/-- An expression, where `(|r| path)` reads a register, or the field `r` of the header `segs`
when `r` names one and the path is `nil`. -/
partial def toExp (segs : List Segment) : Sx → Except String Exp
  | .list [.list [.atom "_", .atom "extract", .atom hi, .atom lo], e] => do
    .un (.extract (← readNat 10 hi.toList) (← readNat 10 lo.toList)) <$> toExp segs e
  | .list [.list [.atom "_", .atom "zero_extend", .atom k], e] => do
    .un (.zeroExtend (← readNat 10 k.toList)) <$> toExp segs e
  | .list [.list [.atom "_", .atom "sign_extend", .atom k], e] => do
    .un (.signExtend (← readNat 10 k.toList)) <$> toExp segs e
  | .list [.atom "not", e] => .un .not <$> toExp segs e
  | .list [.atom "bvnot", e] => .un .bvnot <$> toExp segs e
  | .list [.atom "ite", c, a, b] =>
    return .ite (← toExp segs c) (← toExp segs a) (← toExp segs b)
  | .list [.name r, al] => do
    let al ← toPath al
    match segs.find? (·.name == r), al with
    | some g, [] => return .base (.var g.var)
    | _, _ => return .reg r al
  | .list (.atom "_" :: l) => .base <$> toBase (.list (.atom "_" :: l))
  | .list (.atom f :: a :: b :: rest) => do
    let (o, many) ← binop f
    if !rest.isEmpty && !many then throw s!"too many arguments to {f}"
    let first := Exp.bin o (← toExp segs a) (← toExp segs b)
    rest.foldlM (fun e x => Exp.bin o e <$> toExp segs x) first
  | x => .base <$> toBase x

/-- A type: `(_ BitVec w)` or `Bool`. -/
def toTy : Sx → Except String Ty
  | .list [.atom "_", .atom "BitVec", .atom w] => .bv <$> readNat 10 w.toList
  | .atom "Bool" => .ok .bool
  | _ => .error "unknown type"

/-- The number `n` of the variable `v<n>`. -/
def toVar : Sx → Except String Nat
  | .atom a =>
    match a.toList with
    | 'v' :: ds => readNat 10 ds
    | _ => .error s!"bad variable {a}"
  | _ => .error "bad variable"

/-- The references `(_ reg |R0|)` to `(_ reg |R30|)` in order, which every vector primitive of
the traces names. -/
def gprRefs : List Sx := gprs.map fun p => .list [.atom "_", .atom "reg", .name p.1]

/-- The atoms of `(_ vec atom ...)`. -/
def toAtoms : Sx → Except String (List Base)
  | .list (.atom "_" :: .atom "vec" :: bs) => bs.mapM toBase
  | _ => .error "expected a vector"

/-- Whether two s-expressions are equal. -/
partial def Sx.beq : Sx → Sx → Bool
  | .atom a, .atom b | .name a, .name b | .str a, .str b => a == b
  | .list a, .list b => a.length == b.length && (a.zip b).all fun (x, y) => x.beq y
  | _, _ => false

/-- An event other than `cases`.  A memory read's kind and a memory write's kind and result are
dropped, and a vector primitive must name `R0` to `R30` in order. -/
def toEvent (segs : List Segment) : Sx → Except String Event
  | .list [.atom "declare-const", x, ty] => return .declare (← toVar x) (← toTy ty)
  | .list [.atom "define-const", x, e] => return .define (← toVar x) (← toExp segs e)
  | .list [.atom "assert", e] => .assert <$> toExp segs e
  | .list [.atom "assume", e] => .assume <$> toExp segs e
  | .list [.atom "assume-reg", .name r, al, v] => return .assumeReg r (← toPath al) (← toRVal v)
  | .list [.atom "read-reg", .name r, al, v] => return .readReg r (← toPath al) (← toRVal v)
  | .list [.atom "write-reg", .name r, al, v] => return .writeReg r (← toPath al) (← toRVal v)
  | .list [.atom "read-mem", d, _, a, .atom k] =>
    return .readMem (← toBase d) (← toBase a) (← readNat 10 k.toList)
  | .list [.atom "write-mem", _, _, a, d, .atom k] =>
    return .writeMem (← toBase a) (← toBase d) (← readNat 10 k.toList)
  | .list [.atom "abstract-primop", .name "read_register_from_vector", v, i, .list refs, xs] =>
    if Sx.beq (.list refs) (.list (.atom "_" :: .atom "vec" :: gprRefs)) then
      return .readGprs (← toBase v) (← toBase i) (← toAtoms xs)
    else .error "read_register_from_vector of registers other than R0 to R30"
  | .list [.atom "abstract-primop", .name "write_register_from_vector",
      .list [.atom "_", .atom "unit"], i, v, .list refs, xs] =>
    if Sx.beq (.list refs) (.list (.atom "_" :: .atom "vec" :: gprRefs)) then
      return .writeGprs (← toBase i) (← toBase v) (← toAtoms xs)
    else .error "write_register_from_vector of registers other than R0 to R30"
  | .list (.atom h :: _) =>
    if h ∈ ["cycle", "call", "return", "define-enum", "branch-address"] then .ok .skip
    else .error s!"unknown event {h}"
  | _ => .error "bad event"

mutual

/-- A trace `(trace event ...)`. -/
partial def toTrace (segs : List Segment) : Sx → Except String Trace
  | .list (.atom "trace" :: es) => toEvents segs es
  | _ => .error "expected (trace ...)"

/-- The events of a trace, the last of which may be `(cases "loc" trace ...)`. -/
partial def toEvents (segs : List Segment) : List Sx → Except String Trace
  | [] => .ok .done
  | [.list (.atom "cases" :: .str _ :: ts)] => .cases <$> ts.mapM (toTrace segs)
  | e :: es => return .event (← toEvent segs e) (← toEvents segs es)

end

/-- The fields of `(segments (|name| width v<n>) ...)`. -/
def toSegments : List Sx → Except String (List Segment)
  | [] => .ok []
  | .list [.name f, .atom w, x] :: gs => do
    return ⟨f, ← readNat 10 w.toList, ← toVar x⟩ :: (← toSegments gs)
  | _ => .error "bad segment"

/-- The footprint that the text `s` of a file holds: an optional header and a trace. -/
def parse (s : String) : Except String Footprint := do
  let (x, r) ← readSx s.toList
  let (segs, x, r) ← match x with
    | .list (.atom "segments" :: gs) => do
      let segs ← toSegments gs
      let (x, r) ← readSx r
      pure (segs, x, r)
    | _ => pure ([], x, r)
  if skipSpace r ≠ [] then throw "text after the trace"
  return ⟨segs, ← toTrace segs x⟩

open Lean Elab Term in
/-- The footprint in the file at the path, read when the term elaborates. -/
elab "isla_trace% " path:str : term => do
  let s ← IO.FS.readFile path.getString
  match parse s with
  | .ok t => return toExpr t
  | .error e => throwError "{path.getString}: {e}"

end LeanExe.A64.Isla
