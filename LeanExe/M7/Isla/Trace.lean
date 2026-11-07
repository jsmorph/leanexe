import LeanExe.A64.Isla.Trace
import LeanExe.M7.Machine

/-!
The traces that Isla computes for the Thumb forms of `LeanExe/M7/Machine.lean` from the A-profile
Sail model, in AArch32 Thumb state at EL0 under an AArch64 EL1, as a relation between states of an
A-profile machine that contains the model's state.  The syntax, the values, the operators, and the
reader `isla_trace%` are those of `LeanExe/A64/Isla/Trace.lean`, whose documentation describes
them, and the semantics follows the A64 semantics there, with the changes that the AArch32 state
needs.

AArch32 at EL0 under an AArch64 EL1 keeps its registers in the low 32 bits of the X registers: in
User mode, r0 to r12 are bits 31 to 0 of X0 to X12, SP is those of X13, and LR those of X14, and
the other X registers hold the banked registers of the other modes (`LookUpRIndex`, `v8_base.sail`
6343).  `Mach` holds the model's `State` and the parts of the A-profile machine that the model
lacks: bits 63 to 32 of X0 to X14, X15 to X30, and the bytes of memory at physical addresses from
2^32, where the traces of the loads and stores find their translation table.  The registers `R0`
to `R30` of the Sail model are X0 to X30, the program counter `_PC` holds the model's program
counter zero-extended to 64 bits, and the fields `N`, `Z`, `C`, and `V` of `PSTATE` are the
model's flags.  Every other register lies outside the model, in `σ`, with `PSTATE`'s other fields
in a struct.

The rules differ from those of the A64 semantics as follows.

1. A write of `_PC` sets the model's program counter when the value is below 2^32 and ends the path
   in `fail` otherwise.  A write of `R0` to `R14` sets the register's low word in the model and its
   high word in `Mach.hi`, and one of `R15` to `R30` sets `Mach.xs`.
2. At the end of a path, while `__BranchTaken` is false, the program counter advances by the
   instruction's length, 4 bytes for a 32-bit opcode and 2 for a 16-bit one, and the path ends in
   `fail` when the sum reaches 2^32.  `__InstructionExecute` writes `_PC` with the sum of `_PC` and
   `ThisInstrLength()` divided by 8 in 64 bits (`fetch.sail` 331-333), a value that rule 1 rejects
   from 2^32.  The harness functions `isla_footprint_t32` and `isla_footprint_t16` of
   `tests/isla/armv9p4-t32.diff` replace the rest of `__InstructionExecute` as
   `isla_footprint_no_init` does for A64 (reading 4 of the A64 semantics), and they write
   `__DefaultCond`, AL outside an IT block, to `__currentCond` after the trace's `cycle` event, so
   that the trace records the write.  The same diff edits the decode clause of B T3
   (`instrs32.sail` 1478-1487) to write the opcode's `cond` field to `__currentCond`, the
   condition of B T3 that `CurrentCond()` of DDI 0403E.e A7.3.1 gives.  Arm's ASL declares
   `AArch32.CurrentCond` without defining it, and the check assumes the edit.
3. A read of `k` bytes at the physical address `a` is a device read when `k` is 4, `a` is below
   2^32, and the platform names `a` a device address: its value must be the next value of the
   device sequence `δ`, and the model's state records the access and counts the read.  A write of
   4 bytes there appends a write event.  Every other read and write concerns the bytes of memory,
   the model's below 2^32 and `Mach.far` above.  A trace's memory event carries no memory type, so
   the platform decides which accesses are device accesses, and the traces of `m7-traces.sh` map
   the model's device window as Device memory and DTCM as Normal memory.
4. The vector primitives read and write `R0` to `R30` as `Mach.x` and `Mach.setX` give them.
5. A call of an abstract function ends the path in `fail`.  The M7 traces come from runs without
   `--abstract`, so they hold no such call, and the semantics gives no function a meaning.
-/

namespace LeanExe.M7.Isla

open LeanExe.A64.Isla (Base Exp Event Trace Footprint Opcode Fields Val Vars Sys acc upd bit
  bytes writeBytes)

/-- The A-profile machine of a trace: the model's state, bits 63 to 32 of X0 to X14, X15 to X30, and
the bytes of memory at physical addresses from 2^32. -/
structure Mach where
  s : State
  hi : Fin 15 → UInt32
  xs : Fin 16 → UInt64
  far : UInt64 → UInt8

/-- The low word of X register `i` below 15: r0 to r12, SP, or LR. -/
def low (s : State) (i : Nat) : UInt32 :=
  if h : i < 13 then s.regs ⟨i, h⟩ else if i = 13 then s.sp else s.lr

/-- The state with the low word of X register `i` below 15 set to `v`. -/
def setLow (s : State) (i : Nat) (v : UInt32) : State :=
  if i < 13 then { s with regs := fun j => if j.val = i then v else s.regs j }
  else if i = 13 then { s with sp := v } else { s with lr := v }

/-- The value of X register `i`. -/
def Mach.x (m : Mach) (i : Nat) : Nat :=
  if h : i < 15 then (m.hi ⟨i, h⟩).toNat * 4294967296 + (low m.s i).toNat
  else if h' : i < 31 then (m.xs ⟨i - 15, by omega⟩).toNat else 0

/-- The machine with X register `i` below 31 set to the 64-bit value `n`. -/
def Mach.setX (m : Mach) (i n : Nat) : Mach :=
  if i < 15 then
    { m with s := setLow m.s i (.ofNat n),
             hi := fun j => if j.val = i then .ofNat (n / 4294967296) else m.hi j }
  else { m with xs := fun j => if j.val + 15 = i then .ofNat n else m.xs j }

/-- The bytes of memory by physical address: the model's below 2^32, `far` above. -/
def Mach.mem (m : Mach) (a : UInt64) : UInt8 :=
  if a.toNat < 4294967296 then m.s.mem a.toUInt32 else m.far a

/-- The machine whose memory holds the bytes of `f`: the model's memory takes those below 2^32 and
`far` those from 2^32, keeping its own values below 2^32, which `Mach.mem` does not read. -/
def Mach.setMem (m : Mach) (f : UInt64 → UInt8) : Mach :=
  { m with s := { m.s with mem := fun b => f b.toUInt64 },
           far := fun a => if a.toNat < 4294967296 then m.far a else f a }

/-- The registers `R0` to `R30` of the Sail model with their numbers. -/
def gprs : List (String × Nat) :=
  [("R0", 0), ("R1", 1), ("R2", 2), ("R3", 3), ("R4", 4), ("R5", 5), ("R6", 6), ("R7", 7),
    ("R8", 8), ("R9", 9), ("R10", 10), ("R11", 11), ("R12", 12), ("R13", 13), ("R14", 14),
    ("R15", 15), ("R16", 16), ("R17", 17), ("R18", 18), ("R19", 19), ("R20", 20), ("R21", 21),
    ("R22", 22), ("R23", 23), ("R24", 24), ("R25", 25), ("R26", 26), ("R27", 27), ("R28", 28),
    ("R29", 29), ("R30", 30)]

/-- A part of the model's state that a register access names. -/
inductive Part where
  | x (i : Nat)
  | pc
  | n
  | z
  | c
  | v

/-- The part of the model's state that the register `r` at the accessor path `al` names: `R0` to
`R30`, `_PC`, and the fields `N`, `Z`, `C`, and `V` of `PSTATE`. -/
def part (r : String) : List String → Option Part
  | [] => if r = "_PC" then some .pc else (gprs.lookup r).map .x
  | [f] =>
    if r = "PSTATE" then
      if f = "N" then some .n else if f = "Z" then some .z else if f = "C" then some .c
      else if f = "V" then some .v else none
    else none
  | _ :: _ :: _ => none

/-- The value of a part: an X register or the program counter as a bit vector of width 64, a flag as
one of width 1. -/
def partGet (m : Mach) : Part → Val
  | .x i => .bits 64 (m.x i)
  | .pc => .bits 64 m.s.pc.toNat
  | .n => bit m.s.nFlag
  | .z => bit m.s.zFlag
  | .c => bit m.s.cFlag
  | .v => bit m.s.vFlag

/-- The machine with a part set to `v`, `none` when `v` has the wrong width or, for the program
counter, does not fit 32 bits. -/
def partPut (m : Mach) : Part → Val → Option Mach
  | .x i, .bits 64 n => some (m.setX i n)
  | .pc, .bits 64 n => if n < 4294967296 then some { m with s := { m.s with pc := .ofNat n } }
      else none
  | .n, .bits 1 n => some { m with s := { m.s with nFlag := n = 1 } }
  | .z, .bits 1 n => some { m with s := { m.s with zFlag := n = 1 } }
  | .c, .bits 1 n => some { m with s := { m.s with cFlag := n = 1 } }
  | .v, .bits 1 n => some { m with s := { m.s with vFlag := n = 1 } }
  | _, _ => none

/-- The value of the register `r` at the accessor path `al`: the model's part that they name, or
else the part at `al` of the register outside the model.  `PSTATE` as a whole has no value. -/
def regGet (m : Mach) (σ : Sys) (r : String) (al : List String) : Option Val :=
  match part r al with
  | some p => some (partGet m p)
  | none => if r = "PSTATE" ∧ al = [] then none else σ.get r al

/-- The machine and registers after writing `x` to the register `r` at the accessor path `al`.  A
whole register outside the model takes `x` whether or not `σ` holds it. -/
def regSet (m : Mach) (σ : Sys) (r : String) (al : List String) (x : Val) :
    Option (Mach × Sys) :=
  match part r al with
  | some p => (partPut m p x).map (·, σ)
  | none =>
    if r = "PSTATE" ∧ al = [] then none
    else match al with
      | [] => some (m, σ.set r x)
      | _ :: _ => (σ r).bind fun w => (upd al w x).map fun w' => (m, σ.set r w')

/-- The values of `R0` to `R30`, as the vector primitives list them. -/
def gprVals (m : Mach) : List Val := gprs.map fun p => .bits 64 (m.x p.2)

/-- The register that `read_register_from_vector` reads at the index `i` below 32: register `i`
below 31, and `R0`, the base of Isla's chain, at 31. -/
def regAt (m : Mach) (i : Nat) : Nat := if i < 31 then m.x i else m.x 0

/-- The machine after `write_register_from_vector` writes `n` at the index `i` below 32: register
`i` set below 31, and no change at 31. -/
def setRegAt (m : Mach) (i n : Nat) : Mach := if i < 31 then m.setX i n else m

/-- The value of an expression, `none` when an operator does not apply to its arguments. -/
def eval (m : Mach) (σ : Sys) (ρ : Vars) : Exp → Option Val
  | .base b => b.eval ρ
  | .reg r al => regGet m σ r al
  | .un o e => (eval m σ ρ e).bind o.apply
  | .bin o a b =>
    match eval m σ ρ a, eval m σ ρ b with
    | some x, some y => o.apply x y
    | _, _ => none
  | .ite c a b =>
    match eval m σ ρ c, eval m σ ρ a, eval m σ ρ b with
    | some (.bool k), some (.bits w x), some (.bits w' y) =>
      if w = w' then some (.bits w (cond k x y)) else none
    | some (.bool k), some (.bool x), some (.bool y) => some (.bool (cond k x y))
    | some (.bool k), some (.enum x), some (.enum y) => some (.enum (cond k x y))
    | _, _, _ => none

/-- An access of `k` bytes at the physical address `a` is a device access: a word at an address
below 2^32 that the platform names a device address. -/
def device (P : Platform) (a k : Nat) : Bool := k == 4 && a < 4294967296 && P.device (.ofNat a)

/-- The machine after a device read of the value `v` at `a`. -/
def devRead (m : Mach) (a v : UInt32) : Mach :=
  { m with s := { m.s with trace := m.s.trace ++ [.read a v], reads := m.s.reads + 1 } }

/-- The machine after a write of `x` as `k` bytes from `a`: a device write at a device address, and
a write to memory everywhere else. -/
def store (P : Platform) (m : Mach) (a x k : Nat) : Mach :=
  if device P a k then
    { m with s := { m.s with trace := m.s.trace ++ [.write (.ofNat a) (.ofNat x)] } }
  else m.setMem (writeBytes m.mem (.ofNat a) x k)

/-- How a path of a trace ends: in a machine and the registers outside it, or in failure. -/
inductive Outcome where
  | done (m : Mach) (σ : Sys)
  | fail

/-- The outcome at the end of a path from the machine `m` and the registers `σ`: while
`__BranchTaken` is false, the program counter advances by `len` bytes, and the path fails when the
sum reaches 2^32. -/
def finish (len : Nat) (m : Mach) (σ : Sys) : Outcome :=
  match σ "__BranchTaken" with
  | some (.bool false) =>
    if m.s.pc.toNat + len < 4294967296 then
      .done { m with s := { m.s with pc := m.s.pc + .ofNat len } } σ
    else .fail
  | some (.bool true) => .done m σ
  | _ => .fail

mutual

/-- Some path of the trace from the machine `m`, the registers `σ`, and the variables `ρ` ends in
the outcome `o`, for the platform `P`, the device values `δ`, and an instruction of `len` bytes. -/
def run (P : Platform) (δ : Nat → UInt32) (len : Nat) :
    Trace → Vars → Mach → Sys → Outcome → Prop
  | .done, _, m, σ, o => o = finish len m σ
  | .cases ts, ρ, m, σ, o => runSome P δ len ts ρ m σ o
  | .event (.declare x (.bv w)) t, ρ, m, σ, o =>
    match ρ x with
    | none => ∃ n, n < 2 ^ w ∧ run P δ len t (ρ.set x (.bits w n)) m σ o
    | some (.bits w' n) => if w' = w ∧ n < 2 ^ w then run P δ len t ρ m σ o else o = .fail
    | some _ => o = .fail
  | .event (.declare x .bool) t, ρ, m, σ, o =>
    match ρ x with
    | none => ∃ b, run P δ len t (ρ.set x (.bool b)) m σ o
    | some (.bool _) => run P δ len t ρ m σ o
    | some _ => o = .fail
  | .event (.define x e) t, ρ, m, σ, o =>
    match eval m σ ρ e with
    | some v => run P δ len t (ρ.set x v) m σ o
    | none => o = .fail
  | .event (.assert e) t, ρ, m, σ, o =>
    match eval m σ ρ e with
    | some (.bool b) => b = true ∧ run P δ len t ρ m σ o
    | _ => o = .fail
  | .event (.assume e) t, ρ, m, σ, o =>
    match eval m σ ρ e with
    | some (.bool b) => if b then run P δ len t ρ m σ o else o = .fail
    | _ => o = .fail
  | .event (.assumeReg r al v) t, ρ, m, σ, o =>
    match regGet m σ r al, v.eval ρ with
    | some w, some w' => w = w' ∧ run P δ len t ρ m σ o
    | _, _ => o = .fail
  | .event (.readReg r al v) t, ρ, m, σ, o =>
    match regGet m σ r al, (v.eval ρ).bind (acc al) with
    | some w, some w' => w = w' ∧ run P δ len t ρ m σ o
    | _, _ => o = .fail
  | .event (.writeReg r al v) t, ρ, m, σ, o =>
    match ((v.eval ρ).bind (acc al)).bind (regSet m σ r al) with
    | some (m', σ') => run P δ len t ρ m' σ' o
    | none => o = .fail
  | .event (.readMem d a k) t, ρ, m, σ, o =>
    match d.eval ρ, a.eval ρ with
    | some (.bits w x), some (.bits 64 y) =>
      if w = 8 * k then
        if device P y k then
          x = (δ m.s.reads).toNat ∧ run P δ len t ρ (devRead m (.ofNat y) (δ m.s.reads)) σ o
        else x = bytes m.mem (.ofNat y) k ∧ run P δ len t ρ m σ o
      else o = .fail
    | _, _ => o = .fail
  | .event (.writeMem a d k) t, ρ, m, σ, o =>
    match a.eval ρ, d.eval ρ with
    | some (.bits 64 y), some (.bits w x) =>
      if w = 8 * k then run P δ len t ρ (store P m y x k) σ o else o = .fail
    | _, _ => o = .fail
  | .event (.readGprs v i xs) t, ρ, m, σ, o =>
    match v.eval ρ, i.eval ρ, Base.evalAll ρ xs with
    | some (.bits 64 y), some (.bits _ k), some ws =>
      ws = gprVals m ∧ y = regAt m (k % 32) ∧ run P δ len t ρ m σ o
    | _, _, _ => o = .fail
  | .event (.writeGprs i v xs) t, ρ, m, σ, o =>
    match i.eval ρ, v.eval ρ, Base.evalAll ρ xs with
    | some (.bits _ k), some (.bits 64 y), some ws =>
      ws = gprVals m ∧ run P δ len t ρ (setRegAt m (k % 32) y) σ o
    | _, _, _ => o = .fail
  | .event (.abstractCall _ _ _) _, _, _, _, o => o = .fail
  | .event .skip t, ρ, m, σ, o => run P δ len t ρ m σ o

/-- Some path of some trace of `ts` ends in the outcome `o`. -/
def runSome (P : Platform) (δ : Nat → UInt32) (len : Nat) :
    List Trace → Vars → Mach → Sys → Outcome → Prop
  | [], _, _, _, _ => False
  | t :: ts, ρ, m, σ, o => run P δ len t ρ m σ o ∨ runSome P δ len ts ρ m σ o

end

/-- Some path of the footprint `F` for the fields `f` ends in the outcome `o`: its trace runs with
the header's variables bound, `__BranchTaken` false, and the opcode's length in bytes. -/
def footRun (P : Platform) (δ : Nat → UInt32) (F : Footprint) (f : Fields) (m : Mach)
    (σ : Sys) (o : Outcome) : Prop :=
  run P δ (F.opcode.width / 8) F.trace (F.vars f) m (σ.set "__BranchTaken" (.bool false)) o

/-- The halfwords of the opcode `p` for the fields `f`, the first at the lower address: one for an
opcode of 16 bits, two for one of 32. -/
def halves (p : Opcode) (f : Fields) : List UInt16 :=
  if p.width = 16 then [.ofNat (p.word f)] else [.ofNat (p.word f / 65536), .ofNat (p.word f)]

/-- The registers outside the model that an event reads, with their accessor paths. -/
def eventReads : Event → List (String × List String)
  | .define _ e | .assert e | .assume e => e.regs.filter fun q => (part q.1 q.2).isNone
  | .assumeReg r al _ | .readReg r al _ => if (part r al).isNone then [(r, al)] else []
  | _ => []

mutual

/-- The registers outside the model that a trace reads, with their accessor paths. -/
def reads : Trace → List (String × List String)
  | .done => []
  | .event e t => eventReads e ++ reads t
  | .cases ts => readsAll ts

def readsAll : List Trace → List (String × List String)
  | [] => []
  | t :: ts => reads t ++ readsAll ts

end

end LeanExe.M7.Isla
