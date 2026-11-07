import LeanExe.M7.Encode

/-!
A board's initialization as a list of device accesses, the code that performs them, and the trace
that they give.  An `InitOp` is a read-modify-write of a device register, a read whose value is
discarded, a write of a constant, or `DSB SY`.  A read-modify-write reads the register and writes
the value read with the bits of a mask cleared and those of another set, so the value written is
a function of the value read, and the register's reset value enters no statement.

`opCode` places each register's address in r0 with `MOVW` and `MOVT` and accesses it with a word
load or store at offset 0, the value in r1 and the masks in r2.  `initTrace ops σ` is the trace of
the accesses of `ops` when the reads return `σ 0`, `σ 1`, and so on, in order, and `initReads ops`
is the number of those reads.
-/

namespace LeanExe.M7

/-- A device access of a board's initialization. -/
inductive InitOp where
  /-- A read of the register at `a` and a write of the value read with the bits of `clear`
  cleared and the bits of `set` set. -/
  | rmw (a clear set : UInt32)
  /-- A read of the register at `a` whose value the initialization discards. -/
  | read (a : UInt32)
  /-- A write of `v` to the register at `a`. -/
  | write (a v : UInt32)
  /-- `DSB SY`, which completes the accesses before it and makes no access. -/
  | dsb

/-- `MOVW` and `MOVT` that set register `d` to the word `w`. -/
def movWord (d : Fin 8) (w : UInt32) : List Instr :=
  [.movwOf d (w.toNat % 65536), .movtOf d (w.toNat / 65536)]

/-- The instructions of an access. -/
def opCode : InitOp → List Instr
  | .rmw a c v =>
      movWord 0 a ++ [.ldr 1 0 0] ++ movWord 2 (~~~c) ++ [.andReg 1 1 2] ++ movWord 2 v ++
        [.orrReg 0 1 1 2, .str 1 0 0]
  | .read a => movWord 0 a ++ [.ldr 1 0 0]
  | .write a v => movWord 0 a ++ movWord 1 v ++ [.str 1 0 0]
  | .dsb => [.dsb]

/-- The instructions of an initialization. -/
def initCode (ops : List InitOp) : List Instr := ops.flatMap opCode

/-- The number of device reads of an access. -/
def opReads : InitOp → Nat
  | .rmw .. | .read _ => 1
  | .write .. | .dsb => 0

/-- The device accesses of an access whose read, if it has one, returns `x`. -/
def opTrace : InitOp → UInt32 → List Access
  | .rmw a c v, x => [.read a x, .write a (x &&& ~~~c ||| v)]
  | .read a, x => [.read a x]
  | .write a v, _ => [.write a v]
  | .dsb, _ => []

/-- The device accesses of the initialization `ops` when its reads return `σ 0`, `σ 1`, and so
on. -/
def initTrace : List InitOp → (Nat → UInt32) → List Access
  | [], _ => []
  | op :: ops, σ => opTrace op (σ 0) ++ initTrace ops (fun j => σ (j + opReads op))

/-- The number of device reads of the initialization `ops`. -/
def initReads (ops : List InitOp) : Nat := (ops.map opReads).sum

end LeanExe.M7
