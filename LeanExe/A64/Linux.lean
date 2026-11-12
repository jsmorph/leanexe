import LeanExe.A64.Boot
import LeanExe.A64.Image

/-!
A model of a Linux process at EL0 that runs the code of the AArch64 back end and makes system
calls with `SVC #0`.  The program's model of `LeanExe/A64/Machine.lean` has no form for `SVC`: its
word, `svcWord`, decodes to nothing, so `step` stops there.  `pstep` takes one step of the process:
at `SVC #0` the call's effect comes from `Kernel.svc`, `MSR FPCR, Xt` sets the process's `fpcr`,
and every other word steps by `exec`, a floating-point form only while `fpcr` holds `fpcrValue`,
the value under which `exec` gives the forms' results, and only when the next program counter
lies below 2^55, since Linux enables address tagging at EL0 and a branch to a larger target
changes the target's top byte.

The arguments of a call lie in X0 to X5 and its number in X8, and the kernel returns the result in
X0 and keeps every other general register, the flags, SP_EL0, the low 128 bits of each SIMD
register, and every byte of memory that the call does not write (Linux 7.0,
`arch/arm64/kernel/syscall.c` lines 54 and 151, `arch/arm64/kernel/entry.S` lines 204 to 218 and
414 to 428, and `Documentation/arch/arm64/sve.rst` line 113).  The record `Kernel` fixes the
kernel's choices, as `Rx` fixes the UART's reads: the bytes of standard input before its end, the
most bytes that each call transfers, and the calls that fail.  Call `k` is the call made when the
process's trace holds `k` events.  `Kernel.svc` covers `read` of descriptor 0 and `write` of
descriptor 1.  A `read` returns at least one byte while input remains and the count asked for is
not 0, and 0 at the input's end, so the bytes that the reads return before the first that returns
0 are `Kernel.input`.  A `write` transfers at least one byte when the count is not 0.  A failed
call returns the negated error number and changes nothing else.  Every other call, `exit_group`
among them, has no rule, and a run that reaches it has ended.  Each call appends an event to the
trace, whose `write` events give the bytes of standard output.
-/

namespace LeanExe.A64

/-- The word of `SVC #0`. -/
def svcWord : UInt32 := 0xD4000001

/-- A word of the process's runtime: an instruction of the model, or `SVC #0`. -/
inductive Op where
  | ins (i : Instr)
  | svc
  deriving DecidableEq

/-- The word of an `Op`. -/
def Op.word : Op → UInt32
  | .ins i => encode i
  | .svc => svcWord

/-- The bytes of the words of `ops`, each word's lowest byte first. -/
def opBytes (ops : List Op) : List UInt8 := ops.flatMap fun o => wordBytes o.word

/-- An event of a process's trace: a `read` that returned `bytes`, a `write` that took `bytes`, or
a call of number `nr` that failed with the error number `errno`. -/
inductive Event where
  | read (bytes : List UInt8)
  | write (bytes : List UInt8)
  | fail (nr : UInt64) (errno : Nat)

/-- The bytes that a `read` event returned. -/
def Event.inBytes : Event → List UInt8
  | .read bs => bs
  | _ => []

/-- The bytes that a `write` event took. -/
def Event.outBytes : Event → List UInt8
  | .write bs => bs
  | _ => []

/-- The bytes that the reads of the trace `tr` returned, in order. -/
def stdinOf (tr : List Event) : List UInt8 := tr.flatMap Event.inBytes

/-- The bytes that the writes of the trace `tr` gave standard output, in order. -/
def stdoutOf (tr : List Event) : List UInt8 := tr.flatMap Event.outBytes

/-- What the kernel does at the calls of a process: `input`, the bytes of standard input before
its end; `size k + 1`, the most bytes that call `k` transfers; and `fail k`, an error that call `k`
returns instead, whose number is `fail k + 1`. -/
structure Kernel where
  input : List UInt8
  size : Nat → Nat
  fail : Nat → Option (Fin 4095)

/-- A process: the program's state, the value of `FPCR`, and the events of its calls. -/
structure Proc where
  core : State
  fpcr : UInt64
  trace : List Event

/-- The memory `m` with the bytes `bs` written from `a`. -/
def writeList (m : UInt64 → UInt8) (a : UInt64) : List UInt8 → UInt64 → UInt8
  | [] => m
  | b :: bs => writeList (store8 m a b) (a + 1) bs

/-- The `n` bytes of the memory `m` from `a`. -/
def readList (m : UInt64 → UInt8) (a : UInt64) : Nat → List UInt8
  | 0 => []
  | n + 1 => m a :: readList m (a + 1) n

/-- The process `p` after a call that returns `v` in X0, leaves the memory `mem`, and appends the
event `e`: the program counter at the next word and every other register as it was. -/
def Proc.ret (p : Proc) (v : UInt64) (mem : UInt64 → UInt8) (e : Event) : Proc :=
  { p with core := { p.core.setX 0 v with mem, pc := p.core.pc + 4 }, trace := p.trace ++ [e] }

/-- The process after the call that `p` makes at `SVC #0`, or `none` where the model has no rule.
Call `k` is the call made after `k` events.  `read` (X8 = 63) of descriptor 0 into the X2 bytes
from X1 returns `r`, the least of `size k + 1`, X2, and the number of bytes of input that earlier
reads did not return, and writes those `r` bytes from X1, which must lie in Normal memory.
`write` (X8 = 64) of descriptor 1 from the X2 bytes from X1 takes the least of `size k + 1` and X2
bytes, which must lie in Normal memory, and returns their number.  When `fail k` holds `e`, either
call returns the negated number `e + 1` and changes nothing else. -/
def Kernel.svc (K : Kernel) (P : Platform) (p : Proc) : Option Proc :=
  let s := p.core
  let k := p.trace.length
  let n := (s.x 2).toNat
  if (s.x 8 = 63 ∧ s.x 0 = 0) ∨ (s.x 8 = 64 ∧ s.x 0 = 1) then
    match K.fail k with
    | some e => some (p.ret (0 - UInt64.ofNat (e.val + 1)) s.mem (.fail (s.x 8) (e.val + 1)))
    | none =>
      if s.x 8 = 63 then
        let rest := K.input.drop (stdinOf p.trace).length
        let r := min (K.size k + 1) (min n rest.length)
        if P.mapped (s.x 1) r then
          some (p.ret (UInt64.ofNat r) (writeList s.mem (s.x 1) (rest.take r))
            (.read (rest.take r)))
        else none
      else
        let r := min (K.size k + 1) n
        if P.mapped (s.x 1) r then
          some (p.ret (UInt64.ofNat r) s.mem (.write (readList s.mem (s.x 1) r)))
        else none
  else none

/-- The source register of `MSR FPCR, Xt`, and `none` for every other instruction. -/
def Instr.fpcrSource : Instr → Option (Fin 32)
  | .msr k t => if k.val = SysReg.fpcr.code then some t else none
  | _ => none

/-- One step of the process `p` with the code `code`, or `none` where the model stops: `SVC #0`
by `Kernel.svc`, `MSR FPCR, Xt` by setting `fpcr`, and every other word by `exec`, a
floating-point form only while `fpcr` holds `fpcrValue`, and only when the next program counter
lies below 2^55. -/
def pstep (K : Kernel) (P : Platform) (code : UInt64 → Option UInt32) (p : Proc) :
    Option Proc :=
  match code p.core.pc with
  | none => none
  | some w =>
    if w = svcWord then K.svc P p
    else match decode w with
      | none => none
      | some i =>
        match i.fpcrSource with
        | some t =>
            some { p with core := { p.core with pc := p.core.pc + 4 }, fpcr := p.core.x t }
        | none =>
          if i.isFP = true ∧ p.fpcr ≠ fpcrValue then none
          else match exec P i p.core with
            | some c => if c.pc.toNat < 2 ^ 55 then some { p with core := c } else none
            | none => none

/-- The processes that zero or more steps reach from a process. -/
inductive ProcReach (K : Kernel) (P : Platform) (code : UInt64 → Option UInt32) :
    Proc → Proc → Prop
  | refl (p : Proc) : ProcReach K P code p p
  | next {p q r : Proc} : pstep K P code p = some q → ProcReach K P code q r →
      ProcReach K P code p r

end LeanExe.A64
