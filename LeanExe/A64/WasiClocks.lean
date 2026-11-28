module

public import LeanExe.A64.Gen
public import LeanExe.Area

@[expose] public section

/-!
The stubs of `clock_time_get` and `random_get`, which follow `clockInvoke` and `randomInvoke` of
`Verified/Shim/Clocks.lean`.  A stub receives its arguments in X0 to X2, keeps its return address
in X19 across its calls, which it makes through the runtime's routine `SVC #0; RET` at `svc`, and
uses no stack.  It writes guest memory only where the specification's function writes, and the
stub of `clock_time_get` also writes the timespec of the shim's scratch, `timespecOffset` bytes
into the scratch, which lies `scratch` bytes above the area at X17.

The stub of `clock_time_get` traps for a clock above 3 or a time's pointer `p` above the
memory's size less 8, which the area's first word holds, and returns errno 8 for clocks 2 and 3.
For clocks 0 and 1 it keeps the scratch's address in X20, clears the timespec with two `STR XZR`,
and calls `clock_gettime(id, timespec)`.  A result of 0 with a nanosecond count above `10^9 − 1`
traps.  Otherwise a second count above `⌊(2^64 − 1 − nsec) / 10^9⌋`, the quotient of `UDIV`,
gives errno 61, and any other gives the time `sec · 10^9 + nsec` at `p` and errno 0.  A negated
error number gives its errno through the routine of errnos at `en`, and any other result traps.

The stub of `random_get` traps for a buffer beyond the memory and returns 0 for a buffer of no
byte.  Otherwise it keeps the address of the bytes that remain in X20 and their count in X21 and
calls `getrandom(X20, X21, 0)`.  A result above the count is a negated error number, whose errno
it returns, or a trap.  A result of 0 traps, and any other advances X20 and lowers X21 by the
result and calls again while bytes remain, so a result equal to the count returns errno 0.
-/

namespace LeanExe.A64

/-- The offset of the timespec of `clock_gettime` in the shim's scratch. -/
def timespecOffset : Nat := 1040

/-- The handling of a nonzero result in X0 that is no count, placed at `a`, with the trap stub
at `tr` and the routine of errnos at `en`: the errno of a negated error number returned to X19,
and a branch to `tr` for any other result. -/
def errorTail (a tr en : UInt64) : GenM (List Instr) := do
  return [.subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 (← cbField (after a 2) tr),
    .orrReg 0 31 12, .bl (← bField (after a 4) en), .ret 19]

/-- The stub of `clock_time_get`, placed at `a`, with the routine `SVC #0; RET` at `svc`, the trap
stub at `tr`, the routine of errnos at `en`, and the shim's scratch `scratch` bytes above the
area. -/
def clockStub (a svc tr en : UInt64) (scratch : Nat) : GenM (List Instr) := do
  let head := [.subsImm 31 0 3, .bcond 8 (← cbField (after a 1) tr), .ldr 9 17 0,
    .subsReg 31 2 9, .bcond 8 (← cbField (after a 4) tr), .subsImm 31 0 1,
    .bcond 8 (← cbField (after a 6) (after a 46)), .orrReg 19 31 30]
  let call := movImm 20 (UInt64.ofNat scratch) ++ [.addReg 20 17 20,
    .str 31 20 ⟨timespecOffset / 8, by decide⟩, .str 31 20 ⟨timespecOffset / 8 + 1, by decide⟩,
    .addImm 1 20 ⟨timespecOffset, by decide⟩, .movz 8 113 0, .bl (← bField (after a 17) svc)]
  let time := [.cbnz 0 (← cbField (after a 18) (after a 40)),
    .ldr 9 20 ⟨timespecOffset / 8, by decide⟩, .ldr 10 20 ⟨timespecOffset / 8 + 1, by decide⟩] ++
    movImm 11 999999999 ++ [.subsReg 31 10 11, .bcond 8 (← cbField (after a 26) tr),
    .addImm 11 11 1, .subReg 12 31 10, .subImm 12 12 1, .udiv 12 12 11, .subsReg 31 9 12,
    .bcond 8 (← cbField (after a 32) (after a 38)), .madd 9 9 11 10, .addReg 13 17 2,
    .str 9 13 512, .movz 0 0 0, .ret 19, .movz 0 61 0, .ret 19]
  let tail ← errorTail (after a 40) tr en
  return head ++ call ++ time ++ tail ++ [.movz 0 8 0, .ret 30]

/-- The stub of `random_get`, placed at `a`, with the routine `SVC #0; RET` at `svc`, the trap stub
at `tr`, and the routine of errnos at `en`. -/
def randomStub (a svc tr en : UInt64) : GenM (List Instr) := do
  let head := [.addReg 9 0 1, .ldr 10 17 0, .addImm 10 10 8, .subsReg 31 9 10,
    .bcond 8 (← cbField (after a 4) tr), .cbz 1 (← cbField (after a 5) (after a 24)),
    .orrReg 19 31 30, .addReg 20 17 0, .addImm 20 20 4095, .addImm 20 20 1, .orrReg 21 31 1]
  let loop := [.orrReg 0 31 20, .orrReg 1 31 21, .movz 2 0 0, .movz 8 278 0,
    .bl (← bField (after a 15) svc), .subsReg 31 0 21,
    .bcond 8 (← cbField (after a 17) (after a 26)), .cbz 0 (← cbField (after a 18) tr),
    .subReg 21 21 0, .addReg 20 20 0, .cbnz 21 (← cbField (after a 21) (after a 11)),
    .movz 0 0 0, .ret 19, .movz 0 0 0, .ret 30]
  let tail ← errorTail (after a 26) tr en
  return head ++ loop ++ tail

/-- The number of instructions of `clockStub`. -/
def clockStubSize : Nat := 48

/-- The number of instructions of `randomStub`. -/
def randomStubSize : Nat := 32

end LeanExe.A64
