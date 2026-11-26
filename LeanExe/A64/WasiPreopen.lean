module

public import LeanExe.A64.WasiStrings

@[expose] public section

/-!
The preopened directory of a WASI command as a Linux executable for AArch64: the startup's check
of descriptor 3 and the stubs of `fd_prestat_get` and `fd_prestat_dir_name`.  Each part reaches the
shim's scratch, `scratch` bytes above the area, as `X17 + scratch` in X20 (`scratchAddr` of
`LeanExe/A64/WasiStrings.lean`).  The scratch holds the preopen flag at offset 8, 1 while descriptor 3 is the preopened directory, a byte
at offset `16 + d` for each descriptor number `d` below 1,024, 1 while the shim holds the number,
and the path buffer at offset 1,080.

`preopenCheck`, which `main` calls before `_start`, writes `.` and its terminating zero to the path
buffer and calls `openat(3, path, O_RDONLY | O_DIRECTORY | O_CLOEXEC, 0)` with arm64's flags
`0x84000`.  A result of `-EBADF` or `-ENOTDIR` grants nothing, and the routine returns.  The routine
closes a descriptor from 4 to `2^31 - 1` with `close`, and when `close` returns 0 or a negated error
number, it sets the preopen flag and the byte of descriptor 3 and returns.  Every other result of
either call ends the run with status 67 through the exit word.  The routine keeps its return
address in X19 across the calls.

The stubs make no call and return to X30.  Each first requires its region of guest memory, which
ends at the guest address in X12, to lie within the memory's size, 8 plus the area's first word,
and branches to the trap stub otherwise (`rangeCheck`).  `preopenTest` branches away unless the
descriptor in X0 is 3 and the preopen flag is set, and `heldTest` unless the shim holds the
descriptor in a register.  `prestatStub` stores the record `[0, 0, 0, 0, 1, 0, 0, 0]`, a directory
whose name has one byte, as the word `2^32` for descriptor 3 while the preopen flag is set, and
returns errno 0.  It returns errno 8 (`badf`) for every other descriptor and for descriptor 3
while the flag is clear.  `dirNameStub` stores `.` at the buffer and returns 0 for descriptor 3
while the flag is set and the buffer is nonempty, and returns errno 37 (`nametoolong`) for an empty
buffer.  For every other descriptor, and for descriptor 3 while the flag is clear, it returns errno
54 (`notdir`) for descriptors 0 to 2 and for a number that the shim holds, and errno 8 otherwise.

A module whose flat imports include a function that reads the shim's descriptor state, one of
`preopenNames`, starts with the check (`needsCheck`), and every other module's startup routine is
a return (`wasiStartupCode`).
-/

namespace LeanExe.A64

open Wasm

/-- The check that the guest's bytes below the guest address in X12 lie within the memory, placed
at `a`, with the trap stub at `tr`: the memory's size, 8 plus the area's first word, in X13, and a
branch to `tr` when X12 exceeds it. -/
def rangeCheck (a tr : UInt64) : GenM (List Instr) := do
  return [.ldr 13 17 0, .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 (← cbField (after a 3) tr)]

/-- The test of the preopened directory, placed at `a`, with the scratch's address in X20: a branch
to `out` unless X0 holds 3 and the preopen flag is set. -/
def preopenTest (a out : UInt64) : GenM (List Instr) := do
  return [.subsImm 31 0 3, .bcond 1 (← cbField (after a 1) out), .ldrb 9 20 8,
    .cbz 9 (← cbField (after a 3) out)]

/-- The test whether the shim holds the descriptor in X`r`, placed at `a`, with the scratch's
address in X20: a branch to `out` when the descriptor is 1,024 or more or its byte is 0. -/
def heldTest (a out : UInt64) (r : Fin 32) : GenM (List Instr) := do
  return [.subsImm 31 r 1023, .bcond 8 (← cbField (after a 1) out), .addReg 10 20 r,
    .ldrb 9 10 16, .cbz 9 (← cbField (after a 4) out)]

/-- The number of instructions of `preopenCheck`. -/
def preopenCheckSize : Nat := 39

/-- The check of descriptor 3, placed at `a`, with the routine `SVC #0; RET` at `svc`, the exit
word at `base`, and the scratch `scratch` bytes above the area. -/
def preopenCheck (a svc base : UInt64) (scratch : Nat) : GenM (List Instr) := do
  return [.orrReg 19 31 30] ++ scratchAddr scratch ++
    [.movz 9 46 0, .strb 9 20 1080, .strb 31 20 1081, .movz 0 3 0, .addImm 1 20 1080,
      .movz 2 0x4000 0, .movk 2 8 1, .movz 3 0 0, .movz 8 56 0,
      .bl (← bField (after a 15) svc), .subReg 9 31 0, .subsImm 31 9 9,
      .bcond 1 (← cbField (after a 18) (after a 20)), .ret 19, .subsImm 31 9 20,
      .bcond 1 (← cbField (after a 21) (after a 23)), .ret 19, .subsImm 31 0 4,
      .bcond 3 (← cbField (after a 24) (after a 37)), .lsrImm 9 0 31,
      .cbnz 9 (← cbField (after a 26) (after a 37)), .movz 8 57 0,
      .bl (← bField (after a 28) svc), .subReg 9 31 0,
      .cbz 0 (← cbField (after a 30) (after a 33)), .subsImm 31 9 4095,
      .bcond 8 (← cbField (after a 32) (after a 37)), .movz 9 1 0, .strb 9 20 8, .strb 9 20 19,
      .ret 19, .movz 0 67 0, .b (← bField (after a 38) base)]

/-- The number of instructions of `prestatStub`. -/
def prestatStubSize : Nat := 21

/-- The stub of `fd_prestat_get` of the descriptor in X0 with the record's pointer in X1, placed
at `a`, with the trap stub at `tr` and the scratch `scratch` bytes above the area. -/
def prestatStub (a tr : UInt64) (scratch : Nat) : GenM (List Instr) := do
  let range ← rangeCheck (after a 1) tr
  let preopen ← preopenTest (after a 10) (after a 19)
  return [.addImm 12 1 8] ++ range ++ scratchAddr scratch ++ preopen ++
    [.addReg 10 17 1, .movz 9 1 2, .str 9 10 512, .movz 0 0 0, .ret 30, .movz 0 8 0, .ret 30]

/-- The number of instructions of `dirNameStub`. -/
def dirNameStubSize : Nat := 34

/-- The stub of `fd_prestat_dir_name` of the descriptor in X0 with the buffer's pointer in X1 and
its capacity in X2, placed at `a`, with the trap stub at `tr` and the scratch `scratch` bytes above
the area. -/
def dirNameStub (a tr : UInt64) (scratch : Nat) : GenM (List Instr) := do
  let range ← rangeCheck (after a 1) tr
  let preopen ← preopenTest (after a 10) (after a 23)
  let held ← heldTest (after a 25) (after a 32) 0
  return [.addReg 12 1 2] ++ range ++ scratchAddr scratch ++ preopen ++
    [.cbz 2 (← cbField (after a 14) (after a 21)), .addReg 10 17 1, .addImm 10 10 1,
      .movz 9 46 0, .strb 9 10 4095, .movz 0 0 0, .ret 30, .movz 0 37 0, .ret 30,
      .subsImm 31 0 3, .bcond 3 (← cbField (after a 24) (after a 30))] ++ held ++
    [.movz 0 54 0, .ret 30, .movz 0 8 0, .ret 30]

/-- The names of the flat imports whose stubs read the shim's descriptor state. -/
def preopenNames : List String :=
  ["path_open", "fd_close", "fd_read", "fd_write", "fd_prestat_get", "fd_prestat_dir_name",
    "fd_filestat_get"]

/-- Whether the flat imports `ds` call for the check of descriptor 3. -/
def needsCheck (ds : List ImportDecl) : Bool := ds.any fun d => preopenNames.contains d.name

/-- The startup routine placed at `a`: the check of descriptor 3 when `check` holds, and a
return otherwise. -/
def wasiStartupCode (check : Bool) (a svc base : UInt64) (scratch : Nat) : GenM (List Instr) :=
  if check then preopenCheck a svc base scratch else pure [.ret 30]

end LeanExe.A64
