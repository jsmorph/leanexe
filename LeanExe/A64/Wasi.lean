import LeanExe.A64.Elf

/-!
A WASI command as a static Linux executable for AArch64: a module of the verified compiler whose
imports are the stream functions of Preview 1, `fd_read`, `fd_write`, and `proc_exit`, in that
order, run from its export `_start`, with each import implemented by a stub that makes the Linux
call of the shim's specification through the runtime's routine `SVC #0; RET`.

Talos numbers a module's functions with the imports first, so function `j` of the module at or
above the three imports lies at position `j - 3` of `m.funcs`.  `genWasiProgram` lays out `main`,
the three stubs, the trap stub, the routine of errnos, and every function of the module, and its
table of calls gives the stubs' entries for the imports' indices and the functions' entries for
the others.  `main` saves X30, sets the stack's limit in X18 `room` bytes below its frame, and
calls `_start`, function `k`, which takes and returns nothing.  Should it return, `main` returns 0.
The memory's cap of `cap` pages is the program's, which `areaOk` requires to lie from the
module's minimum below 65,536 pages.

A stub follows the shim's environment of `Verified/Shim/Env.lean`.  The stubs of `fd_read` and
`fd_write` require the arguments that that environment requires: descriptor 0 for a read and 1 or 2
for a write, the iovec at guest address 0, one iovec, and the count at guest address 8.  They load
the iovec's pointer and length from the guest's bytes 0 to 7, require the buffer to lie within the
memory and below `2^32`, and for a read of a nonempty buffer above the scratch's 16 bytes, and make
the call with the buffer's address `X17 + 4096 + pointer`.  A result at most the length is a count,
which the stub stores at guest address 8 with `STRB` before it returns 0.  A result of `2^64 - x`
for `x` from 1 to 4095 is an error, whose errno the routine `errnoRoutine` gives.  Every other
result, and every request that fails a check, branches to the trap stub.  The stub keeps its
return address in X19 across the call, so it needs no stack frame, and `wasiStackNeed` counts no
stack for a stub.  The stub of `proc_exit`
moves a status of 126 or more to 1 and branches to the exit word, whose `exit_group` ends the
process.  The trap stub sets X0 to 2, the status of every trap, and branches to the exit word.
-/

namespace LeanExe.A64

open Wasm

/-- The imports of a WASI command that `genWasiProgram` accepts: `fd_read`, `fd_write`, and
`proc_exit` of Preview 1, in that order. -/
def streamImports : List ImportDecl :=
  [{ «module» := "wasi_snapshot_preview1", name := "fd_read",
      params := [.i32, .i32, .i32, .i32], results := [.i32] },
   { «module» := "wasi_snapshot_preview1", name := "fd_write",
      params := [.i32, .i32, .i32, .i32], results := [.i32] },
   { «module» := "wasi_snapshot_preview1", name := "proc_exit", params := [.i32], results := [] }]

/-- Linux's error numbers and their WASI errnos, by Wasmtime 44's table with `EXDEV` as `perm`.
Every other number gives `io`, 29. -/
def errnoTable : List (Fin 4096 × Fin 65536) :=
  [(1, 63), (2, 44), (4, 27), (5, 29), (9, 8), (12, 48), (13, 2), (16, 10), (17, 20), (18, 63),
    (20, 54), (21, 31), (22, 28), (27, 22), (28, 51), (29, 70), (31, 34), (32, 64), (36, 37),
    (39, 55), (40, 32), (75, 61), (84, 25), (95, 58), (114, 7), (115, 26)]

/-- The routine that replaces the Linux error number in X0 by its WASI errno and returns to X30:
for each entry of `errnoTable`, a comparison of X0 with the number, a branch past the entry when
they differ, the errno in X0, and the return, and then 29 in X0 and the return. -/
def errnoRoutine : List Instr :=
  errnoTable.flatMap (fun x => [.subsImm 31 0 x.1, .bcond 1 3, .movz 0 x.2 0, .ret 30]) ++
    [.movz 0 29 0, .ret 30]

/-- The checks of the buffer of an iovec at guest address 0, placed at `a`, with the trap stub at
`tr`: the pointer in X10 and the length in X11, from the guest's bytes 0 to 7, and a branch to
`tr` when their sum exceeds the memory's size or `2^32`. -/
def bufferChecks (a tr : UInt64) : GenM (List Instr) := do
  return [.ldr 9 17 512, .orrW 10 31 9, .lsrImm 11 9 32, .addReg 12 10 11, .ldr 13 17 0,
    .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 (← cbField (after a 7) tr), .movz 13 1 2,
    .subsReg 31 12 13, .bcond 8 (← cbField (after a 10) tr)]

/-- The call of the buffer's `read` or `write`, the call `nr`, placed at `a`, with the routine
`SVC #0; RET` at `svc`: the buffer's address `X17 + 4096 + X10` in X1, its length in X2, the
call's number in X8, the return address kept in X19, and `BL` to the routine. -/
def bufferCall (a svc : UInt64) (nr : Fin 65536) : GenM (List Instr) := do
  return [.addReg 1 17 10, .addImm 1 1 4095, .addImm 1 1 1, .orrReg 2 31 11, .movz 8 nr 0,
    .orrReg 19 31 30, .bl (← bField (after a 6) svc)]

/-- The handling of the call's result in X0, placed at `a`, with the length in X11, the trap stub
at `tr`, and the routine of errnos at `en`: a result at most the length stored at guest address 8
as a 32-bit word and errno 0 returned to X19, the errno of a negated error number returned, and a
branch to `tr` for every other result. -/
def resultTail (a tr en : UInt64) : GenM (List Instr) := do
  return [.subsReg 31 0 11, .bcond 8 (← cbField (after a 1) (after a 12)), .addImm 16 17 12,
    .strb 0 16 4092, .lsrImm 12 0 8, .strb 12 16 4093, .lsrImm 12 0 16, .strb 12 16 4094,
    .lsrImm 12 0 24, .strb 12 16 4095, .movz 0 0 0, .ret 19, .subReg 12 31 0,
    .subsImm 31 12 4095, .bcond 8 (← cbField (after a 14) tr), .orrReg 0 31 12,
    .bl (← bField (after a 16) en), .ret 19]

/-- The stub of `fd_read`, placed at `a`: descriptor 0, the iovec at 0, one iovec, and the count
at 8, the buffer's checks, a pointer of at least 16 for a nonempty buffer, `read` (63), and the
result. -/
def readStub (a svc tr en : UInt64) : GenM (List Instr) := do
  let head := [.cbnz 0 (← cbField a tr), .cbnz 1 (← cbField (after a 1) tr), .subsImm 31 2 1,
    .bcond 1 (← cbField (after a 3) tr), .subsImm 31 3 8, .bcond 1 (← cbField (after a 5) tr)]
  let checks ← bufferChecks (after a 6) tr
  let low := [.cbz 11 (← cbField (after a 17) (after a 20)), .subsImm 31 10 16,
    .bcond 3 (← cbField (after a 19) tr), .movz 0 0 0]
  let call ← bufferCall (after a 21) svc 63
  let tail ← resultTail (after a 28) tr en
  return head ++ checks ++ low ++ call ++ tail

/-- The stub of `fd_write`, placed at `a`: descriptor 1 or 2, the iovec at 0, one iovec, and the
count at 8, the buffer's checks, `write` (64), and the result. -/
def writeStub (a svc tr en : UInt64) : GenM (List Instr) := do
  let head := [.subImm 9 0 1, .subsImm 31 9 1, .bcond 8 (← cbField (after a 2) tr),
    .cbnz 1 (← cbField (after a 3) tr), .subsImm 31 2 1, .bcond 1 (← cbField (after a 5) tr),
    .subsImm 31 3 8, .bcond 1 (← cbField (after a 7) tr)]
  let checks ← bufferChecks (after a 8) tr
  let call ← bufferCall (after a 19) svc 64
  let tail ← resultTail (after a 26) tr en
  return head ++ checks ++ call ++ tail

/-- The stub of `proc_exit`, placed at `a`: a status of 126 or more replaced by 1, and a branch to
the exit word at `base`. -/
def exitStub (a base : UInt64) : GenM (List Instr) := do
  return [.subsImm 31 0 126, .bcond 3 (← cbField (after a 1) base), .movz 0 1 0,
    .b (← bField (after a 3) base)]

/-- The trap stub, placed at `a`: status 2 and a branch to the exit word at `base`. -/
def trapStub (a base : UInt64) : GenM (List Instr) := do
  return [.movz 0 2 0, .b (← bField (after a 1) base)]

/-- The number of instructions of `wasiMain`. -/
def wasiMainSize : Nat := 13

/-- The entry routine placed at `a` of a command whose `_start` lies at `entry`: X30 saved in a
frame of 16 bytes, the stack's limit in X18 `room` bytes below the frame, the call of `_start`,
and a return of 0. -/
def wasiMain (a entry room : UInt64) : GenM (List Instr) := do
  return [.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
    [.subReg 18 18 16, .bl (← bField (after a 8) entry), .movz 0 0 0, .ldr 30 31 0,
      .addImm 31 31 16, .ret 30]

/-- The functions of `m` with their indices in Talos's numbering, which counts the imports
first. -/
def wasiFuncs (m : Module) : List (Nat × Function) :=
  m.funcs.zipIdx.map fun x => (m.imports.length + x.2, x.1)

/-- The numbers of parameters and results of the functions that calls may name: the three stream
imports and the functions of `fs`. -/
def wasiSig (fs : List (Nat × Function)) (j : Nat) : Option (Nat × Nat) :=
  match j with
  | 0 | 1 => some (4, 1)
  | 2 => some (1, 0)
  | _ => (fs.find? (·.1 = j)).map fun x => (x.2.params.length, x.2.results.length)

/-- The table of calls: the stubs at `rd`, `wr`, and `ex` for the three imports, and the functions
of `fs` laid out one after another from `first` for the others. -/
def wasiTable (rd wr ex first : UInt64) (fs : List (Nat × Function)) : Table := fun j =>
  match j with
  | 0 => some (rd, [.i32, .i32, .i32, .i32], [.i32])
  | 1 => some (wr, [.i32, .i32, .i32, .i32], [.i32])
  | 2 => some (ex, [.i32], [])
  | _ => entryIn (wasiSig fs) first fs j

/-- Whether an instruction leaves X17 unchanged: no form writes it but those whose destination
register is 17. -/
def Instr.keepsX17 : Instr → Bool
  | .movz d .. | .movk d .. | .addImm d .. | .subImm d .. | .subsImm d .. | .subsReg d ..
  | .csinc d .. | .orrReg d .. | .lsrImm d .. | .ldr d .. | .ldrW d .. | .ldrb d .. | .udiv d ..
  | .msub d .. | .addReg d .. | .subReg d .. | .andReg d .. | .eorReg d .. | .madd d ..
  | .lslv d .. | .lsrv d .. | .orrW d .. | .adr d .. | .adrp d .. | .mrs d .. | .fmovXD d ..
  | .fcvtzu d .. | .fmovWS d .. | .fcvtzuXS d .. | .fcvtzsWS d .. => d.val != 17
  | _ => true

/-- The addresses of `genWasiProgram`'s parts, from `main` at `a`: the stubs of `fd_read`,
`fd_write`, and `proc_exit`, the trap stub, the routine of errnos, and the first function. -/
def wasiReadAt (a : UInt64) : UInt64 := after a 13
def wasiWriteAt (a : UInt64) : UInt64 := after a 59
def wasiExitAt (a : UInt64) : UInt64 := after a 103
def wasiTrapAt (a : UInt64) : UInt64 := after a 107
def wasiErrnoAt (a : UInt64) : UInt64 := after a 109
def wasiFirstAt (a : UInt64) : UInt64 := after a 215

/-- The program of the WASI command `m` whose `_start` is function `k`, placed after its exit word
at `base`, with the routine `SVC #0; RET` at `svc`, a stack of `room` bytes below `main`'s frame,
and a memory of `cap` pages: `main`, the stubs of the three imports, the trap stub, the routine of
errnos, and the functions of `m`.  The module's imports must be `streamImports`, function `k` must
take and return nothing, and no instruction may write X17. -/
def genWasiProgram (m : Module) (k : Nat) (svc base room : UInt64) (cap : Nat) :
    GenM (List Instr) := do
  unless m.imports = streamImports do throw "imports other than fd_read, fd_write, and proc_exit"
  if !areaOk m cap then throw s!"a memory that an area of {cap} pages does not hold"
  let gts ← match globalTypesOf m with
    | some gts => if gts.length ≤ 511 then pure gts else throw "more than 511 globals"
    | none => throw "a global that is not a number"
  let a := after base 1
  let fs := wasiFuncs m
  let first := wasiFirstAt a
  let callee := wasiTable (wasiReadAt a) (wasiWriteAt a) (wasiExitAt a) first fs
  let entry ← match entryIn (wasiSig fs) first fs k with
    | some (e, [], []) => pure e
    | _ => throw s!"no function {k} without parameters and results"
  let S : Shared :=
    { trapUnreachable := wasiTrapAt a, trapBounds := wasiTrapAt a, trapDiv := wasiTrapAt a,
      trapStack := wasiTrapAt a, cap, globalTypes := gts, byteStores := true }
  let main ← wasiMain a entry room
  let rd ← readStub (wasiReadAt a) svc (wasiTrapAt a) (wasiErrnoAt a)
  let wr ← writeStub (wasiWriteAt a) svc (wasiTrapAt a) (wasiErrnoAt a)
  let ex ← exitStub (wasiExitAt a) base
  let tr ← trapStub (wasiTrapAt a) base
  let fns ← genFunctions callee S first fs
  let prog := main ++ rd ++ wr ++ ex ++ tr ++ errnoRoutine ++ fns
  unless prog.all Instr.keepsX17 do throw "an instruction that writes X17"
  return prog

/-- The executable of the WASI command `m` whose `_start` is function `k`, with a memory of `cap`
pages and a stack of `room` bytes. -/
def genWasiElf (m : Module) (k : Nat) (room : UInt64) (cap : Nat) :
    GenM (List UInt8 × ElfLayout) :=
  genElfWith (fun rd _ base => genWasiProgram m k (after rd 1) base room cap) m room cap

end LeanExe.A64
