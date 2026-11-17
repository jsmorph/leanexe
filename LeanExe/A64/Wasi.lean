import LeanExe.A64.Elf
import LeanExe.Wasi.CallTable
import LeanExe.A64.WasiPreopen
import LeanExe.A64.WasiStrings
import LeanExe.A64.WasiFiles

/-!
A WASI command as a static Linux executable for AArch64: a module of the verified compiler whose
imports are the stream functions of Preview 1, `fd_read`, `fd_write`, and `proc_exit`, in that
order, and then flat calls whose stubs `flatStubs` lists, run from its export `_start`, with each
import implemented by a stub that makes the Linux calls of the shim's specification through the
runtime's routine `SVC #0; RET`.

Talos numbers a module's functions with the imports first, so function `j` of the module at or
above the imports lies at position `j - m.imports.length` of `m.funcs`.  `genWasiProgram` lays out
`main`, the entry's prefix, the three stream stubs, the trap stub, the routine of errnos, the stub
of each flat import in the order of the imports, the startup routine, and every function of the
module, and its table of calls gives the stubs' entries for the imports' indices and the
functions' entries for the others.  The header's entry, `wasiEntry`, is the prefix `ADD X2, SP,
#0; B elfEntry`, which keeps the initial SP that Linux gives the process, the address of `argc`,
in X2 while the runtime sets SP to the stack's top.  `main` saves X30, sets the stack's limit in
X18 `room` bytes below its frame, stores X2 at the start of the shim's scratch, calls the startup
routine and then `_start`, function `k`, which takes and returns nothing, and returns 0.  The
startup routine is the check of descriptor 3 of `LeanExe/A64/WasiPreopen.lean` for a module whose
flat imports read the shim's descriptor state (`needsCheck`), and a return for every other
module.  The flat stubs of `flatStubs` are the string stubs of `LeanExe/A64/WasiStrings.lean`,
those of `args_sizes_get`, `args_get`, `environ_sizes_get`, and `environ_get`, the stubs of
`fd_prestat_get` and `fd_prestat_dir_name` of `LeanExe/A64/WasiPreopen.lean`, and the stubs of
`path_open`, `fd_close`, and `fd_read` and `fd_write` on a handle of `LeanExe/A64/WasiFiles.lean`.
The memory's cap of `cap` pages is the program's, which `areaOk` requires to lie from the
module's minimum below 65,536 pages.

The shim's scratch occupies the `scratchSize` bytes from the area's end, at `X17 + areaSize cap`,
to the stack's limit: `genWasiElf` gives the runtime a stack's room of `room + scratchSize`
bytes, and `main` sets the limit `room` bytes below its frame.  The loader fills the scratch with
zeros.  It holds the initial SP, the flag of the preopened directory, a byte for each descriptor
number below 1,024 that the shim holds, and buffers for the calls of the flat stubs (`Scratch`).
`modulePlatform` is the platform of the data segment without the scratch, on which the module's
code runs, and `wasiPlatform` the platform of the data segment and the initial stack, on which
the process runs.  `InitialStack` states the layout of the arguments and the environment that
Linux places at the initial SP, which the stubs of `stringStubs`, of `LeanExe/A64/WasiStrings.lean`,
read through the scratch's first word.

A stub follows the shim's stream functions of `Verified/Shim/Env.lean`.  The stubs of `fd_read` and
`fd_write` require the arguments that that environment requires: descriptor 0 for a read and 1 or 2
for a write, the iovec at guest address 0, one iovec, and the count at guest address 8.  They load
the iovec's pointer and length from the guest's bytes 0 to 7, require the buffer to lie within the
memory and below `2^32`, and for a read of a nonempty buffer above the guest's scratch of 16 bytes,
and make the call with the buffer's address `X17 + 4096 + pointer`.  A result at most the length is
a count, which the stub stores at guest address 8 with `STRB` before it returns 0.  A result of
`2^64 - x` for `x` from 1 to 4095 is an error, whose errno the routine `errnoRoutine` gives.  Every
other result, and every request that fails a check, branches to the trap stub.  The stub keeps its
return address in X19 across the call, so it needs no stack frame, and `wasiStackNeed` counts no
stack for a stub.  The stub of `proc_exit` moves a status of 126 or more to 1 and branches to the
exit word, whose `exit_group` ends the process.  The trap stub sets X0 to 2, the status of every
trap, and branches to the exit word.
-/

namespace LeanExe.A64

open Wasm

/-! ## The scratch, the platforms, and the initial stack -/

/-- The number of bytes of the shim's scratch. -/
def scratchSize : Nat := 5184

/-- The shim's scratch at `base`: the initial SP at offset 0, the preopen flag at 8, which is 1
while descriptor 3 is the preopened directory, a byte for each descriptor number below 1,024 from
16, 1 while the shim holds the number, the timespec of `clock_gettime` at 1,040, the `open_how`
record of `openat2` at 1,056, and the path buffer of 4,096 bytes at 1,080.  The last 8 bytes keep
the stack's top a multiple of 16. -/
structure Scratch where
  base : UInt64

def Scratch.savedSp (G : Scratch) : UInt64 := G.base
def Scratch.preopen (G : Scratch) : UInt64 := G.base + 8
def Scratch.held (G : Scratch) (d : Nat) : UInt64 := G.base + UInt64.ofNat (16 + d)
def Scratch.timespec (G : Scratch) : UInt64 := G.base + 1040
def Scratch.openHow (G : Scratch) : UInt64 := G.base + 1056
def Scratch.path (G : Scratch) : UInt64 := G.base + 1080

/-- The platform on which the module's code runs: the data segment of the layout `L` without the
scratch `G`. -/
def modulePlatform (L : ElfLayout) (G : Scratch) : Platform :=
  { elfPlatform L with
    normal := fun a => (elfPlatform L).normal a &&
      !decide (G.base ≤ a ∧ a.toNat < G.base.toNat + scratchSize) }

/-- The platform on which the process runs: the data segment of the layout `L` and the bytes from
the initial SP `sp` to `top`, where Linux places the initial stack. -/
def wasiPlatform (L : ElfLayout) (sp top : UInt64) : Platform :=
  { elfPlatform L with
    normal := fun a => (elfPlatform L).normal a || decide (sp ≤ a ∧ a < top) }

/-- The word at `a` points at the bytes `s` and a terminating zero, all from `sp` to `top`, with no
zero in `s`. -/
def StringAt (sp top : UInt64) (mem : UInt64 → UInt8) (a : UInt64) (s : List UInt8) : Prop :=
  sp.toNat ≤ (load64 mem a).toNat ∧ (load64 mem a).toNat + s.length + 1 ≤ top.toNat ∧
    0 ∉ s ∧ readList mem (load64 mem a) (s.length + 1) = s ++ [0]

/-- The initial stack that Linux places at the initial SP `sp` for the arguments `args` and the
environment `environ`, each string without its terminating zero (`fs/binfmt_elf.c` of Linux 7.0,
lines 301 to 358): `argc`, the pointers to the arguments, 0, the pointers to the environment's
strings, and 0, every word and string byte of which lies from `sp` to `top`, with `sp` from `2^32`
up and `top` below `2^63`. -/
structure InitialStack (args environ : List (List UInt8)) (sp top : UInt64)
    (mem : UInt64 → UInt8) : Prop where
  above : 2 ^ 32 ≤ sp.toNat
  below : top.toNat < 2 ^ 63
  words : sp.toNat + 8 * (args.length + environ.length + 3) ≤ top.toNat
  argc : load64 mem sp = UInt64.ofNat args.length
  argv : ∀ i (h : i < args.length), StringAt sp top mem (sp + UInt64.ofNat (8 * (i + 1))) args[i]
  argvEnd : load64 mem (sp + UInt64.ofNat (8 * (args.length + 1))) = 0
  envp : ∀ j (h : j < environ.length),
    StringAt sp top mem (sp + UInt64.ofNat (8 * (args.length + 2 + j))) environ[j]
  envpEnd : load64 mem (sp + UInt64.ofNat (8 * (args.length + 2 + environ.length))) = 0

/-! ## The program -/

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
def wasiMainSize : Nat := 20

/-- The entry routine placed at `a` of a command whose startup routine lies at `startup` and
whose `_start` lies at `entry`, with a memory of `cap` pages: X30 saved in a frame of 16 bytes,
the stack's limit in X18 `room` bytes below the frame, X2, the initial SP, stored at the scratch's
first word, `X17 + areaSize cap`, the calls of the startup routine and of `_start`, and a return
of 0. -/
def wasiMain (a startup entry room : UInt64) (cap : Nat) : GenM (List Instr) := do
  return [.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
    [.subReg 18 18 16] ++ movImm 16 (UInt64.ofNat (areaSize cap)) ++
    [.addReg 16 17 16, .str 2 16 0, .bl (← bField (after a 14) startup),
      .bl (← bField (after a 15) entry), .movz 0 0 0, .ldr 30 31 0, .addImm 31 31 16, .ret 30]

/-- The entry's prefix, placed at `a`: X2 set to SP, the initial SP, and a branch to the
runtime's entry. -/
def wasiPrefix (a : UInt64) : GenM (List Instr) := do
  return [.addImm 2 31 0, .b (← bField (after a 1) elfEntry)]

/-- The stub of a flat call as the generator places it: the call, the import that the stub
implements, its number of instructions, and its generator, which takes the stub's address, the
routine `SVC #0; RET`, the trap stub, the routine of errnos, and the scratch's offset from the
area. -/
structure FlatStub where
  call : LeanExe.Wasi.Call
  decl : ImportDecl
  size : Nat
  gen : UInt64 → UInt64 → UInt64 → UInt64 → Nat → GenM (List Instr)

/-- The import of the flat call `name` of Preview 1 with two pointers as `i32` and an errno. -/
def pointerPairImport (name : String) : ImportDecl :=
  { «module» := "wasi_snapshot_preview1", name, params := [.i32, .i32], results := [.i32] }

/-- The stubs of `args_sizes_get`, `args_get`, `environ_sizes_get`, and `environ_get` of
`LeanExe/A64/WasiStrings.lean`, which read the initial stack through the scratch's first word. -/
def stringStubs : List FlatStub :=
  [{ call := .argsSizesGet, decl := pointerPairImport "args_sizes_get",
      size := sizesStubSize .args, gen := fun a _ tr _ scratch => sizesStub .args a tr scratch },
    { call := .argsGet, decl := pointerPairImport "args_get", size := stringsStubSize .args,
      gen := fun a _ tr _ scratch => stringsStub .args a tr scratch },
    { call := .environSizesGet, decl := pointerPairImport "environ_sizes_get",
      size := sizesStubSize .environ,
      gen := fun a _ tr _ scratch => sizesStub .environ a tr scratch },
    { call := .environGet, decl := pointerPairImport "environ_get",
      size := stringsStubSize .environ,
      gen := fun a _ tr _ scratch => stringsStub .environ a tr scratch }]

/-- The import of the flat call `name` of Preview 1 with a descriptor, a pointer, and a length as
`i32` and an errno. -/
def pointerLengthImport (name : String) : ImportDecl :=
  { «module» := "wasi_snapshot_preview1", name, params := [.i32, .i32, .i32], results := [.i32] }

/-- The stubs of `fd_prestat_get` and `fd_prestat_dir_name` of `LeanExe/A64/WasiPreopen.lean`,
which read the preopen flag and the held bytes of the scratch. -/
def preopenStubs : List FlatStub :=
  [{ call := .fdPrestatGet, decl := pointerPairImport "fd_prestat_get", size := prestatStubSize,
      gen := fun a _ tr _ scratch => prestatStub a tr scratch },
    { call := .fdPrestatDirName, decl := pointerLengthImport "fd_prestat_dir_name",
      size := dirNameStubSize, gen := fun a _ tr _ scratch => dirNameStub a tr scratch }]

/-- The stubs of `path_open`, `fd_close`, and `fd_read` and `fd_write` on a handle of
`LeanExe/A64/WasiFiles.lean`, which follow the shim's descriptors through the scratch's bytes. -/
def fileStubs : List FlatStub :=
  [{ call := .pathOpen,
      decl :=
        { «module» := "wasi_snapshot_preview1", name := "path_open",
          params := [.i32, .i32, .i32, .i32, .i32, .i64, .i64, .i32, .i32], results := [.i32] },
      size := openStubSize, gen := openStub },
    { call := .fdClose,
      decl :=
        { «module» := "wasi_snapshot_preview1", name := "fd_close", params := [.i32],
          results := [.i32] },
      size := closeStubSize, gen := closeStub },
    { call := .fdRead,
      decl :=
        { «module» := "wasi_snapshot_preview1", name := "fd_read",
          params := [.i32, .i32, .i32, .i32], results := [.i32] },
      size := handleStubSize, gen := handleStub 63 },
    { call := .fdWrite,
      decl :=
        { «module» := "wasi_snapshot_preview1", name := "fd_write",
          params := [.i32, .i32, .i32, .i32], results := [.i32] },
      size := handleStubSize, gen := handleStub 64 }]

/-- The flat calls whose stubs the generator implements: those of the arguments and the
environment, those of the preopened directory, and those of the files under it. -/
def flatStubs : List FlatStub := stringStubs ++ preopenStubs ++ fileStubs

/-- The stub of `flatStubs` that implements the import `d`, or an error when it holds none. -/
def flatStubFor (d : ImportDecl) : GenM FlatStub :=
  match flatStubs.find? (·.decl = d) with
  | some s => pure s
  | none => throw s!"an import {d.name} with no stub"

/-- The table's entries of the stubs `stubs`, laid out one after another from `a`, for the imports
from index `j`. -/
def stubEntries :
    UInt64 → Nat → List FlatStub → List (Nat × UInt64 × List ValueType × List ValueType)
  | _, _, [] => []
  | a, j, s :: rest =>
      (j, a, s.decl.params, s.decl.results) :: stubEntries (after a s.size) (j + 1) rest

/-- The address after the stubs `stubs`, laid out one after another from `a`. -/
def stubsEnd : UInt64 → List FlatStub → UInt64
  | a, [] => a
  | a, s :: rest => stubsEnd (after a s.size) rest

/-- The code of the stubs `stubs`, laid out one after another from `a`, with the routine
`SVC #0; RET` at `svc`, the trap stub at `tr`, the routine of errnos at `en`, and the scratch at
`scratch` bytes from the area.  Each stub must have its size. -/
def genStubs (svc tr en : UInt64) (scratch : Nat) : UInt64 → List FlatStub → GenM (List Instr)
  | _, [] => pure []
  | a, s :: rest => do
    let is ← s.gen a svc tr en scratch
    unless is.length = s.size do throw s!"a stub of {s.decl.name} of the wrong length"
    return is ++ (← genStubs svc tr en scratch (after a s.size) rest)

/-- The functions of `m` with their indices in Talos's numbering, which counts the imports
first. -/
def wasiFuncs (m : Module) : List (Nat × Function) :=
  m.funcs.zipIdx.map fun x => (m.imports.length + x.2, x.1)

/-- The numbers of parameters and results of the functions that calls may name: the three stream
imports, the flat imports whose entries `flat` holds, and the functions of `fs`. -/
def wasiSig (flat : List (Nat × UInt64 × List ValueType × List ValueType))
    (fs : List (Nat × Function)) (j : Nat) : Option (Nat × Nat) :=
  match j with
  | 0 | 1 => some (4, 1)
  | 2 => some (1, 0)
  | _ => match flat.find? (·.1 = j) with
    | some e => some (e.2.2.1.length, e.2.2.2.length)
    | none => (fs.find? (·.1 = j)).map fun x => (x.2.params.length, x.2.results.length)

/-- The table of calls: the stubs at `rd`, `wr`, and `ex` for the three stream imports, the
entries `flat` of the flat imports' stubs, and the functions of `fs` laid out one after another
from `first` for the others. -/
def wasiTable (rd wr ex : UInt64) (flat : List (Nat × UInt64 × List ValueType × List ValueType))
    (first : UInt64) (fs : List (Nat × Function)) : Table := fun j =>
  match j with
  | 0 => some (rd, [.i32, .i32, .i32, .i32], [.i32])
  | 1 => some (wr, [.i32, .i32, .i32, .i32], [.i32])
  | 2 => some (ex, [.i32], [])
  | _ => match flat.find? (·.1 = j) with
    | some e => some e.2
    | none => entryIn (wasiSig flat fs) first fs j

/-- Whether an instruction leaves X17 unchanged: no form writes it but those whose destination
register is 17. -/
def Instr.keepsX17 : Instr → Bool
  | .movz d .. | .movk d .. | .addImm d .. | .subImm d .. | .subsImm d .. | .subsReg d ..
  | .csinc d .. | .orrReg d .. | .lsrImm d .. | .ldr d .. | .ldrW d .. | .ldrb d .. | .udiv d ..
  | .msub d .. | .addReg d .. | .subReg d .. | .andReg d .. | .eorReg d .. | .madd d ..
  | .lslv d .. | .lsrv d .. | .orrW d .. | .adr d .. | .adrp d .. | .mrs d .. | .fmovXD d ..
  | .fcvtzu d .. | .fmovWS d .. | .fcvtzuXS d .. | .fcvtzsWS d .. => d.val != 17
  | _ => true

/-- Whether an instruction leaves X18, the stack's limit, unchanged: no form writes it but those
whose destination register is 18. -/
def Instr.keepsX18 : Instr → Bool
  | .movz d .. | .movk d .. | .addImm d .. | .subImm d .. | .subsImm d .. | .subsReg d ..
  | .csinc d .. | .orrReg d .. | .lsrImm d .. | .ldr d .. | .ldrW d .. | .ldrb d .. | .udiv d ..
  | .msub d .. | .addReg d .. | .subReg d .. | .andReg d .. | .eorReg d .. | .madd d ..
  | .lslv d .. | .lsrv d .. | .orrW d .. | .adr d .. | .adrp d .. | .mrs d .. | .fmovXD d ..
  | .fcvtzu d .. | .fmovWS d .. | .fcvtzuXS d .. | .fcvtzsWS d .. => d.val != 18
  | _ => true

/-- The addresses of `genWasiProgram`'s parts, from `main` at `a`: the entry's prefix, the stubs of
`fd_read`, `fd_write`, and `proc_exit`, the trap stub, the routine of errnos, and the first flat
stub. -/
def wasiPrefixAt (a : UInt64) : UInt64 := after a 20
def wasiReadAt (a : UInt64) : UInt64 := after a 22
def wasiWriteAt (a : UInt64) : UInt64 := after a 68
def wasiExitAt (a : UInt64) : UInt64 := after a 112
def wasiTrapAt (a : UInt64) : UInt64 := after a 116
def wasiErrnoAt (a : UInt64) : UInt64 := after a 118
def wasiFlatAt (a : UInt64) : UInt64 := after a 224

/-- The header's entry of an executable of `genWasiElf`: the entry's prefix. -/
def wasiEntry : UInt64 := wasiPrefixAt (after elfExitWord 1)

/-- The program of the WASI command `m` whose `_start` is function `k`, placed after its exit word
at `base`, with the routine `SVC #0; RET` at `svc`, a stack of `room` bytes below `main`'s frame,
and a memory of `cap` pages: `main`, the entry's prefix, the stubs of the three stream imports,
the trap stub, the routine of errnos, the stubs of the flat imports, the startup routine, and the
functions of `m`.  The module's imports must be `streamImports` followed by imports whose stubs
`flatStubs` holds, the room must lie below `2^32`, function `k` must take and return nothing, no
instruction may write X17, and no instruction after `main` may write X18. -/
def genWasiProgram (m : Module) (k : Nat) (svc base room : UInt64) (cap : Nat) :
    GenM (List Instr) := do
  unless m.imports.take 3 = streamImports do
    throw "imports that do not begin with fd_read, fd_write, and proc_exit"
  let stubs ← (m.imports.drop 3).mapM flatStubFor
  if 2 ^ 32 ≤ room.toNat then throw "a stack's room of 2^32 bytes or more"
  if !areaOk m cap then throw s!"a memory that an area of {cap} pages does not hold"
  let gts ← match globalTypesOf m with
    | some gts => if gts.length ≤ 511 then pure gts else throw "more than 511 globals"
    | none => throw "a global that is not a number"
  let a := after base 1
  let fs := wasiFuncs m
  let flat := stubEntries (wasiFlatAt a) 3 stubs
  let startAt := stubsEnd (wasiFlatAt a) stubs
  let startup ← wasiStartupCode (needsCheck (m.imports.drop 3)) startAt svc base (areaSize cap)
  let first := after startAt startup.length
  let callee := wasiTable (wasiReadAt a) (wasiWriteAt a) (wasiExitAt a) flat first fs
  let entry ← match entryIn (wasiSig flat fs) first fs k with
    | some (e, [], []) => pure e
    | _ => throw s!"no function {k} without parameters and results"
  let S : Shared :=
    { trapUnreachable := wasiTrapAt a, trapBounds := wasiTrapAt a, trapDiv := wasiTrapAt a,
      trapStack := wasiTrapAt a, cap, globalTypes := gts, byteStores := true }
  let main ← wasiMain a startAt entry room cap
  let pre ← wasiPrefix (wasiPrefixAt a)
  let rd ← readStub (wasiReadAt a) svc (wasiTrapAt a) (wasiErrnoAt a)
  let wr ← writeStub (wasiWriteAt a) svc (wasiTrapAt a) (wasiErrnoAt a)
  let ex ← exitStub (wasiExitAt a) base
  let tr ← trapStub (wasiTrapAt a) base
  let sts ← genStubs svc (wasiTrapAt a) (wasiErrnoAt a) (areaSize cap) (wasiFlatAt a) stubs
  let fns ← genFunctions callee S first fs
  let body := pre ++ rd ++ wr ++ ex ++ tr ++ errnoRoutine ++ sts ++ startup ++ fns
  unless body.all Instr.keepsX18 do throw "an instruction after main that writes X18"
  let prog := main ++ body
  unless prog.all Instr.keepsX17 do throw "an instruction that writes X17"
  return prog

/-- The executable of the WASI command `m` whose `_start` is function `k`, with a memory of `cap`
pages, a stack of `room` bytes, and the scratch between them, entered at the prefix
`wasiEntry`. -/
def genWasiElf (m : Module) (k : Nat) (room : UInt64) (cap : Nat) :
    GenM (List UInt8 × ElfLayout) :=
  genElfEntry wasiEntry (fun rd _ base => genWasiProgram m k (after rd 1) base room cap) m
    (room + UInt64.ofNat scratchSize) cap

end LeanExe.A64
