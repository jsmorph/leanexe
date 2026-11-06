import TestSupport.Native.Gcd
import TestSupport.Bare.Programs
import LeanExe.Native.Bare
import LeanExe.A64.Gen
import LeanExe.A64.Image

/-!
The bare-metal programs of the AArch64 back end, the counterparts of the programs of
`tests/baremetal/programs.sh` that it covers so far: GCD's loop and GCD's recursion on 1071 and 462,
and CRC-32 of the 9 bytes of `123456789`.
The program's exit word lies at `base`, where `tools/baremetal/link.ld` places the section
`.text.a64`, and `main` and the rest of the instructions follow it.  The area of the module's
store lies at `rwStart`, where the link script places the section `.data.a64`.  For each program
`run` places the bytes of the instructions, `imageBytes`, in a memory from `main` and the bytes of
the area, `areaBytes`, from `rwStart`, runs the model from `main` with the code map `fetchFrom` of
that memory, the stack pointer at `stackTop`, and a return address outside the code, and reports
the UART's bytes, the status in X0, and the number of steps when `main` returns.  `stub` writes
the assembly of the two sections: the exit word as a branch to `lx_exit` for the linker, then
`main`, whose words are the bytes of a file that the assembler includes, and the area, whose
bytes are those of another such file.
-/

namespace TestSupport.A64

open LeanExe.A64

/-- The address of the UART's data register on QEMU's `virt` machine (`tools/baremetal/link.ld`). -/
def uart : UInt64 := 0x09000000

/-- The address of the exit word, the start of RAM's writable part in `tools/baremetal/link.ld`
for a program whose code and read-only data take less than 1 MiB, and the top of `run`'s
stack. -/
def base : UInt64 := 0x40100000
def rwStart : UInt64 := 0x40200000
def stackTop : UInt64 := 0x40800000

/-- The bytes of the stack below `main`'s frame from which `main` sets the stack's limit: half of
the stack of 1 MiB that `tools/baremetal/build.sh` gives a program by default. -/
def room : UInt64 := 0x80000

/-- The cap of every program's memory in pages: the 16 pages that the modules of
`verified_compile` declare. -/
def cap : Nat := 16

/-- A program: its name, its module, its instructions, and the bytes it must write. -/
structure Program where
  name : String
  module : Wasm.Module
  code : Except String (List Instr)
  bytes : List UInt8

def programs : List Program := [
  { name := "gcd"
    module := TestSupport.Native.Gcd.loopCompiled.module
    code := genProgram TestSupport.Native.Gcd.loopCompiled.module 2 [1071, 462] uart base room
      rwStart cap
    bytes := LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) },
  { name := "gcdrec"
    module := TestSupport.Native.Gcd.recCompiled.module
    code := genProgram TestSupport.Native.Gcd.recCompiled.module 3 [1071, 462] uart base room
      rwStart cap
    bytes := LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) },
  { name := "crc32"
    module := TestSupport.Bare.crcCompiled.module
    code := genProgram TestSupport.Bare.crcCompiled.module 5 [0x3837363534333231, 0x39] uart base
      room rwStart cap
    bytes := LeanExe.Native.encodeWord (TestSupport.Bare.crcCheck 0x3837363534333231 0x39) }]

/-- The UART's bytes, X0, and the number of steps when `main` returns to the address below the
code, after at most `fuel` steps from `main` at `base + 4` with the area of module `m` at
`rwStart`; or the reason that it did not. -/
def run (m : Wasm.Module) (code : List Instr) (fuel : Nat) :
    Except String (List UInt8 × UInt64 × Nat) := do
  let bytes := (imageBytes code).toArray
  let area := (areaBytes m cap).toArray
  let mainA := base + 4
  let image (a : UInt64) : UInt8 :=
    if rwStart ≤ a then area.getD (a - rwStart).toNat 0
    else if mainA ≤ a then bytes.getD (a - mainA).toNat 0 else 0
  let P : Platform :=
    { normal := fun a => rwStart ≤ a ∧ a < 0x80000000, uart := uart }
  let ret := base - 8
  let mut s : State :=
    { regs := fun r => if r.val = 30 then ret else 0, sp := stackTop, pc := mainA,
      nFlag := false, zFlag := false, cFlag := false, vFlag := false, mem := image, out := [] }
  let fetch := fetchFrom image mainA code.length
  for k in [0:fuel] do
    if s.pc = ret then return (s.out, s.x 0, k)
    if s.pc = base then throw s!"the exit word with X0 {s.x 0} after {k} steps"
    match step P fetch s with
    | some t => s := t
    | none => throw s!"the model stops at {s.pc} after {k} steps"
  throw s!"no return within {fuel} steps"

/-- The assembly of the section `.text.a64`, the exit word, a branch to `lx_exit`, then `main`,
whose words are the bytes of the file `bin`, and of the section `.data.a64`, the area `lx_area`,
whose bytes are those of the file `area`. -/
def stub (bin area : String) : String :=
  "  .section .text.a64, \"ax\"\n  .balign 4\n  b lx_exit\n  .global main\nmain:\n" ++
    s!"  .incbin \"{bin}\"\n" ++
    "  .section .data.a64, \"aw\"\n  .global lx_area\nlx_area:\n" ++
    s!"  .incbin \"{area}\"\n"

end TestSupport.A64
