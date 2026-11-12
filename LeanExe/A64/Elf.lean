import LeanExe.A64.Linux
import LeanExe.A64.Startup

/-!
A program of the AArch64 back end as a static Linux executable: an ELF64 file of type `ET_EXEC`
for `EM_AARCH64`, with no interpreter and no section headers, which the kernel maps at fixed
addresses and enters at its entry with the process's registers at zero (Linux 7.0,
`fs/binfmt_elf.c` lines 861 and 1380, and `arch/arm64/include/asm/processor.h` lines 302 to 342).
Two `PT_LOAD` headers describe it.  The text segment, readable and executable, maps the file from
offset 0 at `elfBase`: the 64-byte ELF header, the two 56-byte program headers, the runtime, the
exit word, and the program of `genProgramWith`.  The data segment, readable and writable, maps from
the next multiple of 64 KiB after the code the area's first `areaPrefix` bytes, and its memory
size covers the rest of the area and the stack, which the kernel fills with zeros (`elf_load`,
lines 411 to 460).  Both segments have an alignment of 64 KiB, which serves kernels with pages of
4, 16, or 64 KiB.

The runtime of `sysRuntime` begins at the entry, `elfEntry`.  It sets X17 to the area and SP to
the stack's top with `ADRP` and `ADD`, writes `FPCR` as `fpcrValue`, and calls `main` with `BL`.
`main` returns to the exit, which calls `exit_group` with the status in X0, and the trap stubs reach
the exit through the exit word.  The routines `sysRead` and `sysWrite` set X8 to the call's number,
issue `SVC #0`, and return, so `main` stays a list of `Instr` and calls them with `BL`.

`genSysMain`, the entry routine of a function over bytes, allocates a block of `inMax + 1` bytes,
reads standard input into it until a read returns 0, and calls the function on a buffer of the
bytes read.  A read that fills the block ends the run with status 64, and a read that returns more
than it asked for, which is how Linux returns an error, with status 65.  It writes the bytes of
the buffer that the function returns to standard output, ending with status 66 when a write
returns 0 or more than it asked for, and returns 0.
-/

namespace LeanExe.A64

open Wasm

/-- The address at which the text segment maps the file's first byte. -/
def elfBase : UInt64 := 0x400000

/-- The entry: the word after the ELF header and the two program headers. -/
def elfEntry : UInt64 := elfBase + 176

/-- The number of words of the runtime, from the entry through the exit word. -/
def runtimeLength : Nat := 18

/-- The exit word, the program's `base`. -/
def elfExitWord : UInt64 := after elfEntry 17

/-- `sysRead`, which issues `read` with the arguments in X0 to X2. -/
def sysReadAddr : UInt64 := after elfEntry 11

/-- `sysWrite`, which issues `write` with the arguments in X0 to X2. -/
def sysWriteAddr : UInt64 := after elfEntry 14

/-- The addresses and sizes of an executable. -/
structure ElfLayout where
  /-- The number of bytes of the text segment: the headers and the code. -/
  codeEnd : Nat
  /-- The file offset of the data segment. -/
  dataOff : Nat
  /-- The area's address, where the data segment begins. -/
  area : UInt64
  /-- The number of bytes of the data segment in the file. -/
  dataFile : Nat
  /-- The number of bytes of the data segment in memory: the area and the stack. -/
  dataMem : Nat
  stackTop : UInt64

/-- The layout of an executable whose program has `n` instructions, for module `m` with an area
of `cap` pages and a stack of `room` bytes below `main`'s frame. -/
def elfLayoutOf (n : Nat) (m : Module) (cap : Nat) (room : UInt64) : ElfLayout :=
  let codeEnd := 176 + 4 * (runtimeLength + n)
  let dataOff := roundUp codeEnd 65536
  let dataMem := areaSize cap + room.toNat + 16
  { codeEnd, dataOff, area := elfBase + UInt64.ofNat dataOff, dataFile := areaPrefix m, dataMem,
    stackTop := elfBase + UInt64.ofNat (dataOff + dataMem) }

/-- The runtime of an executable with layout `L`, from the entry: X17 at the area, SP at the
stack's top, `FPCR` at `fpcrValue`, the call of `main`, the exit, `sysRead`, `sysWrite`, and the
exit word. -/
def sysRuntime (L : ElfLayout) : GenM (List Op) := do
  let ar ← addrOf 17 elfEntry L.area
  let stk ← addrOf 1 (after elfEntry 2) L.stackTop
  let call ← bField (after elfEntry 7) (after elfExitWord 1)
  let back ← bField elfExitWord (after elfEntry 8)
  return (ar ++ stk ++ [.addImm 31 1 0, .movz 1 0x200 1, msrOf .fpcr 1, .bl call,
      .movz 8 94 0]).map .ins ++ [.svc, .ins (.b 0)] ++
    [.ins (.movz 8 63 0), .svc, .ins (.ret 30), .ins (.movz 8 64 0), .svc, .ins (.ret 30),
      .ins (.b back)]

/-- The number of instructions of `genSysMain`. -/
def sysMainSize : Nat := 72

/-- The entry routine placed at `a` of a function over bytes at `entry`, with the module's
allocator at `alloc`, `sysRead` at `rd`, and `sysWrite` at `wr`.  It saves X30 in a frame of 16
bytes, sets the stack's limit in X18 `room` bytes below the frame, allocates `inMax + 1` bytes, and
keeps the block's root in the frame.  It reads standard input into the block from X1 while X2 bytes
of the block remain, until a read returns 0, and calls the function on the root and the number of
bytes read.  It writes the buffer whose root and length the function returns to standard output
and returns 0.  The stubs after the return set X0 to 64, 65, or 66 and branch to the exit word at
`base`. -/
def genSysMain (a entry alloc rd wr inMax room base : UInt64) : GenM (List Instr) := do
  let e64 := after a 57
  let e65 := after a 62
  let e66 := after a 67
  let callA := Instr.bl (← bField (after a 12) alloc)
  let callR := Instr.bl (← bField (after a 22) rd)
  let eof ← cbField (after a 23) (after a 30)
  let rfail ← cbField (after a 25) e65
  let rloop ← cbField (after a 28) (after a 21)
  let over ← bField (after a 29) e64
  let callK := Instr.bl (← bField (after a 36) entry)
  let done ← cbField (after a 41) (after a 50)
  let callW := Instr.bl (← bField (after a 43) wr)
  let wzero ← cbField (after a 44) e66
  let wfail ← cbField (after a 46) e66
  let wloop ← bField (after a 49) (after a 41)
  let x64 ← bField (after e64 4) base
  let x65 ← bField (after e65 4) base
  let x66 ← bField (after e66 4) base
  return [.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
    [.subReg 18 18 16] ++ movImm 0 (inMax + 1) ++ [callA, .str 0 31 1, .addReg 1 17 0,
      .addImm 1 1 2048, .addImm 1 1 2048] ++ movImm 2 (inMax + 1) ++
    [.movz 0 0 0, callR, .cbz 0 eof, .subsReg 31 0 2, .bcond 8 rfail, .addReg 1 1 0,
      .subReg 2 2 0, .cbnz 2 rloop, .b over] ++ movImm 16 (inMax + 1) ++
    [.subReg 1 16 2, .ldr 0 31 1, callK, mov 2 1, .addReg 1 17 0, .addImm 1 1 2048,
      .addImm 1 1 2048, .cbz 2 done, .movz 0 1 0, callW, .cbz 0 wzero, .subsReg 31 0 2,
      .bcond 8 wfail, .addReg 1 1 0, .subReg 2 2 0, .b wloop] ++ movImm 0 0 ++
    [.ldr 30 31 0, .addImm 31 31 16, .ret 30] ++ movImm 0 64 ++ [.b x64] ++ movImm 0 65 ++
    [.b x65] ++ movImm 0 66 ++ [.b x66]

/-- The program that runs function `k` of `m`, a function over bytes, on standard input of at most
`inMax` bytes, placed after its exit word at `base`, with `sysRead` at `rd`, `sysWrite` at `wr`, a
stack of `room` bytes below `main`'s frame, and a memory of `cap` pages.  Function 0 of the
functions that calls reach from function `k` is the allocator, and the functions may store
bytes. -/
def genSysProgram (m : Module) (k : Nat) (inMax rd wr base room : UInt64) (cap : Nat) :
    GenM (List Instr) :=
  genProgramWith sysMainSize (fun e => do
      let fs ← (reachFrom m k).mapM (funcOf m)
      match entryIn (sigIn (callTargets m k) fs) (after (after base 1) sysMainSize) fs 0 with
      | some (a0, _, _) => genSysMain (after base 1) e a0 rd wr inMax room base
      | none => throw "no allocator among the functions that the function calls")
    m k base cap true

/-- The two bytes of `v`, the lowest first. -/
def bytes16 (v : Nat) : List UInt8 := [UInt8.ofNat v, UInt8.ofNat (v / 256)]

/-- The 64-byte ELF header of a little-endian ELF64 executable for AArch64 with the entry
`entry` and two program headers from byte 64, and no section header. -/
def elfHeader (entry : UInt64) : List UInt8 :=
  [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0] ++ bytes64 0 ++ bytes16 2 ++ bytes16 183 ++ wordBytes 1 ++
    bytes64 entry ++ bytes64 64 ++ bytes64 0 ++ wordBytes 0 ++ bytes16 64 ++ bytes16 56 ++
    bytes16 2 ++ bytes16 64 ++ bytes16 0 ++ bytes16 0

/-- A 56-byte program header of type `PT_LOAD` with the flags `flags`, file offset `off`, address
`vaddr`, file size `file`, memory size `mem`, and an alignment of 64 KiB. -/
def loadHeader (flags : UInt32) (off : Nat) (vaddr : UInt64) (file mem : Nat) : List UInt8 :=
  wordBytes 1 ++ wordBytes flags ++ bytes64 (UInt64.ofNat off) ++ bytes64 vaddr ++ bytes64 vaddr ++
    bytes64 (UInt64.ofNat file) ++ bytes64 (UInt64.ofNat mem) ++ bytes64 0x10000

/-- The executable of the program that `gp` gives from `sysRead`, `sysWrite`, and the exit word,
with an area of `cap` pages for the module `m` and a stack of `room` bytes: its bytes and its
layout.  The data segment must end below 2^32, and the area's prefix must fit in the area. -/
def genElfWith (gp : UInt64 → UInt64 → UInt64 → GenM (List Instr)) (m : Module)
    (room : UInt64) (cap : Nat) : GenM (List UInt8 × ElfLayout) := do
  let prog ← gp sysReadAddr sysWriteAddr elfExitWord
  let L := elfLayoutOf prog.length m cap room
  unless elfBase.toNat + L.dataOff + L.dataMem < 2 ^ 32 ∧ areaPrefix m ≤ areaSize cap do
    throw s!"an executable whose data segment ends at or above 2^32, or data past its area"
  let rt ← sysRuntime L
  let bytes := elfHeader elfEntry ++ (loadHeader 5 0 elfBase L.codeEnd L.codeEnd ++
    (loadHeader 6 L.dataOff L.area L.dataFile L.dataMem ++ (opBytes rt ++ (imageBytes prog ++
      (List.replicate (L.dataOff - L.codeEnd) 0 ++ areaPrefixBytes m)))))
  return (bytes, L)

/-- The executable that runs function `k` of `m`, a function over bytes, on standard input of at
most `inMax` bytes and writes the bytes of its result to standard output, with an area of `cap`
pages and a stack of `room` bytes. -/
def genSysElf (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat) :
    GenM (List UInt8 × ElfLayout) :=
  genElfWith (fun rd wr base => genSysProgram m k inMax rd wr base room cap) m room cap

/-! ## The loader's premise -/

/-- The number whose `w` bytes from byte `o` of the file `b` are its base-256 digits, the lowest
first. -/
def leNat (b : Nat → UInt8) (o : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => (b o).toNat + 256 * leNat b (o + 1) w

/-- A program header: its type, flags, file offset, address, file size, and memory size. -/
structure ElfSegment where
  type : Nat
  flags : Nat
  offset : Nat
  vaddr : Nat
  filesz : Nat
  memsz : Nat
  deriving DecidableEq, Repr

/-- The program headers of the ELF64 file `b`: `e_phnum` headers of 56 bytes from `e_phoff`. -/
def elfSegments (b : Nat → UInt8) : List ElfSegment :=
  (List.range (leNat b 56 2)).map fun i =>
    let o := leNat b 32 8 + 56 * i
    ⟨leNat b o 4, leNat b (o + 4) 4, leNat b (o + 8) 8, leNat b (o + 16) 8, leNat b (o + 32) 8,
      leNat b (o + 40) 8⟩

/-- The entry `e_entry` of the ELF64 file `b`. -/
def elfEntryOf (b : Nat → UInt8) : Nat := leNat b 24 8

/-- The memory `mem` holds the file `b` as the kernel loads it: for each `PT_LOAD` header, the
segment's file bytes from its address, and zeros from there up to its memory size. -/
def ElfLoaded (b : Nat → UInt8) (mem : UInt64 → UInt8) : Prop :=
  ∀ seg ∈ elfSegments b, seg.type = 1 → ∀ j < seg.memsz,
    mem (UInt64.ofNat (seg.vaddr + j)) = if j < seg.filesz then b (seg.offset + j) else 0

/-- The platform of an executable with layout `L`: Normal memory is the data segment, and the
UART lies at address 0, which Linux never maps. -/
def elfPlatform (L : ElfLayout) : Platform :=
  { normal := fun a => decide (L.area ≤ a ∧ a.toNat < L.area.toNat + L.dataMem), uart := 0,
    rx := ⟨fun _ => 0, fun _ => 0, fun _ _ => 0⟩ }

end LeanExe.A64
