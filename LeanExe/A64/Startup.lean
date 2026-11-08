import LeanExe.A64.Gen
import LeanExe.A64.Image
import LeanExe.A64.Boot
import LeanExe.A64.Clear

/-!
The image of a program as an arm64 Linux Image: every byte that the loader places, written by Lean.
At the image's base lie the 64-byte header, whose first two words select SP_EL1 and branch to the
startup, then the startup, the exit, a word that halts, the program's exit word, and the program
that `genProgram` generates.  The vector table follows at the next multiple of 2 KiB, each of its
entries a branch to itself, then the translation table of `tableBytes`, and, at the next multiple of
4 KiB, the area's first `areaPrefix` bytes, which hold its size word, its globals, and every data
segment.  The image's memory continues past the file with the rest of the area, which the startup
clears, and the stack, whose top ends the size that the header gives.

The header's first word selects SP_EL1 and its second branches to the startup, which checks
`CurrentEL`, sets `VBAR_EL1`, writes `SCTLR_EL1` with the MMU off, `CPACR_EL1` as `cpacrValue`,
which enables floating point, `MAIR_EL1`, `TCR_EL1`, `TTBR0_EL1`, and `TCR2_EL1` as 0 when
`ID_AA64MMFR3_EL1.TCRX` is not 0, synchronizes with `ISB`, invalidates the TLBs with
`TLBI VMALLE1` and `DSB ISH`, writes `FPCR` as `fpcrValue`, writes `SCTLR_EL1` with the MMU on,
and synchronizes again.  It then clears the area's tail with `clearLoop`, sets SP to the stack's top
and X17 to the area, and calls `main` with `BL`.  `main` returns to the exit, which the trap stubs
also reach through the exit word: the exit stores the status in X0 as one byte to the UART,
completes the store with `DSB SY`, and calls PSCI `SYSTEM_OFF` with `HVC #0`.  Every address comes
from `ADRP` and `ADD`, so the bytes run at any base whose low 12 bits are those of `base` in the
layout, and the layout fixes the base at which `genProgram` places the program.
-/

namespace LeanExe.A64

open Wasm

/-- The eight bytes of `v`, the lowest first. -/
def bytes64 (v : UInt64) : List UInt8 := (List.range 8).map (byteOf v)


/-- The addresses of an image at `image`. -/
structure Layout where
  image : UInt64
  /-- The exit word, which `genProgram` takes as `base`. -/
  base : UInt64
  vectors : UInt64
  table : UInt64
  area : UInt64
  /-- The first byte of the area that the startup clears. -/
  clear : UInt64
  /-- The end of the area. -/
  areaEnd : UInt64
  stackTop : UInt64
  /-- The number of bytes of the file. -/
  fileSize : Nat
  /-- The number of bytes from `image` that the image uses. -/
  size : Nat

/-- The number of instructions from the startup's first to the exit word. -/
def startupLength : Nat := 70

/-- `ADRP` and `ADD` that set register `d` to `target` from `here`. -/
def addrOf (d : Fin 32) (here target : UInt64) : GenM (List Instr) := do
  let pages := Int.ofNat (target.toNat / 4096) - Int.ofNat (here.toNat / 4096)
  if pages < -(2 ^ 20) ∨ pages ≥ 2 ^ 20 then
    throw s!"an address {target} beyond the reach of ADRP from {here}"
  let f := (pages % (2 ^ 21 : Int)).toNat
  return [.adrp d ⟨f % 4, Nat.mod_lt _ (by decide)⟩ ⟨f / 4 % 524288, Nat.mod_lt _ (by decide)⟩,
    .addImm d d ⟨target.toNat % 4096, Nat.mod_lt _ (by decide)⟩]

/-- `MSR` of `r` from `Xt`. -/
def msrOf (r : SysReg) (t : Fin 32) : Instr := .msr ⟨r.code % 32768, Nat.mod_lt _ (by decide)⟩ t

/-- `MRS Xt` of `r`. -/
def mrsOf (t : Fin 32) (r : SysReg) : Instr := .mrs t ⟨r.code % 32768, Nat.mod_lt _ (by decide)⟩

/-- The startup, the exit, the word that halts, and the exit word, from the startup's first
instruction at `L.image + 64`, with `main` at `L.base + 4`. -/
def startupCode (L : Layout) : GenM (List Instr) := do
  let s := L.image + 64
  let at_ (k : Nat) : UInt64 := after s k
  let halt := at_ 69
  let exit := at_ 58
  let toHalt ← cbField (at_ 3) halt
  let skip ← cbField (at_ 30) (at_ 32)
  let vec ← addrOf 1 (at_ 4) L.vectors
  let tab ← addrOf 1 (at_ 24) L.table
  let clr ← addrOf 0 (at_ 43) L.clear
  let fin ← addrOf 1 (at_ 45) L.areaEnd
  let stk ← addrOf 1 (at_ 52) L.stackTop
  let ar ← addrOf 17 (at_ 55) L.area
  let call ← bField (at_ 57) (after L.base 1)
  let back ← bField L.base exit
  return [mrsOf 1 .currentEL, .lsrImm 1 1 2, .subsImm 31 1 1, .bcond 1 toHalt] ++
    vec ++ [msrOf .vbar 1] ++ movImm 1 (sctlrOn - 1) ++
    [msrOf .sctlr 1, .movz 1 0x30 1, msrOf .cpacr 1] ++
    movImm 1 mairValue ++ [msrOf .mair 1] ++ movImm 1 tcrValue ++ [msrOf .tcr 1] ++
    tab ++ [msrOf .ttbr0 1, mrsOf 1 .mmfr3, .movz 2 15 0, .andReg 1 1 2, .cbz 1 skip,
      msrOf .tcr2 31, .isb, .tlbiVmalle1, .dsbIsh, .movz 1 0x200 1, msrOf .fpcr 1] ++
    movImm 1 sctlrOn ++ [msrOf .sctlr 1, .isb] ++ clr ++ fin ++ clearLoop ++ stk ++
    [.addImm 31 1 0] ++ ar ++ [.bl call] ++
    movImm 1 uartAddr ++ [.strb 0 1 0, .dsbSy] ++ movImm 0 0x84000008 ++ [.hvc0, .b 0, .b back]

/-- The 64-byte header of an arm64 Linux Image of `size` bytes: `MSR SPSel, #1` and a branch to
the startup at byte 64, `text_offset` 0, the size, the flags of a little-endian image with 4 KiB
pages, three reserved zero words, and the magic `ARM\x64`. -/
def imageHeader (size : Nat) : List UInt8 :=
  wordBytes (encode .spsel1) ++ wordBytes (encode (.b 15)) ++ bytes64 0 ++
    bytes64 (UInt64.ofNat size) ++
    bytes64 2 ++ bytes64 0 ++ bytes64 0 ++ bytes64 0 ++ wordBytes 0x644D5241 ++ wordBytes 0

/-- The vector table: 16 entries of 128 bytes, each a branch to itself. -/
def vectorBytes : List UInt8 :=
  (List.range 16).flatMap fun _ => wordBytes (encode (.b 0)) ++ List.replicate 124 0

/-- The layout of an image at `image` whose program has `n` instructions, for module `m` with an
area of `cap` pages and a stack of `room` bytes below `main`'s frame. -/
def layoutOf (image : UInt64) (n : Nat) (m : Module) (cap : Nat) (room : UInt64) : Layout :=
  let progEnd := 64 + 4 * (startupLength + 1) + 4 * n
  let vec := roundUp progEnd 2048
  let tab := vec + 2048
  let ar := roundUp (tab + 32) 4096
  let endA := ar + areaSize cap
  let top := endA + room.toNat + 16
  { image, base := image + UInt64.ofNat (64 + 4 * startupLength)
    vectors := image + UInt64.ofNat vec, table := image + UInt64.ofNat tab
    area := image + UInt64.ofNat ar, clear := image + UInt64.ofNat (ar + areaPrefix m)
    areaEnd := image + UInt64.ofNat endA, stackTop := image + UInt64.ofNat top
    fileSize := ar + areaPrefix m, size := top }

end LeanExe.A64
