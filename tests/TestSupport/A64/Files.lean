import TestSupport.A64.Programs
import TestSupport.A64.Gcd
import TestSupport.A64.Crc
import TestSupport.A64.Sha
import TestSupport.A64.Fold
import LeanExe.A64.File

/-!
The theorems of the AArch64 back end's bare-metal programs over the files that
`a64-programs emit` writes.  `tests/baremetal/a64-programs.sh` elaborates this file in the
directory of those files after it emits them, so `file_nat%` and `file_size%` read the bytes of
each program's instructions, NAME.bin, and no build target includes it.  For each program the
kernel evaluates the generator on the program's module, entry, and arguments, with the UART, the
exit word, the stack's room, the area, and the cap of `TestSupport.A64.Programs`, and checks that
the code's bytes are the file's.  The theorem then states, for a memory that holds the file's bytes
from `main`, what the program's theorem states for a memory that holds the code's bytes.  The area
remains a premise about `areaByte` of the module's initial store.
-/

namespace TestSupport.A64.Files

open LeanExe.A64 TestSupport.A64 Wasm

def gcdBytes : Nat := file_nat% "gcd.bin"
def gcdSize : Nat := file_size% "gcd.bin"
def gcdrecBytes : Nat := file_nat% "gcdrec.bin"
def gcdrecSize : Nat := file_size% "gcdrec.bin"
def crcBytes : Nat := file_nat% "crc32.bin"
def crcSize : Nat := file_size% "crc32.bin"
def shaBytes : Nat := file_nat% "sha256.bin"
def shaSize : Nat := file_size% "sha256.bin"
def depthBytes : Nat := file_nat% "depth.bin"
def depthSize : Nat := file_size% "depth.bin"

set_option maxRecDepth 100000

theorem gcd (P : Platform) (hu : P.uart = uart) (ms : State)
    (himage : ∀ j < gcdSize, ms.mem (after base 1 + UInt64.ofNat j) = byteAt gcdBytes j)
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (harea : ∀ j < areaSize cap, ms.mem (rwStart + UInt64.ofNat j) =
      areaByte TestSupport.Native.Gcd.loopCompiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (rwStart + UInt64.ofNat j) = true)
    (habove : rwStart.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) (gcdSize / 4)) ms ms' ∧ ms'.pc = ms.x 30 ∧
      ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) := by
  obtain ⟨is, hl, h⟩ := of_file
    (g := genProgram TestSupport.Native.Gcd.loopCompiled.module 2 [1071, 462] uart base room
      rwStart cap .word) (by decide +kernel) himage fun is hg hi =>
    Gcd.program P base room rwStart cap (by rw [hu]; exact hg) ms hi hpc hal (by decide) htop
      hstack harea hamap habove
  rwa [show gcdSize / 4 = is.length by omega]

theorem gcdrec (P : Platform) (hu : P.uart = uart) (ms : State)
    (himage : ∀ j < gcdrecSize, ms.mem (after base 1 + UInt64.ofNat j) = byteAt gcdrecBytes j)
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (harea : ∀ j < areaSize cap, ms.mem (rwStart + UInt64.ofNat j) =
      areaByte TestSupport.Native.Gcd.recCompiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (rwStart + UInt64.ofNat j) = true)
    (habove : rwStart.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    (∃ ms', Reach P (fetchFrom ms.mem (after base 1) (gcdrecSize / 4)) ms ms' ∧
      ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462)) ∨
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) (gcdrecSize / 4)) ms ms' ∧ ms'.pc = base ∧
      (ms'.x 0 = 1 ∨ ms'.x 0 = 4) ∧ ms'.out = ms.out := by
  obtain ⟨is, hl, h⟩ := of_file
    (g := genProgram TestSupport.Native.Gcd.recCompiled.module 3 [1071, 462] uart base room
      rwStart cap .word) (by decide +kernel) himage fun is hg hi =>
    Gcd.rec_program P base room rwStart cap (by rw [hu]; exact hg) ms hi hpc hal (by decide) htop
      hstack harea hamap habove
  rwa [show gcdrecSize / 4 = is.length by omega]

theorem crc32 (P : Platform) (hu : P.uart = uart) (ms : State)
    (himage : ∀ j < crcSize, ms.mem (after base 1 + UInt64.ofNat j) = byteAt crcBytes j)
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (harea : ∀ j < areaSize cap, ms.mem (rwStart + UInt64.ofNat j) =
      areaByte TestSupport.Bare.crcCompiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (rwStart + UInt64.ofNat j) = true)
    (habove : rwStart.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    (∃ ms', Reach P (fetchFrom ms.mem (after base 1) (crcSize / 4)) ms ms' ∧
      ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧ ms'.out = ms.out ++
        LeanExe.Native.encodeWord (TestSupport.Bare.crcCheck 0x3837363534333231 0x39)) ∨
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) (crcSize / 4)) ms ms' ∧ ms'.pc = base ∧
      (ms'.x 0 = 1 ∨ ms'.x 0 = 4) ∧ ms'.out = ms.out := by
  obtain ⟨is, hl, h⟩ := of_file
    (g := genProgram TestSupport.Bare.crcCompiled.module 5 [0x3837363534333231, 0x39] uart base
      room rwStart cap .word) (by decide +kernel) himage fun is hg hi =>
    Crc.program P base room rwStart cap (by rw [hu]; exact hg) ms hi hpc hal (by decide) htop
      hstack harea hamap habove
  rwa [show crcSize / 4 = is.length by omega]

theorem sha256 (P : Platform) (hu : P.uart = uart) (ms : State)
    (himage : ∀ j < shaSize, ms.mem (after base 1 + UInt64.ofNat j) = byteAt shaBytes j)
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (harea : ∀ j < areaSize cap, ms.mem (rwStart + UInt64.ofNat j) =
      areaByte TestSupport.Bare.shaCompiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (rwStart + UInt64.ofNat j) = true)
    (habove : rwStart.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    (∃ ms', Reach P (fetchFrom ms.mem (after base 1) (shaSize / 4)) ms ms' ∧
      ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeArray (TestSupport.Bare.shaCheck 0x636261)) ∨
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) (shaSize / 4)) ms ms' ∧ ms'.pc = base ∧
      (ms'.x 0 = 1 ∨ ms'.x 0 = 4) ∧ ms'.out = ms.out := by
  obtain ⟨is, hl, h⟩ := of_file
    (g := genProgram TestSupport.Bare.shaCompiled.module 11 [0x636261] uart base room rwStart cap
      .array) (by decide +kernel) himage fun is hg hi =>
    Sha.program P base room rwStart cap (by rw [hu]; exact hg) ms hi hpc hal (by decide) htop
      hstack harea hamap habove
  rwa [show shaSize / 4 = is.length by omega]

theorem depth (P : Platform) (hu : P.uart = uart) (ms : State)
    (himage : ∀ j < depthSize, ms.mem (after base 1 + UInt64.ofNat j) = byteAt depthBytes j)
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (harea : ∀ j < areaSize cap, ms.mem (rwStart + UInt64.ofNat j) =
      areaByte Verified.Examples.Fold.compiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (rwStart + UInt64.ofNat j) = true)
    (habove : rwStart.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    (∃ ms', Reach P (fetchFrom ms.mem (after base 1) (depthSize / 4)) ms ms' ∧
      ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeWord (Verified.Examples.Fold.recursive 1000)) ∨
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) (depthSize / 4)) ms ms' ∧ ms'.pc = base ∧
      (ms'.x 0 = 1 ∨ ms'.x 0 = 4) ∧ ms'.out = ms.out := by
  obtain ⟨is, hl, h⟩ := of_file
    (g := genProgram Verified.Examples.Fold.compiled.module 13 [1000] uart base room rwStart cap
      .word) (by decide +kernel) himage fun is hg hi =>
    Fold.program P base room rwStart cap (by rw [hu]; exact hg) ms hi hpc hal (by decide) htop
      hstack harea hamap habove
  rwa [show depthSize / 4 = is.length by omega]

end TestSupport.A64.Files

#print axioms TestSupport.A64.Files.gcd
#print axioms TestSupport.A64.Files.gcdrec
#print axioms TestSupport.A64.Files.crc32
#print axioms TestSupport.A64.Files.sha256
#print axioms TestSupport.A64.Files.depth
