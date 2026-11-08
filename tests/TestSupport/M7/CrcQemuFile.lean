import TestSupport.M7.CrcLoop

/-!
The kernel's check of the image of the CRC-32 step `crcCmsdkTick` for QEMU's `mps2-an500` that
`m7-windows crc-qemu` writes, `crc-cmsdk-qemu.bin`, and the theorems over that file.
`tests/baremetal/m7-qemu.sh crc` elaborates this file in the directory of the image, so that
`file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`bootProgram` on QEMU's layout with the setup of the step's area before UART0's initialization and
on the module, the index 5, and the initial state `crcInit`, and checks that the file's bytes are
those of the vector table and the instructions.  `crc_qemu` states the loop theorem for every code
map that holds the file's bytes from address 0, where QEMU loads the image, and `crc_qemu_prefix`
that the bytes that the run writes to UART0's data register begin the low bytes of the CRC-32 of
the nonempty prefixes of the bytes that it reads from that register.
-/

namespace TestSupport.M7.CrcQemuFile

open LeanExe.M7 LeanExe.Requests TestSupport.M7.Crc TestSupport.M7.CrcImages

def crcBytes : Nat := file_nat% "crc-cmsdk-qemu.bin"
def crcSize : Nat := file_size% "crc-cmsdk-qemu.bin"

/-- The file holds the bytes of the CRC-32 step's image for QEMU. -/
theorem crc_file : bootFileOk qemuBoot qemuProgram crcBytes crcSize = true := by
  decide +kernel

/-- The CRC-32 step on `mps2-an500` from QEMU's reset, over the image file: for every sequence `σ`
of the values that device reads return, every number `N` of windows, every code map that holds
the file's bytes from address 0, and every state that reset gives from the vector table at 0, the
model reaches the loop's head of `main` with the trace of UART0's initialization followed by the
accesses of the first `N` windows of `crcCmsdkTick` from the state `crcInit`. -/
theorem crc_qemu (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code crcBytes crcSize 0) (b : State) (hb : Reset code 0 b) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) crcCmsdkTick crcInit σ) N :=
  crcQemu_loop crc_file hf b hb N

/-- The CRC-32 step's replies on `mps2-an500` from QEMU's reset, over the image file. -/
theorem crc_qemu_prefix (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code crcBytes crcSize 0) (b : State) (hb : Reset code 0 b) :
    let w := windows (reqTrace (devBus Qemu.devBase) crcCmsdkTick crcInit σ) N
    ∃ s, Reach Qemu.platform σ code b s ∧ s.trace = Qemu.initTrace ++ w ∧
      dataOut (devBus Qemu.devBase) crcCmsdk w <+:
        crcReplies (dataIn (devBus Qemu.devBase) crcCmsdk w) ∧
      (dataIn (devBus Qemu.devBase) crcCmsdk w).length ≤
        (dataOut (devBus Qemu.devBase) crcCmsdk w).length + 1 :=
  crcQemu_prefix crc_file hf b hb N

end TestSupport.M7.CrcQemuFile

#print axioms TestSupport.M7.CrcQemuFile.crc_qemu
#print axioms TestSupport.M7.CrcQemuFile.crc_qemu_prefix
#print axioms TestSupport.M7.CrcQemuFile.crc_file
#print axioms TestSupport.M7.Crc.crcQemu_loop
#print axioms TestSupport.M7.Crc.crcQemu_prefix
#print axioms TestSupport.M7.Crc.crcCmsdk_initStore
