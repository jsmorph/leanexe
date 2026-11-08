import TestSupport.M7.SignedLoop

/-!
The kernel's check of the image of the signed step of `sgCmsdkTick` for QEMU's `mps2-an500` that
`m7-windows signed-qemu` writes, and the loop theorem over that file.
`tests/baremetal/m7-qemu.sh signed` elaborates this file in the directory of the image, so that
`file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`bootProgram` on `sgCmsdkTick`'s module and index and the words of the initial state `sgInit`,
with the image's layout, and checks that the file's bytes are those of the vector table and the
instructions.  `sg_qemu` then states the loop theorem for every code map that holds the file's
bytes from address 0, where QEMU loads the image.
-/

namespace TestSupport.M7.SignedQemuFile

open LeanExe.M7 LeanExe.Requests TestSupport.M7.Signed

def sgBytes : Nat := file_nat% "signed-cmsdk-qemu.bin"
def sgSize : Nat := file_size% "signed-cmsdk-qemu.bin"

/-- The file holds the bytes of the signed step's image for QEMU. -/
theorem sg_file : bootFileOk Qemu.boot qemuProgram sgBytes sgSize = true := by
  decide +kernel

/-- The signed step on `mps2-an500` from QEMU's reset, over the image file: for every sequence `σ`
of the values that device reads return, every number `N` of windows, every code map that holds the
file's bytes from address 0, and every state that reset gives from the vector table at 0, the
model reaches the loop's head of `main` with the trace of UART0's initialization followed by the
accesses of the first `N` windows of `sgCmsdkTick` from `sgInit`. -/
theorem sg_qemu (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code sgBytes sgSize 0) (b : State) (hb : Reset code 0 b) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) sgCmsdkTick sgInit σ) N :=
  qemu_loop sg_file hf b hb N

end TestSupport.M7.SignedQemuFile

#print axioms TestSupport.M7.SignedQemuFile.sg_qemu
#print axioms TestSupport.M7.SignedQemuFile.sg_file
#print axioms TestSupport.M7.Signed.qemu_loop
#print axioms TestSupport.M7.Signed.sgCompiled.sgCmsdkTick.implements
