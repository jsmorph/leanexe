import TestSupport.M7.QemuLoop

/-!
The kernel's check of the image of the echo of `cmsdkTick` for QEMU's `mps2-an500` that
`m7-windows qemu` writes, and the loop theorem over that file.  `tests/baremetal/m7-qemu.sh`
elaborates this file in the directory of the image, so that `file_nat%` and `file_size%` read
it, and no build target includes it.  The kernel evaluates `bootProgram` on `cmsdkTick`'s module
and index and the initial state 3, with the image's layout, and checks that the file's bytes are
those of the vector table and the instructions.  `echo_qemu` then states the loop theorem for
every code map that holds the file's bytes from address 0, where QEMU loads the image.
-/

namespace TestSupport.M7.QemuFile

open LeanExe.M7 LeanExe.Requests TestSupport.M7.Qemu TestSupport.Bare

def echoBytes : Nat := file_nat% "echo-cmsdk-qemu.bin"
def echoSize : Nat := file_size% "echo-cmsdk-qemu.bin"

/-- The file holds the bytes of the echo's image. -/
theorem echo_file : bootFileOk boot echoProgram echoBytes echoSize = true := by
  decide +kernel

/-- The echo on `mps2-an500` from QEMU's reset, over the image file: for every sequence `σ` of
the values that device reads return, every number `N` of windows, every code map that holds the
file's bytes from address 0, and every state that reset gives from the vector table at 0, the
model reaches the loop's head of `main` with the trace of UART0's initialization followed by the
accesses of the first `N` windows of `cmsdkTick` from the state 3. -/
theorem echo_qemu (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code echoBytes echoSize 0) (b : State) (hb : Reset code 0 b) :
    ∃ s, Reach platform σ code b s ∧ s.pc = loopHead ∧
      s.trace = Qemu.initTrace ++ windows (reqTrace (devBus devBase) cmsdkTick 3 σ) N :=
  echo_loop echo_file hf b hb N

end TestSupport.M7.QemuFile

#print axioms TestSupport.M7.QemuFile.echo_qemu
#print axioms TestSupport.M7.QemuFile.echo_file
#print axioms TestSupport.M7.Qemu.echo_loop
#print axioms LeanExe.M7.boot_run
#print axioms LeanExe.M7.main_run
#print axioms LeanExe.M7.main_loop
#print axioms LeanExe.M7.main_window
