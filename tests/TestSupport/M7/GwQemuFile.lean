import TestSupport.M7.GwLoop
import LeanExe.M7.Proof.Parts

/-!
The kernel's check of the image of the gateway of `gwTick` for QEMU's `mps2-an500` that
`m7-windows gateway-qemu` writes, in parts, and the loop theorem over that file.
`tests/baremetal/m7-qemu.sh gateway` elaborates this file in the directory of the image, so that
`file_nat%` and `file_size%` read it, and no build target includes it.  The check of the whole
image as one declaration does not fit 16 GiB, so each part has a declaration of its own: the
vector table, the self-loop, and UART0's initialization, then `main`, the step `gwTick`,
`gwTickWith`, two groups of the other functions that calls reach from the step, each checking its
entry of `gwSizes`, and the trap stubs with `udivmod64`.  `bootFileOk_parts` joins them into the
check `bootFileOk` that `qemu_loop` takes.  `gw_qemu` then states the loop theorem for every code
map that holds the file's bytes from address 0, where QEMU loads the image.
-/

namespace TestSupport.M7.GwQemuFile

open LeanExe.M7 LeanExe.Requests TestSupport.M7.Qemu TestSupport.M7.Gw Demos.Energy

def gwBytes : Nat := file_nat% "gateway-cmsdk-qemu.bin"
def gwSize : Nat := file_size% "gateway-cmsdk-qemu.bin"

/-- The vector table, the self-loop, and UART0's initialization. -/
theorem gw_head : bootHeadOk boot gwBytes = true := by
  decide +kernel

theorem gw_main :
    mainPartOk gwCompiled.module 33 gwState boot.base devBase gwBytes (bootHead boot).length =
      true := by
  decide +kernel

/-- `gwTick`. -/
theorem gw_fns0 : functionsPartOk gwCompiled.module 33 gwState boot.base stackLimit gwSizes gwBytes
    (bootHead boot).length 0 1 = true := by
  decide +kernel

/-- `gwTickWith`, the largest function. -/
theorem gw_fns1 : functionsPartOk gwCompiled.module 33 gwState boot.base stackLimit gwSizes gwBytes
    (bootHead boot).length 1 2 = true := by
  decide +kernel

/-- `readReq`, `writeReq`, `shiftIn`, `gateway`, `siteProf`, and `gatewayWith`. -/
theorem gw_fns2 : functionsPartOk gwCompiled.module 33 gwState boot.base stackLimit gwSizes gwBytes
    (bootHead boot).length 2 8 = true := by
  decide +kernel

/-- The other functions. -/
theorem gw_fns8 : functionsPartOk gwCompiled.module 33 gwState boot.base stackLimit gwSizes gwBytes
    (bootHead boot).length 8 32 = true := by
  decide +kernel

theorem gw_tail :
    tailPartOk gwState gwSizes udivmod64 gwBytes (bootHead boot).length 242 = true := by
  decide +kernel

theorem gw_size :
    gwSize = (bootHead boot).length + (4 * (mainSize gwState + gwSizes.sum) + 242) ∧
      gwBytes < 256 ^ gwSize := by
  decide +kernel

/-- The file holds the bytes of the gateway's image. -/
theorem gw_file : bootFileOk boot qemuProgram gwBytes gwSize = true :=
  bootFileOk_parts gw_head gw_main gw_count.2
    (functionsPartOk_append
      (functionsPartOk_append (functionsPartOk_append gw_fns0 gw_fns1) gw_fns2) gw_fns8)
    gw_tail gw_size.1 gw_size.2

/-- The gateway on `mps2-an500` from QEMU's reset, over the image file: for every sequence `σ` of
the values that device reads return, every number `N` of windows, every code map that holds the
file's bytes from address 0, and every state that reset gives from the vector table at 0, the
model reaches the loop's head of `main` with the trace of UART0's initialization followed by the
accesses of the first `N` windows of `gwTick` from the state `gwInit`. -/
theorem gw_qemu (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code gwBytes gwSize 0) (b : State) (hb : Reset code 0 b) :
    ∃ s, Reach platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++ windows (reqTrace (devBus devBase) gwTick gwInit σ) N :=
  qemu_loop gw_file hf b hb N

end TestSupport.M7.GwQemuFile

#print axioms TestSupport.M7.GwQemuFile.gw_qemu
#print axioms TestSupport.M7.GwQemuFile.gw_file
#print axioms TestSupport.M7.Gw.qemu_loop
#print axioms TestSupport.M7.Gw.gw_count
#print axioms TestSupport.M7.Qemu.stackOk
