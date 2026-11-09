import TestSupport.M7.BmsLoop

/-!
The kernel's check of the image of the BMS step `bmsTick` for QEMU's `mps2-an500` that
`m7-windows bms-qemu` writes, `bms-cmsdk-qemu.bin`, and the theorems B4 and B3a of
`Demos/Bms/requirements.md` over that file.  `tests/baremetal/m7-qemu.sh bms` elaborates this file
in the directory of the image, so that `file_nat%` and `file_size%` read it, and no build target
includes it.  The kernel evaluates `bootProgram` on `bmsTick`'s module and index and the words of
the initial state `bmsInit`, with the image's layout, and checks that the file's bytes are those of
the vector table and the instructions.  `bms_qemu` states the loop theorem for every code map that
holds the file's bytes from address 0, where QEMU loads the image, `bms_qemu_poll` that each
window takes at most 202,799 steps and each window other than the window of a delimiter at most
3,301, and `bms_qemu_prefix` that the
bytes that the run writes to UART0's data register begin the encoded answers of the
specification's machine to the non-empty segments of the bytes that it reads, all of them whenever
a window reads a byte.
-/

namespace TestSupport.M7.BmsQemuFile

open LeanExe.M7 LeanExe.Requests TestSupport.M7.Bms Demos.Bms.Program
open Demos.Bms.Spec (machine maxSegment)

def bmsBytes : Nat := file_nat% "bms-cmsdk-qemu.bin"
def bmsSize : Nat := file_size% "bms-cmsdk-qemu.bin"

/-- The file holds the bytes of the BMS step's image for QEMU. -/
theorem bms_qemu_file : bootFileOk Qemu.boot qemuProgram bmsBytes bmsSize = true := by
  decide +kernel

/-- B4: the BMS step on `mps2-an500` from QEMU's reset, over the image file: for every sequence `σ`
of the values that device reads return, every number `N` of windows, every code map that holds the
file's bytes from address 0, and every state that reset gives from the vector table at 0, the
model reaches the loop's head of `main` with the trace of UART0's initialization followed by the
accesses of the first `N` windows of `bmsTick` from `bmsInit`. -/
theorem bms_qemu (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code bmsBytes bmsSize 0) (b : State) (hb : Reset code 0 b) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) bmsTick bmsInit σ) N :=
  qemu_loop bms_qemu_file hf b hb N

/-- B3a on `mps2-an500` from QEMU's reset over the image file, counted: window `i` takes `cs[i]`
steps, at most 202,799, and at most 3,301 when its state and the value that it receives do not
satisfy `BmsDecodes`. -/
theorem bms_qemu_poll (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code bmsBytes bmsSize 0) (b : State) (hb : Reset code 0 b) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 202799) ∧
      (∀ i x, cs[i]? = some x →
        ¬ BmsDecodes (reqRun bmsTick bmsInit σ i).state (reqRun bmsTick bmsInit σ i).last →
        x ≤ 3301) ∧
      ∀ i ≤ N, ∃ s, run Qemu.platform σ code (c + (cs.take i).sum) b = some s ∧
        s.pc = qemuHead ∧
        s.trace = Qemu.initTrace ++
          windows (reqTrace (devBus Qemu.devBase) bmsTick bmsInit σ) i :=
  qemu_loop_poll bms_qemu_file hf b hb N

/-- B4: the answers on `mps2-an500` from QEMU's reset, over the image file. -/
theorem bms_qemu_prefix (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code bmsBytes bmsSize 0) (b : State) (hb : Reset code 0 b) :
    let w := windows (reqTrace (devBus Qemu.devBase) bmsTick bmsInit σ) N
    ∃ s, Reach Qemu.platform σ code b s ∧ s.trace = Qemu.initTrace ++ w ∧
      dataOut (devBus Qemu.devBase) bmsCmsdk w <+:
        (delimAnswers machine maxSegment Demos.Bms.Spec.init
          ((dataIn (devBus Qemu.devBase) bmsCmsdk w).map UInt64.toUInt8)).map UInt8.toUInt64 ∧
      (dataIn (devBus Qemu.devBase) bmsCmsdk
          (reqTrace (devBus Qemu.devBase) bmsTick bmsInit σ N) ≠ [] →
        dataOut (devBus Qemu.devBase) bmsCmsdk w =
          (delimAnswers machine maxSegment Demos.Bms.Spec.init
            ((dataIn (devBus Qemu.devBase) bmsCmsdk w).map UInt64.toUInt8)).map
            UInt8.toUInt64) :=
  qemu_prefix bms_qemu_file hf b hb N

end TestSupport.M7.BmsQemuFile

#print axioms TestSupport.M7.BmsQemuFile.bms_qemu_file
#print axioms TestSupport.M7.BmsQemuFile.bms_qemu
#print axioms TestSupport.M7.BmsQemuFile.bms_qemu_poll
#print axioms TestSupport.M7.BmsQemuFile.bms_qemu_prefix
#print axioms TestSupport.M7.Bms.qemu_loop
#print axioms TestSupport.M7.Bms.qemu_loop_poll
#print axioms Demos.Bms.Program.bmsCompiled.bmsTick.implements
#print axioms Demos.Bms.Program.bms_cmsdk_prefix
#print axioms Demos.Bms.Program.bms_cmsdk_answered
#print axioms LeanExe.Requests.delim_prefix
