import TestSupport.M7.DelimLoop

/-!
The kernel's check of the image of the echo of records of `dlCmsdkTick` for QEMU's `mps2-an500`
that `m7-windows delim-qemu` writes, `delim-cmsdk-qemu.bin`, and the theorems over that file.
`tests/baremetal/m7-qemu.sh delim` elaborates this file in the directory of the image, so that
`file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`bootProgram` on `dlCmsdkTick`'s module and index and the words of the initial state `dlInit`,
with the image's layout, and checks that the file's bytes are those of the vector table and the
instructions.  `dl_qemu` states the loop theorem for every code map that holds the file's bytes
from address 0, where QEMU loads the image, `dl_qemu_poll` that each window takes at most 151,558
steps and each window that does not decode a segment at most 2,036, and `dl_qemu_prefix` that the
bytes that the run
writes to UART0's data register begin the encoded answers of `echoMach` to the nonempty segments
of the bytes that it reads, all of them whenever a window reads a byte.
-/

namespace TestSupport.M7.DelimQemuFile

open LeanExe.M7 LeanExe.Requests TestSupport.M7.Delim

def dlBytes : Nat := file_nat% "delim-cmsdk-qemu.bin"
def dlSize : Nat := file_size% "delim-cmsdk-qemu.bin"

/-- The file holds the bytes of the echo of records' image for QEMU. -/
theorem dl_file : bootFileOk Qemu.boot qemuProgram dlBytes dlSize = true := by
  decide +kernel

/-- The echo of records on `mps2-an500` from QEMU's reset, over the image file: for every
sequence `σ` of the values that device reads return, every number `N` of windows, every code map
that holds the file's bytes from address 0, and every state that reset gives from the vector
table at 0, the model reaches the loop's head of `main` with the trace of UART0's initialization
followed by the accesses of the first `N` windows of `dlCmsdkTick` from `dlInit`. -/
theorem dl_qemu (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code dlBytes dlSize 0) (b : State) (hb : Reset code 0 b) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ) N :=
  qemu_loop dl_file hf b hb N

/-- The echo of records' windows on `mps2-an500` from QEMU's reset over the image file, counted:
window `i` takes `cs[i]` steps, at most 151,558, and at most 2,036 when its state and the value
that it receives do not satisfy `DlDecodes`. -/
theorem dl_qemu_poll (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code dlBytes dlSize 0) (b : State) (hb : Reset code 0 b) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 151558) ∧
      (∀ i x, cs[i]? = some x →
        ¬ DlDecodes (reqRun dlCmsdkTick dlInit σ i).state (reqRun dlCmsdkTick dlInit σ i).last →
        x ≤ 2036) ∧
      ∀ i ≤ N, ∃ s, run Qemu.platform σ code (c + (cs.take i).sum) b = some s ∧
        s.pc = qemuHead ∧
        s.trace = Qemu.initTrace ++
          windows (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ) i :=
  qemu_loop_poll dl_file hf b hb N

/-- The echo of records' answers on `mps2-an500` from QEMU's reset, over the image file. -/
theorem dl_qemu_prefix (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code dlBytes dlSize 0) (b : State) (hb : Reset code 0 b) :
    let w := windows (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ) N
    ∃ s, Reach Qemu.platform σ code b s ∧ s.trace = Qemu.initTrace ++ w ∧
      dataOut (devBus Qemu.devBase) dlCmsdk w <+:
        (delimAnswers echoMach 36 0 ((dataIn (devBus Qemu.devBase) dlCmsdk w).map
          UInt64.toUInt8)).map UInt8.toUInt64 ∧
      (dataIn (devBus Qemu.devBase) dlCmsdk
          (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ N) ≠ [] →
        dataOut (devBus Qemu.devBase) dlCmsdk w =
          (delimAnswers echoMach 36 0 ((dataIn (devBus Qemu.devBase) dlCmsdk w).map
            UInt64.toUInt8)).map UInt8.toUInt64) :=
  qemu_prefix dl_file hf b hb N

end TestSupport.M7.DelimQemuFile

#print axioms TestSupport.M7.DelimQemuFile.dl_qemu
#print axioms TestSupport.M7.DelimQemuFile.dl_qemu_poll
#print axioms TestSupport.M7.DelimQemuFile.dl_qemu_prefix
#print axioms TestSupport.M7.DelimQemuFile.dl_file
#print axioms TestSupport.M7.Delim.qemu_loop
#print axioms TestSupport.M7.Delim.qemu_loop_poll
#print axioms TestSupport.M7.Delim.dlCompiled.dlCmsdkTick.implements
#print axioms TestSupport.M7.Delim.dl_cmsdk_prefix
#print axioms TestSupport.M7.Delim.dl_cmsdk_answered
#print axioms LeanExe.Requests.delim_prefix
#print axioms LeanExe.Requests.cobsDecode_eq_some_iff
