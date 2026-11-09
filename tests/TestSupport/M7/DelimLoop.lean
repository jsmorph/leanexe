import TestSupport.M7.DelimImages
import TestSupport.M7.DelimStep
import TestSupport.M7.DelimAbs
import TestSupport.M7.QemuLoop

/-!
The loop theorems of the echo of records of `tests/TestSupport/M7/Delim.lean` through the
Cortex-M7 back end, from reset, for every sequence `σ` of the values that device reads return and
every number `N` of windows.  `qemu_loop` instantiates `boot_run` with QEMU's layout of
`tests/TestSupport/M7/Qemu.lean` and the step `dlCmsdkTick` from the state `dlInit`, with the
compiler's theorem of the step, the kernel's evaluations of `reachCovered` and of the stack bound
of `tests/TestSupport/M7/DelimStep.lean`, and the module's initial store.  It holds for every code
map that holds the bytes of a file whose kernel check `bootFileOk` passes, and every state that
reset gives from the file's vector table.  `qemu_prefix` joins it to `dl_cmsdk_prefix` and
`dl_cmsdk_answered` of `tests/TestSupport/M7/DelimAbs.lean`: the bytes that the windows write to
UART0's data register begin the encoded answers of `echoMach` to the nonempty segments of the
bytes that they read from it, and they are all those answers whenever a window reads a byte.
-/

namespace TestSupport.M7.Delim

open LeanExe.M7 LeanExe.Requests LeanExe.Pipeline TestSupport.M7

/-- The echo of records of `dlCmsdkTick` from `dlInit` on `mps2-an500`, from reset: the model
reaches the loop's head of `main` with UART0's initialization and the accesses of the first `N`
windows in its trace. -/
theorem qemu_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready dlCompiled.module dlCompiled.tables
      (Verified.initialHeap dlCompiled.tables) dlCompiled.module.initialStore :=
    Verified.Ready.initial rfl dlCompiled.initial
  exact boot_run (B := Qemu.boot) (s0 := dlState) (words := dlWords) (fun _ => rfl)
    (fun _ => rfl) dlCompiled.dlCmsdkTick.implements (fun _ _ _ => trivial) rfl dl_covered.2
    dl_noArea.2 Qemu.devWindow hAt0 hcap0 (by decide) (by decide) hk hf (by decide)
    (Qemu.initRuns σ code) (by decide) (by decide)
    (fun s hs => by rw [dl_stack.2]; exact Qemu.stackOk (by decide) s hs) dlInit rfl b hb N

/-- The echo of records on `mps2-an500` from reset: the run reaches UART0's initialization
followed by the accesses `w` of the first `N` windows, the bytes that `w` writes to UART0's data
register begin the encoded answers of `echoMach` to the nonempty segments of the bytes that `w`
reads from it, and they are all those answers when window `N` reads a byte. -/
theorem qemu_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    let w := windows (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ) N
    ∃ s, Reach Qemu.platform σ code b s ∧ s.trace = Qemu.initTrace ++ w ∧
      dataOut (devBus Qemu.devBase) dlCmsdk w <+:
        (delimAnswers echoMach 36 0 ((dataIn (devBus Qemu.devBase) dlCmsdk w).map
          UInt64.toUInt8)).map UInt8.toUInt64 ∧
      (dataIn (devBus Qemu.devBase) dlCmsdk
          (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ N) ≠ [] →
        dataOut (devBus Qemu.devBase) dlCmsdk w =
          (delimAnswers echoMach 36 0 ((dataIn (devBus Qemu.devBase) dlCmsdk w).map
            UInt64.toUInt8)).map UInt8.toUInt64) := by
  intro w
  obtain ⟨s, r, -, tr⟩ := qemu_loop hk hf b hb N
  exact ⟨s, r, tr, dl_cmsdk_prefix _ σ N, dl_cmsdk_answered _ σ N⟩

end TestSupport.M7.Delim
