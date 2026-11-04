import Verified.Reflect.Command
import TestSupport.Native.Common
import LeanExe.Native.Proof.Ctl
import Verified.Bare
import Verified.Call

/-!
The step function of the controller loop's test (`docs/native-bare-metal.md`): a first-order
low-pass filter whose state moves a quarter of the way toward the input word in each window.  The
step allocates nothing and cannot trap, so the controller's `main` calls it in every window from
the store that the last window left.  The module's memory starts with one page, and the
translation gives `lx_mem` one page, so that the program fits a microcontroller's RAM.
-/

namespace TestSupport.Bare

/-- The new state of the filter from the state `s` and the input `x`. -/
def ctlStep (s x : UInt64) : UInt64 :=
  if s < x then s + (x - s) / 4 else s - (s - x) / 4

verified_compile (pages := 1) (cap := 1) ctlCompiled := [ctlStep]

open Wasm LClight LeanExe.Native in
/-- The controller program around `ctlStep`, from the state 0, runs forever: for every sequence
`σ` of the values that its volatile loads read, window `n` reads the word of `σ (8 n)` to
`σ (8 n + 7)` and stores the eight bytes of the new state. -/
theorem filter_program (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) :
    LoopReacts A X (inProgram pre ctlCompiled.translation (ctlMain 2 0)) E0
      (ctlTrace ctlStep 0 σ) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := ctlCompiled.ctlStep.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := [.i64, .i64]) (rs0 := [.i64])
    (by decide +kernel)
  have hty : type_of_function fd = .Tfunction [tulong, tulong] tulong cc_default := by
    rw [entry_type ctlCompiled.translation_eq hfd hsig]
    rfl
  obtain ⟨hAt0, -, -⟩ : Verified.Ready ctlCompiled.module ctlCompiled.tables
      (Verified.initialHeap ctlCompiled.tables) ctlCompiled.module.initialStore :=
    Verified.Ready.initial rfl ctlCompiled.initial
  exact ctl_program ctlCompiled.translation_eq hpre hfd hty A X (heapAt_nativeStore hAt0 1)
    (ctlRuns_of_nativeA hnat (fun _ _ _ => trivial) (by decide)) 0 σ

end TestSupport.Bare
