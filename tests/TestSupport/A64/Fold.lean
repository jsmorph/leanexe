import Verified.Examples.Fold
import LeanExe.A64.Proof.Program
import LeanExe.A64.Image
import LeanExe.Native.Bare
import LeanExe.Native.Proof.Main

/-!
The theorem of the bare-metal program for AArch64 of Fold's recursion of depth 1000: `main` calls
entry 13 of `Verified.Examples.Fold.compiled.module`, `recursive`, on 1000.  Under the premises of
the theorems of GCD's programs, the machine writes the eight bytes of `recursive 1000` to the UART
from `main` and returns 0 to the address in X30, or it reaches the exit word at `base` with the
status 1 of `unreachable`, which the guard of the call depth reaches, or the status 4 of an
overflow of the stack, and the UART's output as it was.
-/

namespace TestSupport.A64.Fold

open LeanExe.A64 Verified.Examples.Fold Wasm

theorem program (P : Platform) (base room area : UInt64) (cap : Nat) {is : List Instr}
    (hg : genProgram compiled.module 13 [1000] P.uart base room area cap .word = .ok is)
    (ms : State)
    (himage : ∀ j (hj : j < (imageBytes is).length),
      ms.mem (after base 1 + UInt64.ofNat j) = (imageBytes is)[j])
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (harea : ∀ j < areaSize cap,
      ms.mem (area + UInt64.ofNat j) = areaByte compiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    (∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = ms.x 30 ∧
      ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeWord (recursive 1000)) ∨
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = base ∧
      (ms'.x 0 = 1 ∨ ms'.x 0 = 4) ∧ ms'.out = ms.out := by
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, hok, -, -, hfs, -⟩ := gen_program hg
  have hcap := cap_lt_of_areaOk hok
  have hcheck : (match (reachFrom compiled.module 13).mapM (funcOf compiled.module) with
      | .ok fs => decide (4 * (mainSize 1 .word + (fs.map fun x =>
          functionSize (sigIn (callTargets compiled.module 13) fs) x.2).sum + 20) < 2 ^ 64)
      | .error _ => false) = true := by decide +kernel
  rw [hfs] at hcheck
  have hn : 4 * is.length < 2 ^ 64 := by
    rw [genProgram_length hg hfs]
    simpa using hcheck
  have hpar : (compiled.module.funcs[13]?).map (fun f => f.params.length) = some 1 := by
    decide
  cases hk : compiled.module.funcs[13]? with
  | none => rw [hk] at hpar; cases hpar
  | some f =>
      rw [hk] at hpar
      simp only [Option.map_some, Option.some.injEq] at hpar
      obtain ⟨N, hN⟩ := compiled.recursive.implements {} _ _ [.i64 1000] 1000
        (LeanExe.Native.heapAt_nativeStore compiled.initial.1 cap) trivial rfl
        LeanExe.Pipeline.Separate.nil (show cap ≤ 65535 by omega)
      have hc := codeAt_fetchFrom hn himage
      have hsim := program_sim P _ hg hc rfl hk hpar.symm N ms hpc hal hroom htop hstack harea
        hamap habove
      rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, heap', -, hown, -⟩ | ⟨st', hrun⟩
      · have hv : vs.reverse = [.i64 (recursive 1000)] := hown
        rw [List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append] at hv
        subst hv
        rcases ProgramOutcome.success P _ hsim hrun with ⟨-, ms', hr, hp, hx, hout⟩ |
          ⟨w, ms', hw, h⟩
        · exact .inr ⟨ms', hr, hp, .inr hx, hout⟩
        · simp only [ValRel] at hw
          subst hw
          exact .inl ⟨ms', h⟩
      · rcases ProgramOutcome.unreachable P _ hsim hrun with ⟨-, ms', hr, hp, hx, hout⟩ |
          ⟨ms', hr, hp, hx, hout⟩
        · exact .inr ⟨ms', hr, hp, .inr hx, hout⟩
        · exact .inr ⟨ms', hr, hp, .inl hx, hout⟩

end TestSupport.A64.Fold
