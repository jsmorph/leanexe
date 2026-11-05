import TestSupport.Native.Gcd
import LeanExe.A64.Proof.Program
import LeanExe.Native.Bare

/-!
The theorem of GCD's bare-metal program for AArch64: `main` calls entry 2 of
`loopCompiled.module`, the loop of `gcd`, on 1071 and 462.  From `main`, the machine writes the
eight bytes of `gcd 1071 462` to the UART and returns 0 to the address in X30.
-/

namespace TestSupport.A64.Gcd

open LeanExe.A64 TestSupport.Native.Gcd Wasm

theorem program (P : Platform) (code : UInt64 → Option UInt32) (base : UInt64)
    {is : List Instr} (hg : genProgram loopCompiled.module 2 [1071, 462] P.uart base = .ok is)
    (hcode : CodeAt code (after base 1) is) (ms : State) (hpc : ms.pc = after base 1)
    (hal : ms.sp % 16 = 0)
    (hstack : ∀ j < 4112, P.normal (ms.sp - 4112 + UInt64.ofNat j) = true) :
    ∃ ms', Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeWord (gcd 1071 462) := by
  obtain ⟨f, -, -, -, hk, -⟩ := gen_program hg
  have hf : (loopCompiled.module.funcs[2]?).map
      (fun f => (f.params.length, f.locals.all numeric)) = some (2, true) := by decide
  rw [hk] at hf
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨N, hN⟩ := loopCompiled.gcd.implements {} _ _ [.i64 1071, .i64 462] (1071, 462)
    loopCompiled.initial.1 trivial rfl LeanExe.Pipeline.Separate.nil loopCompiled.initial.2.1
  rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, heap', -, hown, -⟩ | hab
  · have hv : vs.reverse = [.i64 (gcd 1071 462)] := hown
    rw [List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append] at hv
    subst hv
    exact program_sim P code hg hcode rfl hk
      (fun t ht => ValRel_zero (List.all_eq_true.mp hf.2 t ht)) hf.1.symm hrun ms hpc hal hstack
  · exact hab.elim

end TestSupport.A64.Gcd
