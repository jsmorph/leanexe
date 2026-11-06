import TestSupport.Bare.Programs
import LeanExe.A64.Proof.Program
import LeanExe.A64.Image
import LeanExe.Native.Bare
import Verified.Bare

/-!
The theorem of CRC-32's bare-metal program for AArch64: `main` calls entry 5 of
`crcCompiled.module`, the wrapper `crcCheck`, on the two words of `123456789`, and the wrapper
calls `crcMsg` with the table of CRC-32.  Under the premises of the theorems of GCD's programs,
the machine writes the eight bytes of `crcCheck 0x3837363534333231 0x39` to the UART from `main`
and returns 0 to the address in X30, or it reaches the exit word at `base` with the status 1 of
`unreachable`, which the allocator reaches when the memory cannot grow, or the status 4 of an
overflow of the stack, and the UART's output as it was.
-/

namespace TestSupport.A64.Crc

open LeanExe.A64 TestSupport.Bare Wasm

set_option maxRecDepth 100000 in
theorem program (P : Platform) (base room area : UInt64) (cap : Nat) {is : List Instr}
    (hg : genProgram crcCompiled.module 5 [0x3837363534333231, 0x39] P.uart base room area cap =
      .ok is)
    (ms : State)
    (himage : ∀ j (hj : j < (imageBytes is).length),
      ms.mem (after base 1 + UInt64.ofNat j) = (imageBytes is)[j])
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (harea : ∀ j < areaSize cap,
      ms.mem (area + UInt64.ofNat j) = areaByte crcCompiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    (∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = ms.x 30 ∧
      ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeWord (crcCheck 0x3837363534333231 0x39)) ∨
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = base ∧
      (ms'.x 0 = 1 ∨ ms'.x 0 = 4) ∧ ms'.out = ms.out := by
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, hok, -, -, hfs, -⟩ := gen_program hg
  have hcap := cap_lt_of_areaOk hok
  have hcheck : (match (reachFrom crcCompiled.module 5).mapM (funcOf crcCompiled.module) with
      | .ok fs => decide (4 * (mainSize 2 + (fs.map fun x =>
          functionSize (sigIn (callTargets crcCompiled.module 5) fs) x.2).sum + 20) < 2 ^ 64)
      | .error _ => false) = true := by decide +kernel
  rw [hfs] at hcheck
  have hn : 4 * is.length < 2 ^ 64 := by
    rw [genProgram_length hg hfs]
    simpa using hcheck
  have hpar : (crcCompiled.module.funcs[5]?).map (fun f => f.params.length) = some 2 := by
    decide
  cases hk : crcCompiled.module.funcs[5]? with
  | none => rw [hk] at hpar; cases hpar
  | some f =>
      rw [hk] at hpar
      simp only [Option.map_some, Option.some.injEq] at hpar
      obtain ⟨N, hN⟩ := crcCompiled.crcCheck.implements {} _ _
        [.i64 0x3837363534333231, .i64 0x39] (0x3837363534333231, 0x39)
        (LeanExe.Native.heapAt_nativeStore crcCompiled.initial.1 cap) trivial
        (fun t ht => by
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨Verified.borrowed_nativeStore (crcCompiled.initial.2.2 0 (by decide)) cap,
            LeanExe.Pipeline.Apart.nil⟩)
        rfl LeanExe.Pipeline.Separate.nil (show cap ≤ 65535 by omega)
      have hc := codeAt_fetchFrom hn himage
      have hsim := program_sim P _ hg hc rfl hk hpar.symm N ms hpc hal hroom htop hstack harea
        hamap habove
      rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, heap', -, hown, -⟩ | ⟨st', hrun⟩
      · have hv : vs.reverse = [.i64 (crcCheck 0x3837363534333231 0x39)] := hown
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

end TestSupport.A64.Crc
