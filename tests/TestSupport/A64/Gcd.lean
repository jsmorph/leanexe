import TestSupport.Native.Gcd
import LeanExe.A64.Proof.Program
import LeanExe.A64.Image
import LeanExe.Native.Bare
import LeanExe.Native.Proof.Main

/-!
The theorems of GCD's bare-metal programs for AArch64.  In the first, `main` calls entry 2 of
`loopCompiled.module`, the loop of `gcd`, on 1071 and 462.  When the memory holds the bytes of the
program's instructions from `main`, the machine fetches its instructions from those bytes, the
stack below SP holds `room + 16` bytes of Normal memory above address 4096, for a `room` of at least
4096 bytes, and the area at `area` holds `areaBytes` of the module with `cap` pages in Normal memory
below the stack's limit, the machine writes the eight bytes of `gcd 1071 462` to the UART from
`main` and returns 0 to the address in X30.  In the second, `main` calls entry 3 of
`recCompiled.module`, the recursion of `gcd` with the depth of calls, and the machine writes the
same bytes and returns 0, or it reaches the exit word with the status 1 of the trap of the depth's
guard or the status 4 of an overflow of the stack.
-/

namespace TestSupport.A64.Gcd

open LeanExe.A64 TestSupport.Native.Gcd Wasm

theorem program (P : Platform) (base room area : UInt64) (cap : Nat) {is : List Instr}
    (hg : genProgram loopCompiled.module 2 [1071, 462] P.uart base room area cap .word = .ok is)
    (ms : State)
    (himage : ∀ j (hj : j < (imageBytes is).length),
      ms.mem (after base 1 + UInt64.ofNat j) = (imageBytes is)[j])
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (harea : ∀ j < areaSize cap,
      ms.mem (area + UInt64.ofNat j) = areaByte loopCompiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = ms.x 30 ∧
      ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeWord (gcd 1071 462) := by
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, hok, -, -, hfs, -⟩ := gen_program hg
  have hcap := cap_lt_of_areaOk hok
  have hcheck : (match (reachFrom loopCompiled.module 2).mapM (funcOf loopCompiled.module) with
      | .ok fs => decide (4 * (mainSize 2 .word + (fs.map fun x =>
          functionSize (sigIn (callTargets loopCompiled.module 2) fs) x.2).sum + 20) < 2 ^ 64)
      | .error _ => false) = true := by decide +kernel
  rw [hfs] at hcheck
  have hn : 4 * is.length < 2 ^ 64 := by
    rw [genProgram_length hg hfs]
    simpa using hcheck
  have hct : callTargets loopCompiled.module 2 = [] := by decide +kernel
  have hpar : (loopCompiled.module.funcs[2]?).map (fun f => f.params.length) = some 2 := by
    decide
  cases hk : loopCompiled.module.funcs[2]? with
  | none => rw [hk] at hpar; cases hpar
  | some f =>
      rw [hk] at hpar
      simp only [Option.map_some, Option.some.injEq] at hpar
      obtain ⟨N, hN⟩ := loopCompiled.gcd.implements {} _ _ [.i64 1071, .i64 462] (1071, 462)
        (LeanExe.Native.heapAt_nativeStore loopCompiled.initial.1 cap) trivial rfl
        LeanExe.Pipeline.Separate.nil (show cap ≤ 65535 by omega)
      rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, heap', -, hown, -⟩ | hab
      · have hv : vs.reverse = [.i64 (TestSupport.Native.Gcd.gcd 1071 462)] := hown
        rw [List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append] at hv
        subst hv
        rcases ProgramOutcome.success P _ (program_sim P _ hg (codeAt_fetchFrom hn himage) rfl hk
          hpar.symm N ms hpc hal hroom htop hstack harea hamap habove) hrun with
          ⟨hne, -⟩ | ⟨w, ms', hw, h⟩
        · exact absurd hct hne
        · simp only [ValRel] at hw
          subst hw
          exact ⟨ms', h⟩
      · exact hab.elim

/-- The theorem of GCD's recursion: `main` calls entry 3 of `recCompiled.module`, which calls
the recursion of `gcd` with depth 0, on 1071 and 462.  Under the premises of `program`, the
machine writes the eight bytes of `gcd 1071 462` to the UART from `main` and returns 0 to the
address in X30, or it reaches the exit word at `base` with the status 1 of the trap of the call
depth's guard or the status 4 of an overflow of the stack, and the UART's output as it was. -/
theorem rec_program (P : Platform) (base room area : UInt64) (cap : Nat) {is : List Instr}
    (hg : genProgram recCompiled.module 3 [1071, 462] P.uart base room area cap .word = .ok is)
    (ms : State)
    (himage : ∀ j (hj : j < (imageBytes is).length),
      ms.mem (after base 1 + UInt64.ofNat j) = (imageBytes is)[j])
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (harea : ∀ j < areaSize cap,
      ms.mem (area + UInt64.ofNat j) = areaByte recCompiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    (∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = ms.x 30 ∧
      ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462)) ∨
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = base ∧
      (ms'.x 0 = 1 ∨ ms'.x 0 = 4) ∧ ms'.out = ms.out := by
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, hok, -, -, hfs, -⟩ := gen_program hg
  have hcap := cap_lt_of_areaOk hok
  have hcheck : (match (reachFrom recCompiled.module 3).mapM (funcOf recCompiled.module) with
      | .ok fs => decide (4 * (mainSize 2 .word + (fs.map fun x =>
          functionSize (sigIn (callTargets recCompiled.module 3) fs) x.2).sum + 20) < 2 ^ 64)
      | .error _ => false) = true := by decide +kernel
  rw [hfs] at hcheck
  have hn : 4 * is.length < 2 ^ 64 := by
    rw [genProgram_length hg hfs]
    simpa using hcheck
  have hpar : (recCompiled.module.funcs[3]?).map (fun f => f.params.length) = some 2 := by
    decide
  cases hk : recCompiled.module.funcs[3]? with
  | none => rw [hk] at hpar; cases hpar
  | some f =>
      rw [hk] at hpar
      simp only [Option.map_some, Option.some.injEq] at hpar
      obtain ⟨N, hN⟩ := recCompiled.gcd.implements {} _ _ [.i64 1071, .i64 462] (1071, 462)
        (LeanExe.Native.heapAt_nativeStore recCompiled.initial.1 cap) trivial rfl
        LeanExe.Pipeline.Separate.nil (show cap ≤ 65535 by omega)
      have hc := codeAt_fetchFrom hn himage
      have hsim := program_sim P _ hg hc rfl hk hpar.symm N ms hpc hal hroom htop hstack harea
        hamap habove
      rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, heap', -, hown, -⟩ | ⟨st', hrun⟩
      · have hv : vs.reverse = [.i64 (TestSupport.Native.Gcd.gcd 1071 462)] := hown
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

end TestSupport.A64.Gcd
