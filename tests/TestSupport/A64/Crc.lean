import TestSupport.Bare.Programs
import LeanExe.A64.Proof.Program
import LeanExe.A64.Image
import LeanExe.Native.Bare
import Verified.Bare

/-!
The theorems of CRC-32's bare-metal program for AArch64: `main` calls entry 5 of
`crcCompiled.module`, the wrapper `crcCheck`, on the two words of `123456789`, and the wrapper
calls `crcMsg` with the table of CRC-32.  Under the premises of the theorems of GCD's programs,
the machine writes the eight bytes of `crcCheck 0x3837363534333231 0x39` to the UART from `main`
and returns 0 to the address in X30.  The compiler's theorem without a trap excludes the status 1
of `unreachable`, which the allocator reaches when the memory cannot grow, and `stackBound`
excludes the status 4 of an overflow of the stack.
-/

namespace TestSupport.A64.Crc

open LeanExe.A64 TestSupport.Bare Wasm

/-- The memory of `crcCompiled.module` starts with 16 pages. -/
theorem pages : (crcCompiled.module.memory.map (·.pagesMin.toNat)).getD 0 = 16 := by
  decide +kernel

/-- The heap's `top` at the end of the tables, plus the allocations of
`crcCheck 0x3837363534333231 0x39`, fits 16 pages. -/
theorem heap_room : (Verified.initialHeap crcCompiled.tables).top.toNat +
    crcCompiled.crcCheck.bound (0x3837363534333231, 0x39) ≤ 65536 * 16 := by
  decide +kernel

/-- The bound of the stack that a call of `crcCheck` uses. -/
theorem stack_bound : stackBound crcCompiled.module 5 = 1632 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The theorem of CRC-32's program: under the premises of GCD's `program`, the machine writes the
eight bytes of `crcCheck 0x3837363534333231 0x39` to the UART from `main` and returns 0 to the
address in X30.  `crcCompiled.crcCheck.trapFree` excludes the trap at `unreachable`: the
allocations of 232 bytes from the end of the tables, at byte 6152, fit the memory's first 16
pages.  `stackBound` gives 1632 bytes, which the room of at least 4096 bytes holds, so the stack
does not overflow. -/
theorem program (P : Platform) (base room area : UInt64) (cap : Nat) {is : List Instr}
    (hg : genProgram crcCompiled.module 5 [0x3837363534333231, 0x39] P.uart base room cap
      .word = .ok is)
    (ms : State)
    (himage : ∀ j (hj : j < (imageBytes is).length),
      ms.mem (after base 1 + UInt64.ofNat j) = (imageBytes is)[j])
    (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (h17 : ms.x 17 = area) (harea : ∀ j < areaSize cap,
      ms.mem (area + UInt64.ofNat j) = areaByte crcCompiled.module.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat) :
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = ms.x 30 ∧
      ms'.sp = ms.sp ∧ ms'.x 0 = 0 ∧
      ms'.out = ms.out ++ LeanExe.Native.encodeWord (crcCheck 0x3837363534333231 0x39) := by
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, hok, -, -, hfs, -⟩ := gen_program hg
  have hcap := cap_lt_of_areaOk hok
  have hcheck : (match (reachFrom crcCompiled.module 5).mapM (funcOf crcCompiled.module) with
      | .ok fs => decide (4 * (mainSize 2 .word + (fs.map fun x =>
          functionSize (sigIn (callTargets crcCompiled.module 5) fs) x.2).sum + 20) < 2 ^ 64)
      | .error _ => false) = true := by decide +kernel
  rw [hfs] at hcheck
  have hn : 4 * is.length < 2 ^ 64 := by
    rw [genProgram_length hg hfs]
    simpa using hcheck
  have hpar : (crcCompiled.module.funcs[5]?).map (fun f => f.params.length) = some 2 := by
    decide
  have hpg := pages_le_of_areaOk hok
  rw [pages] at hpg
  have hheap := heap_room
  have hbound := stack_bound
  cases hk : crcCompiled.module.funcs[5]? with
  | none => rw [hk] at hpar; cases hpar
  | some f =>
      rw [hk] at hpar
      simp only [Option.map_some, Option.some.injEq] at hpar
      obtain ⟨N, hN⟩ := crcCompiled.crcCheck.trapFree {} _ _
        [.i64 0x3837363534333231, .i64 0x39] (0x3837363534333231, 0x39)
        (LeanExe.Native.heapAt_nativeStore crcCompiled.initial.1 cap)
        (show _ ≤ 65536 * cap by omega)
        (fun t ht => by
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨Verified.borrowed_nativeStore (crcCompiled.initial.2.2 0 (by decide)) cap,
            LeanExe.Pipeline.Apart.nil⟩)
        rfl LeanExe.Pipeline.Separate.nil (show cap ≤ 65535 by omega)
      have hsim := program_sim_bounded P _ hg (codeAt_fetchFrom hn himage) rfl hk hpar.symm N
        ms hpc hal hroom (by omega) htop hstack h17 harea hamap habove
      rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, heap', -, hown, -⟩ | hab
      · have hv : vs.reverse = [.i64 (crcCheck 0x3837363534333231 0x39)] := hown
        rw [List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append] at hv
        subst hv
        obtain ⟨w, ms', hw, h⟩ := ProgramResult.success P _ hsim hrun
        simp only [ValRel] at hw
        subst hw
        exact ⟨ms', h⟩
      · exact hab.elim

end TestSupport.A64.Crc
